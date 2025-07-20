module regression #(// Deep pipelined Gaussian elimination (Q16.16)
	parameter int WIDTH         		= fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT          		= fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC         		= fpga_cfg_pkg::FP_QFRAC,
)(
    input  logic clk,
    input  logic rst_n,

	//from accumulator
    input  logic 					valid_in,
    input  logic signed [WIDTH-1:0] mat_flat [0:11],
    input  logic 					solver_ready,
    output logic 					valid_out,
	output logic 					singular_err,
    output logic signed [WIDTH-1:0] beta [0:2]
);

    logic v0, v1, v2, v3, v4, v5, v6, v6b, v7a, v7b1, v7b, v7c1, v7c;

    // helper function for abs value 
    function automatic logic signed [WIDTH-1:0] abs_val(input logic signed [WIDTH-1:0] x);
      	abs_val = x[WIDTH-1] ? -x : x;
    endfunction

	//-----------------------------------------------------------
	// flag thats high on the first bad pivot, stays high until reset
	//-----------------------------------------------------------
	logic pivot0_is_zero, pivot1_is_zero, pivot2_is_zero;
	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			singular_err <=  '0;
		else if (pivot0_is_zero || pivot1_is_zero || pivot2_is_zero)
			singular_err <=  1;           // sticky until reset
	end
	
    // Skid buffer for input (one-deep to handle stalls)
    logic buf_valid;
    logic signed [WIDTH-1:0] buf_mat_flat [0:11];

    logic accept_to_skid;
    assign accept_to_skid = valid_in && ready_out && !buf_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 1'b0;
        end else if (accept_to_skid) begin
            for (int i = 0; i < 12; i++) buf_mat_flat[i] <= mat_flat[i];
            buf_valid <= 1'b1;
        end else if (ready_in && buf_valid) begin
            buf_valid <= 1'b0;
        end
    end

    // Matrix registers (augmented 3×4) per stage
    logic signed [WIDTH-1:0] mat0[0:2][0:3];
    logic signed [WIDTH-1:0] mat1[0:2][0:3];
    logic signed [WIDTH-1:0] mat2[0:2][0:3];
    logic signed [WIDTH-1:0] mat3[0:2][0:3];
    logic signed [WIDTH-1:0] mat4[0:2][0:3];
    logic signed [WIDTH-1:0] mat5[0:2][0:3];
    logic signed [WIDTH-1:0] mat6[0:2][0:3];
	logic signed [WIDTH-1:0] mat7[0:2][0:3];

    logic stage2_barrier_ready, stage3_barrier_ready, stage5_barrier_ready, stage6b_barrier_ready, stage7_barrier_ready;
    assign ready_out = !buf_valid || (stage2_barrier_ready && stage3_barrier_ready && stage5_barrier_ready && stage6b_barrier_ready && stage7_barrier_ready && ready_in);

  	//-------------------------------------------------------------------
    // Stage 0 : get inputs
    //-------------------------------------------------------------------
	logic signed [WIDTH-1:0] sum1_latched; 
	logic signed [WIDTH-1:0] sumy_latched; 
    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) 
			v0 <= '0;
		else begin
			v0 <= (buf_valid || valid_in) && ready_out;
			for (int i = 0; i < 3; i++) begin
                mat0[i][0] <= buf_valid ? buf_mat_flat[i*4+0] : mat_flat[i*4+0];
                mat0[i][1] <= buf_valid ? buf_mat_flat[i*4+1] : mat_flat[i*4+1];
                mat0[i][2] <= buf_valid ? buf_mat_flat[i*4+2] : mat_flat[i*4+2];
                mat0[i][3] <= buf_valid ? buf_mat_flat[i*4+3] : mat_flat[i*4+3];
            end
			sum1_latched <= mat0[0][0];
            sumy_latched <= mat0[0][3];
		end
    end

  	//-------------------------------------------------------------------
    // Stage‑1 : pivot row 0
    //-------------------------------------------------------------------
	// |largest| first actual value between rows 0,1,2
    logic [1:0] pivot0_row;
    always_comb begin
		pivot0_row = 0;
		if(abs_val(mat0[1][0]) > abs_val(mat0[0][0]))
			pivot0_row = 1;
		if(abs_val(mat0[2][0]) > abs_val(mat0[pivot0_row][0]))
			pivot0_row = 2;
    end


    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v1 <= 0;
		else begin
			v1 <= v0 && stage0_barrier_ready;
        // Unrolled assignments for readability/retiming
            mat1[0][0] <= mat0[pivot0_row][0];
            mat1[0][1] <= mat0[pivot0_row][1];
            mat1[0][2] <= mat0[pivot0_row][2];
            mat1[0][3] <= mat0[pivot0_row][3];
            mat1[1][0] <= (1 == pivot0_row) ? mat0[0][0] : mat0[1][0];
            mat1[1][1] <= (1 == pivot0_row) ? mat0[0][1] : mat0[1][1];
            mat1[1][2] <= (1 == pivot0_row) ? mat0[0][2] : mat0[1][2];
            mat1[1][3] <= (1 == pivot0_row) ? mat0[0][3] : mat0[1][3];
            mat1[2][0] <= (2 == pivot0_row) ? mat0[0][0] : mat0[2][0];
            mat1[2][1] <= (2 == pivot0_row) ? mat0[0][1] : mat0[2][1];
            mat1[2][2] <= (2 == pivot0_row) ? mat0[0][2] : mat0[2][2];
            mat1[2][3] <= (2 == pivot0_row) ? mat0[0][3] : mat0[2][3];
		end
    end

    //-------------------------------------------------------------------
    // Stage 2 : normalize row‑0 (4 div)
    //-------------------------------------------------------------------
	//mat2[0][c] = mat1[0][0] / mat1[0][c], mat2[i][c] = mat1[i][c] (for rows 1,2)
    logic signed [WIDTH-1:0] div0_num[0:3], div0_den[0:3], div0_res[0:3];
    logic [3:0] div0_done, div0_ready [0:3];

	assign pivot0_is_zero = v1 & (mat1[0][0] == '0);
    assign stage2_barrier_ready = div0_ready[0] && div0_ready[1] && div0_ready[2] && div0_ready[3];

    generate //4 parallel computed cals cuz of generate
		for (genvar g = 0; g < 4; ++g) begin: DIV0

			logic signed [2*WIDTH-1:0] num64_ext;
            assign num64_ext = $signed(mat1[0][g]) <<< QFRAC; // move into the int area for fix point div
			
            always_comb begin
                if (num64_ext > (1 <<< (2*WIDTH-1)-1)) num64_ext = (1 <<< (2*WIDTH-1)-1);
                else if (num64_ext < -(1 <<< (2*WIDTH-1))) num64_ext = -(1 <<< (2*WIDTH-1));
            end
            assign div0_num[g] = num64_ext[WIDTH + QFRAC - 1 : QFRAC];
			assign div0_den[g] = mat1[0][0];

			fxDiv #() d0(
				.clk(clk), .rst_n(rst_n), 
                .valid_in(v1 && !pivot0_is_zero),
				.valid_out(div0_done[g]),
                .ready_in(stage3_barrier_ready), 
                .ready_out(div0_ready[g])
                .numerator(div0_num[g]), 
                .denominator(div0_den[g]), 
                .result(div0_res[g]),
            );
    	end
	endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v2 <= 0;
		else begin
			v2 <= (&div0_done) && !pivot0_is_zero//if all divisions are complete
			// Unrolled for mat2 just cuz
            mat2[0][0] <= div0_res[0];
            mat2[0][1] <= div0_res[1];
            mat2[0][2] <= div0_res[2];
            mat2[0][3] <= div0_res[3];
            mat2[1][0] <= mat1[1][0];
            mat2[1][1] <= mat1[1][1];
            mat2[1][2] <= mat1[1][2];
            mat2[1][3] <= mat1[1][3];
            mat2[2][0] <= mat1[2][0];
            mat2[2][1] <= mat1[2][1];
            mat2[2][2] <= mat1[2][2];
            mat2[2][3] <= mat1[2][3];
		end
    end

    //-------------------------------------------------------------------
    // Stage 3 : eliminate col‑0 (8 mul)
    //-------------------------------------------------------------------
	//new_row1[c] = old_row1[c] − row0[0] * row0[c], new_row2[c] = old_row2[c] − row1[0] * row0[c]

    logic signed [WIDTH-1 : 0] mul0_r0[0:3], mul0_r1[0:3];
    logic [3:0] mul0_done_r0, mul0_done_r1;
    logic [3:0] mul0_ready_r0, mul0_ready_r1;
    assign stage3_barrier_ready = (&mul0_ready_r0) && (&mul0_ready_r1);

    generate for (genvar c = 0; c < 4; c++) begin: MUL0
		fxMul #() m0(
			.clk(clk), .rst_n(rst_n), 
            .valid_in(v2),
			.valid_out(mul0_done_r0[c])
            .ready_out(mul0_ready_r0[c]), 
            .ready_in(stage5_barrier_ready),
            .a(mat2[1][0]), 
            .b(mat2[0][c]), 
            .result(mul0_r0[c])
        );

		fxMul #() m1(
			.clk(clk), .rst_n(rst_n), 
            .valid_in(v2),
			.valid_out(mul0_done_r1[c]),
            .ready_out(mul0_ready_r1[c]), 
            .ready_in(stage5_barrier_ready),
            .a(mat2[2][0]), 
            .b(mat2[0][c]), 
            .result(mul0_r1[c])
        );
    end endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v3 <= 0;
		else begin
			v3 <= (&mul0_done_r0) && (&mul0_done_r1); //all high, ex: 4'b1111

			for(int j = 0; j < 4; ++j) begin
				mat3[0][j] <= mat2[0][j];
				mat3[1][j] <= mat2[1][j] - mul0_r0[j];
				mat3[2][j] <= mat2[2][j] - mul0_r1[j];
			end
		end
    end

    //-------------------------------------------------------------------
    // Stage‑4 : pivot row‑1
    //-------------------------------------------------------------------
	// |largest| first actual value between rows 1,2
    logic[1:0] pivot1_row;

    always_comb begin
		pivot1_row = 1;
		if (abs_val(mat3[2][1]) > abs_val(mat3[1][1]))
			pivot1_row = 2;
    end

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v4 <= 0;
		else begin
			v4 <= v3;
			mat4[0][0] <= mat3[0][0];//screw for loops
            mat4[0][1] <= mat3[0][1];
            mat4[0][2] <= mat3[0][2];
            mat4[0][3] <= mat3[0][3];
            mat4[1][0] <= mat3[1][0];
            mat4[1][1] <= mat3[pivot1_row][1];
            mat4[1][2] <= mat3[pivot1_row][2];
            mat4[1][3] <= mat3[pivot1_row][3];
            mat4[2][0] <= mat3[2][0];
            mat4[2][1] <= (pivot1_row == 2) ? mat3[1][1] : mat3[2][1];
            mat4[2][2] <= (pivot1_row == 2) ? mat3[1][2] : mat3[2][2];
            mat4[2][3] <= (pivot1_row == 2) ? mat3[1][3] : mat3[2][3];
		end
    end

    //-------------------------------------------------------------------
    // Stage 5 : normalize row‑1 (3 div)
    //-------------------------------------------------------------------
	//mat5[1][c] = mat4[1][1] / mat4[1][c], mat5[i][c] = mat4[i][c] (for rows 0,2), mat5[1][0] = mat4[1][0]
    logic signed [WIDTH-1:0] div1_num[0:2], div1_den[0:2], div1_res[0:2];
    logic [2:0] div1_done;
    logic [2:0] div1_ready;
	assign pivot1_is_zero = v4 && (mat4[1][1] == '0);
    assign stage5_barrier_ready = div1_ready[0] && div1_ready[1] && div1_ready[2];
	
	generate for (genvar g = 0; g < 3; g++) begin : DIV1

		logic signed [2 * WIDTH - 1 : 0] num64_ext1;
        assign num64_ext1 = $signed(mat4[1][g+1]) <<< QFRAC;
        
		always_comb begin
            if (num64_ext1 > (1 <<< (2*WIDTH-1)-1)) 
                num64_ext1 = (1 <<< (2*WIDTH-1)-1);
            else if (num64_ext1 < -(1 <<< (2*WIDTH-1))) 
                num64_ext1 = -(1 <<< (2*WIDTH-1));
        end
        assign div1_num[g] = num64_ext1[WIDTH + QFRAC - 1 : QFRAC];
        assign div1_den[g] = mat4[1][1];
		
		fxDiv #() d1(
			.clk(clk), .rst_n(rst_n), 
            .valid_in(v4 && !pivot1_is_zero),
			.valid_out(div1_done[g]),
            .ready_out(div1_ready[g]), 
            .ready_in(stage6b_barrier_ready),
            .numerator(div1_num[g]), 
            .denominator(div1_den[g]), 
            .result(div1_res[g])
        );
	end endgenerate

	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v5 <= '0;
		else begin
			v5 <= (&div1_done) && !pivot1_is_zero;
            mat5[0][0] <= mat4[0][0];
            mat5[0][1] <= mat4[0][1];
            mat5[0][2] <= mat4[0][2];
            mat5[0][3] <= mat4[0][3];
            mat5[1][0] <= mat4[1][0];
            mat5[1][1] <= div1_res[0];
            mat5[1][2] <= div1_res[1];
            mat5[1][3] <= div1_res[2];
            mat5[2][0] <= mat4[2][0];
            mat5[2][1] <= mat4[2][1];
            mat5[2][2] <= mat4[2][2];
            mat5[2][3] <= mat4[2][3];
		end
	end

    //-------------------------------------------------------------------
    // Stage‑6 : eliminate col‑1 in row‑2 
    //-------------------------------------------------------------------
	//mat6[2][c] = mat5[2][c] − mat5[2][1] * mat5[1][c], mat6[i][c] = mat5[i][c] (for rows 0,1), mat6[2][0] = mat5[2][0]
	logic signed [WIDTH-1:0] mul_elim_res[3];  // For j=1 to 3
    logic [2:0] mul_elim_valid, mul_elim_ready;
    assign stage6_barrier_ready = &mul_elim_ready;

    generate for (genvar j = 1; j < 4; j++) begin : ELIM_MUL
        logic signed [WIDTH-1:0] mul_res;
        fxMul_always #() mul_elim (
            .clk(clk), .rst_n(rst_n), 
            .valid_in(v5),
            .valid_out(mul_elim_valid[j-1]),
            .ready_in(stage6b_barrier_ready),
            .ready_out(mul_elim_ready[j-1]),
            .a(mat5[2][1]), 
            .b(mat5[1][j]), 
            .result(mul_res)
        );
    end endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v6 <= 0;
        end else begin
            v6 <= v5 && (&mul_elim_valid);
            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 4; j++) begin
                    if (i < 2) 
                        mat6[i][j] <= mat5[i][j];  // Rows 0/1 unchanged
                    else 
                        mat6[2][j] <= (j == 0) ? mat5[2][0] : mat5[2][j] - mul_elim_res[j-1];
                end
            end
        end
    end
	//------------------------------------------------------------------
	// Stage-6B : normalise row-2
	//------------------------------------------------------------------
	logic signed [WIDTH-1:0] div2_num[0:2], div2_res[0:2];
	logic signed [WIDTH-1:0] div2_den;
	logic [2:0] div2_done;
    logic [2:0] div2_ready;

	assign div2_den = mat6[2][2];
    assign stage6b_barrier_ready = &div2_ready;

	generate for (genvar g = 0; g < 3; ++g) begin : DIV2

		logic signed [2*WIDTH-1:0] num64_ext2;
        assign num64_ext2 = $signed(mat6[2][g+1]) <<< QFRAC;

        always_comb begin
            if (num64_ext2 > (1 <<< (2*WIDTH-1)-1)) 
                num64_ext2 = (1 <<< (2*WIDTH-1)-1);
            else if (num64_ext2 < -(1 <<< (2*WIDTH-1))) 
                num64_ext2 = -(1 <<< (2*WIDTH-1));
        end

        assign div2_num[g] = num64_ext2[WIDTH+QFRAC-1 : QFRAC];

        fxDiv #() d2 (
            .clk(clk), .rst_n(rst_n), 
            .valid_in(v6),
            .valid_out(div2_done[g]),
            .ready_in(stage7_barrier_ready),
            .ready_out(div2_ready[g]), 
            .numerator(div2_num[g]), 
            .denominator(div2_den), 
            .result(div2_res[g])
        );
    end endgenerate

	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v6b <= '0;
		else
			v6b <= &div2_done;

		// copy rows 0 and 1 unchanged
		for (int j=0; j<4; ++j) begin
			mat7[0][j] <= mat6[0][j];
			mat7[1][j] <= mat6[1][j];
		end

		mat7[2][0] <= mat6[2][0];          // col-0 unchanged
		for (int j = 1; j < 4; ++j)
			mat7[2][j] <= div2_res[j-1];     // normalised Q16.16
	end



    //-------------------------------------------------------------------
    // Stage‑7 : back subs 
    //-------------------------------------------------------------------
    logic signed [WIDTH-1:0] bt2;
	assign pivot2_is_zero = v6b && (mat7[2][2] == '0);

    fxDiv #() div_b2 (
        .clk(clk), .rst_n(rst_n),
        .valid_in(v6b && !pivot2_is_zero),
        .valid_out(v7a),
        .ready_in(mul12_ready),
        .ready_out(div_b2_ready), 
        .numerator(mat7[2][3] <<< QFRAC), 
        .denominator(mat7[2][2]), 
        .result(bt2));

    //beta[1] = (mat6[1][3] – mat6[1][2]*beta[2]) / mat6[1][1]
	logic signed [WIDTH-1:0] prod12, bt1;

	fxMul #() mul12(
		.clk(clk), .rst_n(rst_n), 
        .valid_in(v7a), 
		.valid_out(v7b1), 
        .ready_in(div_b1_ready),
        .ready_out(mul12_ready), 
        .a(mat7[1][2]), 
        .b(bt2), 
        .result(prod12)
	);

	fxDiv #() div_b1(
		.clk(clk), 
        .rst_n(rst_n), 
        .valid_in(v7b1),
        .valid_out(v7b), 
        .ready_in(mul01_ready),
        .ready_out(div_b1_ready),
		.numerator(($signed(mat7[1][3]) - prod12) <<< QFRAC), 
		.denominator(mat7[1][1]), 
        .result(bt1)
	);


	// beta[0] = (beta[0] – mat6[0][1]*beta[1]) / mat6[0][0]
	logic signed [WIDTH-1:0] prod01, bt0;

	fxMul #() mul01 (
		.clk(clk), .rst_n(rst_n), 
        .valid_in(v7b),
        .valid_out (v7c1), 
        .ready_in(mul02_ready),
        .ready_out(mul01_ready),
		.a(mat7[0][1]), 
        .b(bt1), 
        .result(prod01)
	);

    fxMul_always #() mul02 (
        .clk(clk), .rst_n(rst_n), 
        .valid_in(v7c),
        .valid_out (v7c1), 
        .ready_in(div_b0_ready),
        .ready_out(mul02_ready), 
        .a(mat7[0][2]), 
        .b(bt2), 
        .result(prod02)
    );

	fxDiv #() div_b0 (
		.clk(clk), .rst_n(rst_n), 
        .valid_in(v7c1),
        .valid_out(v7c), 
        .ready_in(ready_in),
        .ready_out(div_b0_ready),
		.numerator(($signed(mat7[0][3]) - prod01) <<< QFRAC), 
		.denominator(mat7[0][0]), 
        .result(bt0)
	);

    assign stage7_barrier_ready = div_b2_ready && mul12_ready && div_b1_ready && mul01_ready && mul02_ready && div_b0_ready;
	// -------------------------------------------------------------
    // Stage-7d Fallback if singular, look at accumulator code for why
    // -------------------------------------------------------------
    logic v_fallback;
    assign v_fallback = v7c && singular_err;   // bad pivot
    logic mean_valid;
    logic signed [WIDTH-1:0] mean_payoff;

    fxDiv #() div_mean (
        .clk(clk), .rst_n(rst_n), 
        .valid_in(v_fallback),
        .valid_out(mean_valid),
        .ready_in(ready_in),
        .ready_out(mean_ready),
        .numerator(sumy_latched <<< QFRAC), 
        .denominator(sum1_latched ), 
		.result(mean_payoff)
    );


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
            beta[0] <= '0;
			beta[1] <= '0;
			beta[2] <= '0;
        end else begin
            // normal path
            if (mean_valid && !singular_err && ready_in) begin
                beta[2]   <= bt2;
                beta[1]   <= bt1;
                beta[0]   <= bt0;
                valid_out <= 1'b1;
            end
            // fallback path
            else if (mean_valid && singular_err && ready_in) begin
                beta[2]   <= '0;
                beta[1]   <= '0;
                beta[0]   <= mean_payoff;
                valid_out <= 1'b1;
            end
            else
                valid_out <= 1'b0; 
        end
    end

    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(beta)) 
            else $error("Regression output stall overwrite");
        
        assert property (@(posedge clk) disable iff (!rst_n) skid_valid && !ready_in |=> $stable(skid_mat_flat)) 
            else $error("Regression input skid stall overwrite");
        
        assert property (@(posedge clk) disable iff (!rst_n) singular_err |=> singular_err) 
            else $error("singular_err not sticky");
        
        assert property (@(posedge clk) disable iff (!rst_n) v2 && stage2_barrier_ready |-> $stable(mat2)) 
            else $error("Stage2 desync on stall");
    end
endmodule

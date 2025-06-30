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
		if (!rst_n || v0)
			singular_err <=  0;
		else if (pivot0_is_zero | pivot1_is_zero | pivot2_is_zero)
			singular_err <=  1;           // sticky until reset
	end
	

    //-----------------------------------------------------------
    // Matrix registers (augmented 3×4) per stage
    //-----------------------------------------------------------

    logic signed [WIDTH-1:0] mat0[0:2][0:3];
    logic signed [WIDTH-1:0] mat1[0:2][0:3];
    logic signed [WIDTH-1:0] mat2[0:2][0:3];
    logic signed [WIDTH-1:0] mat3[0:2][0:3];
    logic signed [WIDTH-1:0] mat4[0:2][0:3];
    logic signed [WIDTH-1:0] mat5[0:2][0:3];
    logic signed [WIDTH-1:0] mat6[0:2][0:3];
	logic signed [WIDTH-1:0] mat7[0:2][0:3];

  	//-------------------------------------------------------------------
    // Stage 0 : get inputs
    //-------------------------------------------------------------------
	logic v0;
	logic signed [WIDTH-1:0] sum1_latched; 
	logic signed [WIDTH-1:0] sumy_latched; 
    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) 
			v0 <= 0;
		else begin
			v0 <= valid_in;
			for (int i = 0; i < 3; ++i) begin
				for (int j = 0; j < 4; ++j)
					mat0[i][j] <= mat_flat[i*4+j];
			end
			sum1_latched <= mat_flat[0];
        	sumy_latched <= mat_flat[3];
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
			v1<=v0;

			for (int i = 0; i < 3; ++i) begin
				for (int j = 0; j < 4; ++j) begin
					case(i)
					0:
						mat1[i][j] <= mat0[pivot0_row][j];
					default:
						if (i[1:0] == pivot0_row)
							mat1[i][j] <= mat0[0][j];
						else
							mat1[i][j] <= mat0[i][j];//whatever
					endcase
				end
			end
		end
    end

    //-------------------------------------------------------------------
    // Stage 2 : normalize row‑0 (4 div)
    //-------------------------------------------------------------------
	//mat2[0][c]= mat1[0][0] / mat1[0][c], mat2[i][c] = mat1[i][c] (for rows 1,2)
    logic signed [WIDTH-1:0] div0_num[0:3], div0_den[0:3], div0_res[0:3];
    logic [3:0] div0_done;
	assign pivot0_is_zero = v1 & (mat1[0][0] == '0);

    generate //4 parallel computed cals cuz of generate
		for (genvar g = 0; g < 4; ++g) begin: DIV0

			/* verilator lint_off UNUSED */
			logic signed [2*WIDTH-1:0] num64_ext = $signed(mat1[0][g]) <<< QFRAC; // move into the int area for fix point div
			/* verilator lint_on WIDTH */
			assign div0_num[g] = num64_ext[WIDTH + QFRAC - 1 : QFRAC];
			assign div0_den[g] = mat1[0][0];

			fxDiv #() d0(
				.clk(clk), .rst_n(rst_n), .valid_in(v1 & ~pivot0_is_zero),
				.numerator(div0_num[g]), .denominator(div0_den[g]), .result(div0_res[g]), .valid_out(div0_done[g]));
    	end
	endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v2 <= 0;
		else begin
			v2 <= (&div0_done) & ~pivot0_is_zero;//if all divisions are complete

			for (int i = 0; i < 3; ++i)
				for (int j = 0; j < 4; ++j)
					mat2[i][j] <= (i == 0 ? div0_res[j] : mat1[i][j]);
		end
    end

    //-------------------------------------------------------------------
    // Stage 3 : eliminate col‑0 (8 mul)
    //-------------------------------------------------------------------
	//new_row1[c] = old_row1[c] − row0[0] * row0[c], new_row2[c] = old_row2[c] − row1[0] * row0[c]

    logic signed [WIDTH-1 : 0] mul0_r0[0:3], mul0_r1[0:3];
    logic [3:0] mul0_done_r0, mul0_done_r1;
    generate for (genvar c = 0; c < 4; c++) begin: MUL0
		fxMul_always  #() m0(
			.clk(clk), .rst_n(rst_n), .valid_in(v2),
			.a(mat2[1][0]), .b(mat2[0][c]), .result(mul0_r0[c]), .valid_out(mul0_done_r0[c]));

		fxMul_always  #() m1(
			.clk(clk), .rst_n(rst_n), .valid_in(v2),
			.a(mat2[2][0]), .b(mat2[0][c]), .result(mul0_r1[c]), .valid_out(mul0_done_r1[c]));
    end endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v3 <= 0;
		else begin
			v3 <= &mul0_done_r0 & &mul0_done_r1; //all high, ex: 4'b1111

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
		pivot1_row=1;
		if (abs_val(mat3[2][1]) > abs_val(mat3[1][1]))
			pivot1_row = 2;
    end

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v4 <= 0;
		else begin
			v4 <= v3;
			for (int i = 0; i < 3; ++i) begin
				mat4[i][0] <= mat3[i][0];

				for (int j = 1; j < 4; ++j)
					if (i == 1)
						mat4[i][j] <= mat3[pivot1_row][j];
					else if (i[1:0] == pivot1_row)
						mat4[i][j] <= mat3[1][j];
					else
						mat4[i][j] <= mat3[i][j];
			end
		end
    end

    //-------------------------------------------------------------------
    // Stage 5 : normalize row‑1 (3 div)
    //-------------------------------------------------------------------
	//mat5[1][c] = mat4[1][1] / mat4[1][c], mat5[i][c] = mat4[i][c] (for rows 0,2), mat5[1][0] = mat4[1][0]
    logic signed [WIDTH-1:0] div1_num[1:3],div1_den[1:3],div1_res[1:3];
    logic [3:1] div1_done;
	assign pivot1_is_zero = v4 & (mat4[1][1] == '0);
	
    
	generate for (genvar g = 1; g < 4; g++) begin:DIV1

		/* verilator lint_off UNUSED */
		logic signed [2 * WIDTH - 1 : 0] num64_ext1;
		/* verilator lint_on UNUSED */

		assign num64_ext1 = $signed({{WIDTH{mat4[1][g][WIDTH - 1]}}, mat4[1][g]}) <<< QFRAC;
		assign div1_num[g] = num64_ext1[WIDTH + QFRAC - 1 : QFRAC];
		assign div1_den[g]= mat4[1][1];
		
		fxDiv #() d1(
			.clk(clk), .rst_n(rst_n), .valid_in(v4 & ~pivot1_is_zero),
			.numerator(div1_num[g]), .denominator(div1_den[g]), .result(div1_res[g]), .valid_out(div1_done[g]));
		end 
	endgenerate

	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v5 <= 0;
		else begin
			v5 <= (&div1_done[3:1]) & ~pivot1_is_zero;

			for (int j = 0; j < 4; ++j) begin
				mat5[0][j] <= mat4[0][j];
				mat5[2][j] <= mat4[2][j];
			end

			mat5[1][0]<=mat4[1][0];
			for (int j = 1; j < 4; ++j)
				mat5[1][j] <= div1_res[j];
		end
	end

    //-------------------------------------------------------------------
    // Stage‑6 : eliminate col‑1 in row‑2 
    //-------------------------------------------------------------------
	//mat6[2][c] = mat5[2][c] − mat5[2][1] * mat5[1][c], mat6[i][c] = mat5[i][c] (for rows 0,1), mat6[2][0] = mat5[2][0]
	logic v6_done;
    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			v6 <= 1'b0;
			v6_done <= 1'b0;
		end else begin
			v6 <= v5;
			v6_done <= v6;

			// pass rows 0 & 1 straight through
			for (int j = 0; j < 4; ++j) begin
				mat6[0][j] <= mat5[0][j];
				mat6[1][j] <= mat5[1][j];
			end

			mat6[2][0] <= mat5[2][0];

			for (int j = 1; j < 4; ++j) begin
				logic signed [2*WIDTH-1:0] prod64;
				prod64 = $signed(mat5[2][1]) * $signed(mat5[1][j]);
				prod64 = prod64 >>> QFRAC;
				mat6[2][j] <= mat5[2][j] - prod64[WIDTH+QFRAC-1 : QFRAC];
			end
		end
	end
	//------------------------------------------------------------------
	// Stage-6B : normalise row-2
	//------------------------------------------------------------------
	logic signed [WIDTH-1:0] div2_num[1:3];
	logic signed [WIDTH-1:0] div2_res[1:3];
	logic signed [WIDTH-1:0] div2_den;
	logic [3:1]               div2_done;

	assign div2_den = mat6[2][2];

	generate for (genvar g = 1; g < 4; ++g) begin : DIV2

		/* verilator lint_off UNUSED */
		logic signed [2*WIDTH-1:0] num64_ext2;
		/* verilator lint_on UNUSED */

		assign num64_ext2 = $signed({{WIDTH{mat6[2][g][WIDTH-1]}}, mat6[2][g]}) <<< QFRAC;
		assign div2_num[g] = num64_ext2[WIDTH+QFRAC-1 : QFRAC];

		fxDiv #() d2 (
			.clk(clk), .rst_n(rst_n), .valid_in(v6_done),
			.numerator(div2_num[g]), .denominator(div2_den), .result(div2_res[g]), .valid_out(div2_done[g]));
		end
	endgenerate

	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v6b <= 1'b0;
		else
			v6b <= &div2_done;

		// copy rows 0 and 1 unchanged
		for (int j=0; j<4; ++j) begin
			mat7[0][j] <= mat6[0][j];
			mat7[1][j] <= mat6[1][j];
		end
		mat7[2][0] <= mat6[2][0];          // col-0 unchanged
		for (int j=1; j<4; ++j)
			mat7[2][j] <= div2_res[j];     // normalised Q16.16
	end



    //-------------------------------------------------------------------
    // Stage‑7 : back subs 
    //-------------------------------------------------------------------
    logic signed [WIDTH-1:0] bt2;
	assign pivot2_is_zero = v6b & (mat7[2][2] == '0);
    fxDiv #() div_b2 (
      .clk(clk), .rst_n(rst_n),.valid_in(v6b & ~pivot2_is_zero),
      .numerator(mat7[2][3] <<< QFRAC), .denominator(mat7[2][2]), .valid_out(v7a), .result(bt2));

    //beta[1] = (mat6[1][3] – mat6[1][2]*beta[2]) / mat6[1][1]
	logic signed [WIDTH-1:0] prod12, bt1;

	fxMul_always #() mul12(
		.clk(clk), .rst_n(rst_n), .valid_in(v7a), 
		.a(mat7[1][2]), .b(bt2), .valid_out(v7b1), .result(prod12)
	);

	fxDiv #() div_b1(
		.clk(clk), .rst_n(rst_n), .valid_in(v7b1),
		.numerator(($signed(mat7[1][3]) - prod12) <<< QFRAC), 
		.denominator(mat7[1][1]), .valid_out(v7b), .result(bt1)
	);


	// beta[0] = (beta[0] – mat6[0][1]*beta[1]) / mat6[0][0]
	logic signed [WIDTH-1:0] prod01, bt0;
	fxMul_always #() mul01 (
		.clk(clk), .rst_n(rst_n), .valid_in(v7b),
		.a(mat7[0][1]), .b(bt1), .valid_out (v7c1), .result(prod01)
	);

	fxDiv #() div_b0 (
		.clk(clk), .rst_n (rst_n), .valid_in(v7c1),
		.numerator(($signed(mat7[0][3]) - prod01) <<< QFRAC), 
		.denominator(mat7[0][0]), .valid_out(v7c), .result(bt0)
	);

	// -------------------------------------------------------------
    // Stage-7d Fallback if singular, look at accumulator code for why
    // -------------------------------------------------------------
    logic v_fallback  = v7c &  singular_err;   // bad pivot
    logic v_good      = v7c & ~singular_err;   // normal finish
	logic mean_valid;
    logic signed [WIDTH-1:0] mean_payoff;

    fxDiv #(.WIDTH(WIDTH),.QINT(QINT)) div_mean (
        .clk(clk), .rst_n(rst_n), .valid_in(v_fallback),
        .numerator(sumy_latched  <<< QFRAC), .denominator(sum1_latched ), 
		.result(mean_payoff), .valid_out(mean_valid)
    );


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
            beta[0] <= '0;
			beta[1] <= '0;
			beta[2] <= '0;
        end else begin
            // normal path
            if (v_mean & solver_ready) begin
                beta[2]   <= bt2;
                beta[1]   <= bt1;
                beta[0]   <= bt0;
                valid_out <= 1'b1;
            end
            // fallback path
            else if (mean_valid & solver_ready) begin
                beta[2]   <= '0;
                beta[1]   <= '0;
                beta[0]   <= mean_payoff;
                valid_out <= 1'b1;
            end
            else
                valid_out <= 1'b0; 
        end
    end
endmodule

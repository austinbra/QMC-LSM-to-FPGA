module pipelinedRegression3x3 #(// Deep pipelined Gaussian elimination (Q16.16)
	parameter int WIDTH = 32,
    parameter int QINT = 16,
    parameter int QFRAC = WIDTH - QINT,
    parameter int DIV_LATENCY = 3,
    parameter int MUL_LATENCY = 2
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic signed [WIDTH-1:0] A_flat [0:8],
    input  logic signed [WIDTH-1:0] B_flat [0:2],
    output logic valid_out,
    output logic signed [WIDTH-1:0] beta [0:2]
);
    logic v0, v1, v2, v3, v4, v5, v6, v7;

    // helper function for abs value 
    function automatic logic signed [WIDTH-1:0] abs_val(input logic signed [WIDTH-1:0] x);
      	abs_val = x[WIDTH-1] ? -x : x;
    endfunction

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

  	//-------------------------------------------------------------------
    // Stage 0 : get inputs
    //-------------------------------------------------------------------

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v0 <= 0;
		else begin
			v0 <= valid_in;
			for (int i = 0; i < 3; ++i) begin
				for (int j = 0; j < 3; ++j)
					mat0[i][j] <= A_flat[i*3+j];
				mat0[i][3] <= B_flat[i];
			end
		end
    end

  	//-------------------------------------------------------------------
    // Stage‑1 : pivot row 0
    //-------------------------------------------------------------------

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
						if(i == pivot0_row)
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

    logic signed [WIDTH-1:0] div0_num[0:3], div0_den[0:3], div0_res[0:3];
    logic        [3:0]       div0_done;

    generate for(genvar g = 0; g < 4; ++g) begin:DIV0
		logic signed [2 * WIDTH - 1 : 0] num64_ext;

		assign num64_ext = $signed({{WIDTH{mat1[0][g][WIDTH - 1]}}, mat1[0][g]}) <<< QFRAC;
		assign div0_num[g] = num64_ext[WIDTH + QFRAC - 1 : QFRAC];
		assign div0_den[g] = mat1[0][0];

		fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(DIV_LATENCY)) d0(
			.clk(clk),
			.rst_n(rst_n),
			.start(v1),
			.numerator(div0_num[g]),
			.denominator(div0_den[g]),
			.result(div0_res[g]),
			.done(div0_done[g]));
    end endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) v2 <= 0; else begin
			v2 <= &div0_done;

			for (int i = 0; i < 3; ++i)
				for (int j = 0; j < 4; ++j)
					mat2[i][j] <= (i == 0? div0_res[j] : mat1[i][j]);
		end
    end

    //-------------------------------------------------------------------
    // Stage‑3 : eliminate col‑0 (8 mul)
    //-------------------------------------------------------------------

    logic signed [WIDTH-1:0] mul0_r0[0:3], mul0_r1[0:3];
    logic [3:0] mul0_done_r0, mul0_done_r1;

    generate for (genvar c = 0; c < 4; c++) begin: MUL0
      fxMul #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(MUL_LATENCY)) m0(
        .clk(clk),
		.rst_n(rst_n),
		.start(v2),
        .a(mat2[1][0]),
		.b(mat2[0][c]),
		.result(mul0_r0[c]),
		.done(mul0_done_r0[c]));

      fxMul #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(MUL_LATENCY)) m1(
        .clk(clk),
		.rst_n(rst_n),
		.start(v2),
        .a(mat2[2][0]),
		.b(mat2[0][c]),
		.result(mul0_r1[c]),
		.done(mul0_done_r1[c]));
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
    // Stage‑5 : normalize row‑1 (3 div)
    //-------------------------------------------------------------------
    logic signed [WIDTH-1:0] div1_num[1:3],div1_den[1:3],div1_res[1:3];
    logic [3:1] div1_done;

    generate for (genvar g = 1; g < 4; g++) begin:DIV1
		logic signed [2 * WIDTH-1:0] num64_ext1;

		assign num64_ext1 = $signed({{WIDTH{mat4[1][g][WIDTH - 1]}}, mat4[1][g]}) <<< QFRAC;
		assign div1_num[g] = num64_ext1[WIDTH + QFRAC - 1 : QFRAC];
		assign div1_den[g]= mat4[1][1];

		fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(DIV_LATENCY)) d1(
			.clk(clk),
			.rst_n(rst_n),
			.start(v4),
			.numerator(div1_num[g]),
			.denominator(div1_den[g]),
			.result(div1_res[g]),
			.done(div1_done[g]));
		end endgenerate

	always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) v5 <= 0; else begin
			v5 <= &div1_done[3:1];

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
    // Stage‑6 : eliminate col‑1 in row‑2 (combinational)
    //-------------------------------------------------------------------

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n)
			v6 <= 0;
		else begin
			v6 <= v5;
			// pass rows 0 & 1
			for(int j = 0; j < 4; ++j) begin
				mat6[0][j] <= mat5[0][j];
				mat6[1][j] <= mat5[1][j];
			end
			
			mat6[2][0]<=mat5[2][0];
			for(int j = 1; j < 4; ++j) begin
				logic signed [2 * WIDTH - 1 : 0] prod64;
				prod64 = $signed({{WIDTH{mat5[2][1][WIDTH-1]}}, mat5[2][1]}) * $signed({{WIDTH{mat5[1][j][WIDTH-1]}}, mat5[1][j]});
				prod64 = prod64 >>> QFRAC; // undo scale
				mat6[2][j] <= mat5[2][j] - prod64[WIDTH + QFRAC - 1 : QFRAC];
			end
		end
    end

    //-------------------------------------------------------------------
    // Stage‑7 : back‑substitution (single‑cycle)
    //-------------------------------------------------------------------

    always_ff @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			v7 <= 0;
			valid_out <= 0;
			beta[0] <= 0;
			beta[1] <= 0;
			beta[2] <= 0;
		end else begin
			v7 <= v6;
			valid_out<=v7;
			if (v7) begin
				logic signed [2*WIDTH-1:0] num64, den64, div64, prod64;
				logic signed [WIDTH-1:0] bt2, bt1, bt0;

				// beta2
				num64 = $signed({{WIDTH{mat6[2][3][WIDTH-1]}}, mat6[2][3]}) <<< QFRAC;
				den64 = $signed({{WIDTH{mat6[2][2][WIDTH-1]}}, mat6[2][2]});
				div64 = num64/den64;
				bt2 = div64[WIDTH-1:0];

				// beta1
				prod64 = $signed({{WIDTH{mat6[1][2][WIDTH-1]}},mat6[1][2]}) * $signed({{WIDTH{bt2[WIDTH-1]}},bt2}) >>> QFRAC;
				num64  = ($signed({{WIDTH{mat6[1][3][WIDTH-1]}},mat6[1][3]}) - prod64) <<< QFRAC;
				den64  = $signed({{WIDTH{mat6[1][1][WIDTH-1]}},mat6[1][1]});
				div64  = num64/den64;
				bt1 = div64[WIDTH-1:0];

				// beta0
				prod64 = $signed({{WIDTH{mat6[0][1][WIDTH-1]}}, mat6[0][1]}) * $signed({{WIDTH{bt1[WIDTH-1]}}, bt1}) >>> QFRAC;
				num64  = ($signed({{WIDTH{mat6[0][3][WIDTH-1]}}, mat6[0][3]}) - prod64) <<< QFRAC;
				den64  = $signed({{WIDTH{mat6[0][0][WIDTH-1]}}, mat6[0][0]});
				div64  = num64/den64;
				bt0 = div64[WIDTH-1:0];

				beta[2] <= bt2;
				beta[1] <= bt1;
				beta[0] <= bt0;
			end
		end
    end
endmodule

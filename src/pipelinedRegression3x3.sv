module pipelinedRegression3x3 #(
  parameter int WIDTH = 32,
  parameter int QFRAC = 16
)(
  input  logic                  clk,
  input  logic                  rst_n,
  input  logic                  valid_in,
  input  logic signed [WIDTH-1:0] A_flat [0:8],
  input  logic signed [WIDTH-1:0] B_flat [0:2],
  output logic                  valid_out,
  output logic signed [WIDTH-1:0] beta    [0:2]
);

  // ------------------------------------------------------------------------
  // Stage 0: capture inputs + valid_in → v0 + mat0 (3×4)
  // ------------------------------------------------------------------------
  logic                  v0;
  logic signed [WIDTH-1:0] mat0 [0:2][0:3];

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      v0 <= 1'b0;
    end else begin
      v0 <= valid_in;
      for (int i = 0; i < 3; i++) begin
        for (int j = 0; j < 3; j++)
          mat0[i][j] <= A_flat[i*3 + j];
        mat0[i][3] <= B_flat[i];
      end
    end
  end

  // ------------------------------------------------------------------------
  // Stage 1: pivot0 swap → v1 + mat1
  // ------------------------------------------------------------------------
  logic                  v1;
  logic signed [WIDTH-1:0] mat1 [0:2][0:3];
  logic         [1:0]      pivot0_row;

  always_comb begin
    pivot0_row = 0;
    if ((mat0[1][0][WIDTH-1] ? -mat0[1][0] : mat0[1][0])
      > (mat0[pivot0_row][0][WIDTH-1] ? -mat0[pivot0_row][0] : mat0[pivot0_row][0]))
        pivot0_row = 1;
    if ((mat0[2][0][WIDTH-1] ? -mat0[2][0] : mat0[2][0])
      > (mat0[pivot0_row][0][WIDTH-1] ? -mat0[pivot0_row][0] : mat0[pivot0_row][0]))
        pivot0_row = 2;
  end

  always_ff @(posedge clk) begin
    v1 <= v0;
    /* verilator lint_off WIDTH */
    for (int i = 0; i < 3; i++)
      for (int j = 0; j < 4; j++)
        if      (i == 0)               mat1[i][j] <= mat0[pivot0_row][j];
        else if (i == pivot0_row)      mat1[i][j] <= mat0[0][j];
        else                            mat1[i][j] <= mat0[i][j];
    /* verilator lint_on WIDTH */
  end

  // ------------------------------------------------------------------------
  // Stage 2: normalize row0 (4× fxDiv) → v2 + mat2
  // ------------------------------------------------------------------------
  logic                  v2;
  logic signed [WIDTH-1:0] mat2 [0:2][0:3];
  wire signed [WIDTH-1:0] div0_res [0:3];
  wire                    div0_done[0:3];

  generate
    genvar j;
    for (j = 0; j < 4; j = j + 1) begin : NORM0
      fxDiv #(.WIDTH(WIDTH), .QFRAC(QFRAC)) D0 (
        .clk    (clk),    .rst_n(rst_n),
        .num    (mat1[0][j]),
        .denom  (mat1[0][0]),
        .result (div0_res[j])
      );
      assign div0_done[j] = 1'b1; // fxDiv is 1-cycle combinational in this context
    end
  endgenerate

  always_ff @(posedge clk) begin
    // all four divides done next cycle
    v2 <= v1;
    for (int i = 0; i < 3; i++)
      for (int j = 0; j < 4; j++)
        mat2[i][j] <= (i == 0 ? div0_res[j] : mat1[i][j]);
  end

  // ------------------------------------------------------------------------
  // Stage 3: eliminate col0 in rows1,2 (2×4 fxMul) → v3 + mat3
  // ------------------------------------------------------------------------
  logic                  v3;
  logic signed [WIDTH-1:0] mat3 [0:2][0:3];
  wire signed [WIDTH-1:0] mul0_res [0:1][0:3];
  wire                    mul0_done[0:1][0:3];

  generate
    genvar r, c;
    for (r = 1; r < 3; r = r + 1) begin : ELIM0_R
      for (c = 0; c < 4; c = c + 1) begin : ELIM0_C
        fxMul #(.WIDTH(WIDTH), .QFRAC(QFRAC)) M0 (
          .clk    (clk),    .rst_n(rst_n),
          .a      (mat2[r][0]),
          .b      (mat2[0][c]),
          .result (mul0_res[r-1][c])
        );
        assign mul0_done[r-1][c] = 1'b1; // combinational here
      end
    end
  endgenerate

  always_ff @(posedge clk) begin
    v3 <= v2;
    // row0 unchanged
    for (int j = 0; j < 4; j++) mat3[0][j] <= mat2[0][j];
    // subtract products
    for (int rr = 1; rr < 3; rr++)
      for (int cc = 0; cc < 4; cc++)
        mat3[rr][cc] <= mat2[rr][cc] - mul0_res[rr-1][cc];
  end

  // ------------------------------------------------------------------------
  // Stage 4: pivot1 swap → v4 + mat4
  // ------------------------------------------------------------------------
  logic                  v4;
  logic signed [WIDTH-1:0] mat4 [0:2][0:3];
  logic         [1:0]      pivot1_row;

  always_comb begin
    pivot1_row = 1;
    if ((mat3[2][1][WIDTH-1] ? -mat3[2][1] : mat3[2][1])
      > (mat3[1][1][WIDTH-1] ? -mat3[1][1] : mat3[1][1]))
        pivot1_row = 2;
  end

  always_ff @(posedge clk) begin
    v4 <= v3;
    /* verilator lint_off WIDTH */
    for (int i = 0; i < 3; i++)
      for (int j = 1; j < 4; j++)
        if      (i == 1)               mat4[i][j] <= mat3[pivot1_row][j];
        else if (i == pivot1_row)      mat4[i][j] <= mat3[1][j];
        else                            mat4[i][j] <= mat3[i][j];
    /* verilator lint_on WIDTH */
  end

  // ------------------------------------------------------------------------
  // Stage 5: normalize row1 (3× fxDiv) → v5 + mat5
  // ------------------------------------------------------------------------
  logic                  v5;
  logic signed [WIDTH-1:0] mat5 [0:2][0:3];
  wire signed [WIDTH-1:0] div1_res [1:3];

  generate
    for (j = 1; j < 4; j = j + 1) begin : NORM1
      fxDiv #(.WIDTH(WIDTH), .QFRAC(QFRAC)) D1 (
        .clk    (clk),    .rst_n(rst_n),
        .num    (mat4[1][j]),
        .denom  (mat4[1][1]),
        .result (div1_res[j])
      );
    end
  endgenerate

  always_ff @(posedge clk) begin
    v5 <= v4;
    // row0, row2 unchanged
    for (int j = 0; j < 4; j++) mat5[0][j] <= mat4[0][j];
    for (int j = 0; j < 4; j++) mat5[2][j] <= mat4[2][j];
    // write normalized row1
    for (int j = 1; j < 4; j++) mat5[1][j] <= div1_res[j];
    mat5[1][0] <= mat4[1][0];
  end

  // ------------------------------------------------------------------------
  // Stage 6: eliminate col1 in row2 (1×3 fxMul) → v6 + mat6
  // ------------------------------------------------------------------------
  logic                  v6;
  logic signed [WIDTH-1:0] mat6 [0:2][0:3];
  wire signed [WIDTH-1:0] mul2_res [1:3];

  generate
    for (j = 1; j < 4; j = j + 1) begin : ELIM1
      fxMul #(.WIDTH(WIDTH), .QFRAC(QFRAC)) M2 (
        .clk    (clk),     .rst_n(rst_n),
        .a      (mat5[2][1]),
        .b      (mat5[1][j]),
        .result (mul2_res[j])
      );
    end
  endgenerate

  always_ff @(posedge clk) begin
    v6 <= v5;
    for (int j = 0; j < 4; j++) mat6[0][j] <= mat5[0][j];
    for (int j = 0; j < 4; j++) mat6[1][j] <= mat5[1][j];
    // subtract on row2
    for (int j = 0; j < 4; j++)
      mat6[2][j] <= mat5[2][j]
                    - (j>=1 ? mul2_res[j] : 0);
  end

  // ------------------------------------------------------------------------
  // Stage 7: back‐substitution (combinational solves) → v7 + beta
  // ------------------------------------------------------------------------
  logic                  v7;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      v7 <= 1'b0;
      beta[0] <= 0;
      beta[1] <= 0;
      beta[2] <= 0;
    end else begin
      v7 <= v6;
      // β₂ = mat6[2][3]/mat6[2][2]
      beta[2] <= (mat6[2][3] <<< QFRAC) / mat6[2][2];
      // β₁ = (mat6[1][3] – β₂*mat6[1][2])<<<QFRAC / mat6[1][1]
      beta[1] <= (((mat6[1][3]
                    - ((beta[2] * mat6[1][2]) >>> QFRAC))
                   <<< QFRAC)
                  / mat6[1][1]);
      // β₀ = (((mat6[0][3] – β₁*mat6[0][1])<<<QFRAC) / mat6[0][0])
      beta[0] <= (((mat6[0][3]
                    - ((beta[1] * mat6[0][1]) >>> QFRAC))
                   <<< QFRAC)
                  / mat6[0][0]);
    end
  end

  // ------------------------------------------------------------------------
  // valid_out = v7
  // ------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)      valid_out <= 1'b0;
    else             valid_out <= v7;
  end

endmodule

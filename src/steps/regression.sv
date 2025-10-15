timeunit 1ns; timeprecision 1ps;
module regression #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT  = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC
)(
    input  logic                         clk,
    input  logic                         rst_n,

    // from accumulator
    input  logic                         valid_in,
    output logic                         ready_out,   // accept new matrix
    input  logic                         ready_in,    // downstream ready for beta

    input  logic signed [WIDTH-1:0]      mat_flat [0:11],
    output logic                         valid_out,
    output logic                         singular_err,
    output logic signed [WIDTH-1:0]      beta [0:2]
);
    // Helper abs
    function automatic logic signed [WIDTH-1:0]
        abs_val(input logic signed [WIDTH-1:0] x);
        return x[WIDTH-1] ? -x : x;
    endfunction

    // Skid buffer for 12-element matrix vector
    logic                         skid_s_ready;
    logic                         skid_m_valid;
    logic                         skid_m_ready;
    wire signed [WIDTH-1:0]      skid_s_data [0:11];
    logic signed [WIDTH-1:0]      skid_m_data [0:11];

    // Stage barrier readies
    wire stage2_barrier_ready;
    wire stage3_barrier_ready;
    wire stage5_barrier_ready;
    wire stage6_barrier_ready;
    wire stage6b_barrier_ready;
    wire stage7_barrier_ready;

    // Map array to skid
    genvar gi;
    generate
        for (gi = 0; gi < 12; ++gi) begin : MAP_IN
            assign skid_s_data[gi] = mat_flat[gi];
        end
    endgenerate

    // Fallback mean: trigger when a pivot fails
    logic mean_valid;
    logic mean_ready;
    logic signed [WIDTH-1:0] mean_payoff;

    // Stage regs
    logic v0;
    logic v1;
    logic v2;
    logic v3;
    logic v4;
    logic v5;
    logic v6;
    logic v6b;
    logic v7a;
    logic v7b1;
    logic v7b;
    logic v7c1;
    logic v7c;

    logic signed [WIDTH-1:0] mat0[0:2][0:3];
    logic signed [WIDTH-1:0] mat1[0:2][0:3];
    logic signed [WIDTH-1:0] mat2[0:2][0:3];
    logic signed [WIDTH-1:0] mat3[0:2][0:3];
    logic signed [WIDTH-1:0] mat4[0:2][0:3];
    logic signed [WIDTH-1:0] mat5[0:2][0:3];
    logic signed [WIDTH-1:0] mat6[0:2][0:3];
    logic signed [WIDTH-1:0] mat7[0:2][0:3];

    // Pivots
    logic [1:0] pivot0_row;
    logic [1:0] pivot1_row;

    // Sticky singular flag (per-solve): set on pivot failure, cleared when a new
    // solve starts or when result is committed. We ensure the pipeline only
    // accepts a new solve when either normal path can drain (barriers) or
    // fallback result (mean_valid) is ready, so clearing at v0 is safe.
    wire pivot0_is_zero;
    wire pivot1_is_zero;
    wire pivot2_is_zero;

    // Stage0 inputs latched for fallback mean
    logic signed [WIDTH-1:0] sum1_latched;
    logic signed [WIDTH-1:0] sumy_latched;

    // Skid downstream ready when pipeline can drain to completion (all barriers)
    // OR fallback result is ready (mean_valid). This prevents accepting a new
    // solve before the current result (normal or fallback) can be produced.
    logic in_flight;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) in_flight <= 1'b0;
        else if (skid_m_valid && skid_m_ready) in_flight <= 1'b1;         // accepted a solve
        else if ((v7c && !singular_err && ready_in) || (mean_valid && ready_in))
            in_flight <= 1'b0;                                             // result committed
    end
    wire all_barriers;
    assign all_barriers = stage2_barrier_ready && stage3_barrier_ready &&
                    stage5_barrier_ready && stage6_barrier_ready &&
                    stage6b_barrier_ready && stage7_barrier_ready;
    assign skid_m_ready = ready_in && ( !in_flight || all_barriers || mean_valid );

    rv_skid_arr_gate #(.N(12), .DW(WIDTH)) u_skid (
        .clk         (clk),
        .rst_n       (rst_n),
        .s_valid     (valid_in),
        .s_ready     (skid_s_ready),
        .s_data      (skid_s_data),
        .gate_accept (1'b1),
        .m_valid     (skid_m_valid),
        .m_ready     (skid_m_ready),
        .m_data      (skid_m_data)
    );
    assign ready_out = skid_s_ready;

    // Stage 0
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v0           <= 1'b0;
        end else begin
            v0 <= skid_m_valid && skid_m_ready;

            if (skid_m_valid && skid_m_ready) begin
                for (int i = 0; i < 3; i++) begin
                    mat0[i][0] <= skid_m_data[i*4+0];
                    mat0[i][1] <= skid_m_data[i*4+1];
                    mat0[i][2] <= skid_m_data[i*4+2];
                    mat0[i][3] <= skid_m_data[i*4+3];
                end
                sum1_latched <= skid_m_data[0];
                sumy_latched <= skid_m_data[3];
            end
        end
    end

    // Stage‑1 : pivot row 0
    always_comb begin
        pivot0_row = 2'd0;
        if (abs_val(mat0[1][0]) > abs_val(mat0[0][0])) pivot0_row = 2'd1;
        if (abs_val(mat0[2][0]) > abs_val(mat0[pivot0_row][0])) pivot0_row = 2'd2;
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v1 <= 1'b0;
        else begin
            v1          <= v0;
            mat1[0][0]  <= mat0[pivot0_row][0];
            mat1[0][1]  <= mat0[pivot0_row][1];
            mat1[0][2]  <= mat0[pivot0_row][2];
            mat1[0][3]  <= mat0[pivot0_row][3];
            mat1[1][0]  <= (2'd1 == pivot0_row) ? mat0[0][0] : mat0[1][0];
            mat1[1][1]  <= (2'd1 == pivot0_row) ? mat0[0][1] : mat0[1][1];
            mat1[1][2]  <= (2'd1 == pivot0_row) ? mat0[0][2] : mat0[1][2];
            mat1[1][3]  <= (2'd1 == pivot0_row) ? mat0[0][3] : mat0[1][3];
            mat1[2][0]  <= (2'd2 == pivot0_row) ? mat0[0][0] : mat0[2][0];
            mat1[2][1]  <= (2'd2 == pivot0_row) ? mat0[0][1] : mat0[2][1];
            mat1[2][2]  <= (2'd2 == pivot0_row) ? mat0[0][2] : mat0[2][2];
            mat1[2][3]  <= (2'd2 == pivot0_row) ? mat0[0][3] : mat0[2][3];
        end
    end

    // Stage 2 : normalize row‑0 (4 div)
    logic signed [WIDTH-1:0] div0_num[0:3];
    logic signed [WIDTH-1:0] div0_den[0:3];
    logic signed [WIDTH-1:0] div0_res[0:3];
    logic [3:0]              div0_done;
    logic                    div0_ready[0:3];  // 1-bit per divider

    assign pivot0_is_zero       = v1 && (mat1[0][0] == '0);
    assign stage2_barrier_ready = div0_ready[0] && div0_ready[1] &&
                                  div0_ready[2] && div0_ready[3];

    generate
        for (genvar g = 0; g < 4; ++g) begin : DIV0
            logic signed [2*WIDTH-1:0] num64_ext0;
            assign num64_ext0 = $signed({{WIDTH{mat1[0][g][WIDTH-1]}}, mat1[0][g]})
                                <<< QFRAC;
            assign div0_num[g] = num64_ext0[WIDTH+QFRAC-1 : QFRAC];
            assign div0_den[g] = mat1[0][0];
            fxDiv #() d0 (
                .clk        (clk),
                .rst_n      (rst_n),
                .valid_in   (v1 && !pivot0_is_zero),
                .ready_out  (div0_ready[g]),
                .ready_in   (stage3_barrier_ready),
                .valid_out  (div0_done[g]),
                .numerator  (div0_num[g]),
                .denominator(div0_den[g]),
                .result     (div0_res[g])
            );
        end
    endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v2 <= 1'b0;
        else begin
            v2          <= (&div0_done) && !pivot0_is_zero;
            mat2[0][0]  <= div0_res[0];
            mat2[0][1]  <= div0_res[1];
            mat2[0][2]  <= div0_res[2];
            mat2[0][3]  <= div0_res[3];
            mat2[1][0]  <= mat1[1][0];
            mat2[1][1]  <= mat1[1][1];
            mat2[1][2]  <= mat1[1][2];
            mat2[1][3]  <= mat1[1][3];
            mat2[2][0]  <= mat1[2][0];
            mat2[2][1]  <= mat1[2][1];
            mat2[2][2]  <= mat1[2][2];
            mat2[2][3]  <= mat1[2][3];
        end
    end

    // Stage 3 : eliminate col‑0 (8 mul)
    logic signed [WIDTH-1:0] mul0_r0[0:3];
    logic signed [WIDTH-1:0] mul0_r1[0:3];
    logic [3:0]              mul0_done_r0;
    logic [3:0]              mul0_done_r1;
    logic [3:0]              mul0_ready_r0;
    logic [3:0]              mul0_ready_r1;

    assign stage3_barrier_ready = (&mul0_ready_r0) && (&mul0_ready_r1);

    generate
        for (genvar c = 0; c < 4; c++) begin : MUL0
            fxMul #() m0 (
                .clk       (clk),
                .rst_n     (rst_n),
                .valid_in  (v2),
                .ready_out (mul0_ready_r0[c]),
                .ready_in  (stage5_barrier_ready),
                .valid_out (mul0_done_r0[c]),
                .a         (mat2[1][0]),
                .b         (mat2[0][c]),
                .result    (mul0_r0[c])
            );
            fxMul #() m1 (
                .clk       (clk),
                .rst_n     (rst_n),
                .valid_in  (v2),
                .ready_out (mul0_ready_r1[c]),
                .ready_in  (stage5_barrier_ready),
                .valid_out (mul0_done_r1[c]),
                .a         (mat2[2][0]),
                .b         (mat2[0][c]),
                .result    (mul0_r1[c])
            );
        end
    endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v3 <= 1'b0;
        else begin
            v3 <= (&mul0_done_r0) && (&mul0_done_r1);
            for (int j = 0; j < 4; ++j) begin
                mat3[0][j] <= mat2[0][j];
                mat3[1][j] <= mat2[1][j] - mul0_r0[j];
                mat3[2][j] <= mat2[2][j] - mul0_r1[j];
            end
        end
    end

    // Stage‑4 : pivot row‑1
    always_comb begin
        pivot1_row = 2'd1;
        if (abs_val(mat3[2][1]) > abs_val(mat3[1][1])) pivot1_row = 2'd2;
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v4 <= 1'b0;
        else begin
            v4          <= v3;
            mat4[0][0]  <= mat3[0][0];
            mat4[0][1]  <= mat3[0][1];
            mat4[0][2]  <= mat3[0][2];
            mat4[0][3]  <= mat3[0][3];
            mat4[1][0]  <= mat3[1][0];
            mat4[1][1]  <= mat3[pivot1_row][1];
            mat4[1][2]  <= mat3[pivot1_row][2];
            mat4[1][3]  <= mat3[pivot1_row][3];
            mat4[2][0]  <= mat3[2][0];
            mat4[2][1]  <= (pivot1_row == 2'd2) ? mat3[1][1] : mat3[2][1];
            mat4[2][2]  <= (pivot1_row == 2'd2) ? mat3[1][2] : mat3[2][2];
            mat4[2][3]  <= (pivot1_row == 2'd2) ? mat3[1][3] : mat3[2][3];
        end
    end

    // Stage 5 : normalize row‑1 (3 div)
    logic signed [WIDTH-1:0] div1_num[0:2];
    logic signed [WIDTH-1:0] div1_den[0:2];
    logic signed [WIDTH-1:0] div1_res[0:2];
    logic [2:0]              div1_done;
    logic [2:0]              div1_ready;

    assign pivot1_is_zero       = v4 && (mat4[1][1] == '0);
    assign stage5_barrier_ready = &div1_ready;

    generate
        for (genvar g1 = 0; g1 < 3; g1++) begin : DIV1
            logic signed [2*WIDTH-1:0] num64_ext1;
            assign num64_ext1   = $signed({{WIDTH{mat4[1][g1+1][WIDTH-1]}},
                                            mat4[1][g1+1]}) <<< QFRAC;
            assign div1_num[g1] = num64_ext1[WIDTH+QFRAC-1 : QFRAC];
            assign div1_den[g1] = mat4[1][1];
            fxDiv #() d1 (
                .clk        (clk),
                .rst_n      (rst_n),
                .valid_in   (v4 && !pivot1_is_zero),
                .ready_out  (div1_ready[g1]),
                .ready_in   (stage6_barrier_ready),
                .valid_out  (div1_done[g1]),
                .numerator  (div1_num[g1]),
                .denominator(div1_den[g1]),
                .result     (div1_res[g1])
            );
        end
    endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v5 <= 1'b0;
        else begin
            v5          <= (&div1_done) && !pivot1_is_zero;
            mat5[0][0]  <= mat4[0][0];
            mat5[0][1]  <= mat4[0][1];
            mat5[0][2]  <= mat4[0][2];
            mat5[0][3]  <= mat4[0][3];
            mat5[1][0]  <= mat4[1][0];
            mat5[1][1]  <= div1_res[0];
            mat5[1][2]  <= div1_res[1];
            mat5[1][3]  <= div1_res[2];
            mat5[2][0]  <= mat4[2][0];
            mat5[2][1]  <= mat4[2][1];
            mat5[2][2]  <= mat4[2][2];
            mat5[2][3]  <= mat4[2][3];
        end
    end

    // Stage‑6 : eliminate col‑1 in row‑2
    logic signed [WIDTH-1:0] mul_elim_res[3];
    logic [2:0]              mul_elim_valid;
    logic [2:0]              mul_elim_ready;

    assign stage6_barrier_ready = &mul_elim_ready;

    generate
        for (genvar j = 1; j < 4; j++) begin : ELIM_MUL
            logic signed [WIDTH-1:0] mul_res;
            fxMul #() mul_elim (
                .clk       (clk),
                .rst_n     (rst_n),
                .valid_in  (v5),
                .ready_out (mul_elim_ready[j-1]),
                .ready_in  (stage6b_barrier_ready),
                .valid_out (mul_elim_valid[j-1]),
                .a         (mat5[2][1]),
                .b         (mat5[1][j]),
                .result    (mul_res)
            );
            assign mul_elim_res[j-1] = mul_res;
        end
    endgenerate

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) v6 <= 1'b0;
        else begin
            v6 <= v5 && (&mul_elim_valid);
            for (int j2 = 0; j2 < 4; ++j2) begin
                mat6[0][j2] <= mat5[0][j2];
                mat6[1][j2] <= mat5[1][j2];
            end
            mat6[2][0] <= mat5[2][0];
            for (int j3 = 1; j3 < 4; ++j3) begin
                mat6[2][j3] <= mat5[2][j3] - mul_elim_res[j3-1];
            end
        end
    end

    // Stage-6B : normalize row‑2
    logic signed [WIDTH-1:0] div2_num[0:2];
    logic signed [WIDTH-1:0] div2_res[0:2];
    logic signed [WIDTH-1:0] div2_den;
    logic [2:0]              div2_done;
    logic [2:0]              div2_ready;

    assign div2_den = mat6[2][2];
    assign stage6b_barrier_ready = &div2_ready;

    generate
        for (genvar g2 = 0; g2 < 3; ++g2) begin : DIV2
            logic signed [2*WIDTH-1:0] num64_ext2;
            assign num64_ext2 = $signed({{WIDTH{mat6[2][g2+1][WIDTH-1]}}, mat6[2][g2+1]}) <<< QFRAC;
            assign div2_num[g2] = num64_ext2[WIDTH+QFRAC-1 : QFRAC];

            fxDiv #() d2 (
                .clk        (clk),
                .rst_n      (rst_n),
                .valid_in   (v6),
                .ready_out  (div2_ready[g2]),
                .ready_in   (stage7_barrier_ready),
                .valid_out  (div2_done[g2]),
                .numerator  (div2_num[g2]),
                .denominator(div2_den),
                .result     (div2_res[g2])
            );
        end
    endgenerate


    // Stage‑7 : back‑substitution
    logic signed [WIDTH-1:0] bt2;
    logic signed [WIDTH-1:0] bt1;
    logic signed [WIDTH-1:0] bt0;
    logic                     div_b2_ready;
    logic                     mul12_ready;
    logic                     div_b1_ready;
    logic                     mul01_ready;
    logic                     mul02_ready;
    logic                     div_b0_ready;

    assign pivot2_is_zero = v6b && (mat7[2][2] == '0);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            singular_err <= 1'b0;
        end else if (skid_m_valid && skid_m_ready) begin
            // new solve starts
            singular_err <= 1'b0;
        end else if ((v1 && pivot0_is_zero) ||
                    (v4 && pivot1_is_zero) ||
                     (v6b && pivot2_is_zero)) begin
            singular_err <= 1'b1;
        end else if ((v7c && !singular_err && ready_in) ||
                     (mean_valid && ready_in)) begin
            // result committed (normal or fallback)
            singular_err <= 1'b0;
        end
    end

    integer j4;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v6b <= 1'b0;
            for (j4 = 0; j4 < 4; ++j4) begin
                mat7[0][j4] <= '0;
                mat7[1][j4] <= '0;
            end
            mat7[2][0] <= '0;
            mat7[2][1] <= '0;
            mat7[2][2] <= '0;
            mat7[2][3] <= '0;
        end else begin
            v6b <= &div2_done;
            for (j4 = 0; j4 < 4; ++j4) begin
                mat7[0][j4] <= mat6[0][j4];
                mat7[1][j4] <= mat6[1][j4];
            end
            mat7[2][0] <= mat6[2][0];
            mat7[2][1] <= div2_res[0];
            mat7[2][2] <= div2_res[1];
            mat7[2][3] <= div2_res[2];
        end
    end

    // bt2 = mat7[2][3] / mat7[2][2]
    logic signed [2*WIDTH-1:0] num64_b2;
    assign num64_b2 = $signed({{WIDTH{mat7[2][3][WIDTH-1]}}, mat7[2][3]}) <<< QFRAC;
    fxDiv #() div_b2 (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (v6b && !pivot2_is_zero),
        .ready_out  (div_b2_ready),
        .ready_in   (mul12_ready),
        .valid_out  (v7a),
        .numerator  (num64_b2[WIDTH+QFRAC-1 : QFRAC]),
        .denominator(mat7[2][2]),
        .result     (bt2)
    );

    logic signed [WIDTH-1:0] prod12;
    logic signed [WIDTH-1:0] prod01;
    logic signed [WIDTH-1:0] prod02;

    fxMul #() mul12 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v7a),
        .ready_out (mul12_ready),
        .ready_in  (div_b1_ready),
        .valid_out (v7b1),
        .a         (mat7[1][2]),
        .b         (bt2),
        .result    (prod12)
    );

    // bt1 = (mat7[1][3] - mat7[1][2]*bt2) / mat7[1][1]
    logic signed [WIDTH-1:0] rhs1;
    logic signed [2*WIDTH-1:0] num64_b1;
    assign rhs1      = $signed(mat7[1][3]) - prod12;
    assign num64_b1  = $signed({{WIDTH{rhs1[WIDTH-1]}}, rhs1}) <<< QFRAC;

    fxDiv #() div_b1 (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (v7b1),
        .ready_out  (div_b1_ready),
        .ready_in   (mul01_ready),
        .valid_out  (v7b),
        .numerator  (num64_b1[WIDTH+QFRAC-1 : QFRAC]),
        .denominator(mat7[1][1]),
        .result     (bt1)
    );

    fxMul #() mul01 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v7b),
        .ready_out (mul01_ready),
        .ready_in  (mul02_ready),
        .valid_out (v7c1),
        .a         (mat7[0][1]),
        .b         (bt1),
        .result    (prod01)
    );

    fxMul #() mul02 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v7c1),
        .ready_out (mul02_ready),
        .ready_in  (div_b0_ready),
        .valid_out (/*unused*/),
        .a         (mat7[0][2]),
        .b         (bt2),
        .result    (prod02)
    );

    // bt0 = (mat7[0][3] - mat7[0][1]*bt1 - mat7[0][2]*bt2) / mat7[0][0]
    logic signed [WIDTH-1:0] rhs0;
    logic signed [2*WIDTH-1:0] num64_b0;
    assign rhs0 = $signed(mat7[0][3]) - prod01;
    assign num64_b0  = $signed({{WIDTH{rhs0[WIDTH-1]}}, rhs0}) <<< QFRAC;

    fxDiv #() div_b0 (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (v7c1),
        .ready_out  (div_b0_ready),
        .ready_in   (ready_in),
        .valid_out  (v7c),
        .numerator  (num64_b0[WIDTH+QFRAC-1 : QFRAC]),
        .denominator(mat7[0][0]),
        .result     (bt0)
    );

    assign stage7_barrier_ready = div_b2_ready && mul12_ready && div_b1_ready && mul01_ready && mul02_ready && div_b0_ready;

    // Fallback mean: trigger when a pivot fails
    wire fallback_req;
    logic signed [2*WIDTH-1:0] num64_mean;

    assign fallback_req = (v1  && pivot0_is_zero) ||
                          (v4  && pivot1_is_zero) ||
                          (v6b && pivot2_is_zero);

    assign num64_mean = $signed({{WIDTH{sumy_latched[WIDTH-1]}}, sumy_latched}) <<< QFRAC;

    fxDiv #() div_mean (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (fallback_req),
        .ready_out  (mean_ready),
        .ready_in   (1'b1),
        .valid_out  (mean_valid),
        .numerator  (num64_mean[WIDTH+QFRAC-1 : QFRAC]),
        .denominator(sum1_latched),
        .result     (mean_payoff)
    );

    // Output
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_out <= 1'b0;
            beta[0]   <= '0;
            beta[1]   <= '0;
            beta[2]   <= '0;
        end else begin
            valid_out <= 1'b0;
            // normal path
            if (v7c && !singular_err && ready_in) begin
                beta[2]   <= bt2;
                beta[1]   <= bt1;
                beta[0]   <= bt0;
                valid_out <= 1'b1;
            end
            // fallback path
            else if (mean_valid && ready_in) begin
                beta[2]   <= '0;
                beta[1]   <= '0;
                beta[0]   <= mean_payoff;
                valid_out <= 1'b1;
            end
        end
    end

    // Assertions
    // capture previous samples
    logic signed [WIDTH-1:0] skid_m_data_q [0:11];
    logic signed [WIDTH-1:0] beta_q        [0:2];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0;i<12;i++) skid_m_data_q[i] <= '0;
            for (int j=0;j<3;j++)  beta_q[j]        <= '0;
        end else begin
            // update refs only when not stalling
            if (!(skid_m_valid && !skid_m_ready))
            for (int i=0;i<12;i++) skid_m_data_q[i] <= skid_m_data[i];
            if (!(valid_out && !ready_in))
            for (int j=0;j<3;j++)  beta_q[j]        <= beta[j];
        end
    end

    // sustained stall -> must match previous sample
    logic skid_bp, skid_bp_prev, out_bp, out_bp_prev;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skid_bp_prev <= 1'b0; skid_bp <= 1'b0;
            out_bp_prev  <= 1'b0; out_bp  <= 1'b0;
        end else begin
            skid_bp_prev <= skid_bp;
            skid_bp      <= skid_m_valid && !skid_m_ready;
            if (skid_bp_prev && skid_bp)
            for (int i=0;i<12;i++) assert (skid_m_data[i] == skid_m_data_q[i])
                else $error("Regression: skid output changed under backpressure");

            out_bp_prev  <= out_bp;
            out_bp       <= valid_out && !ready_in;
            if (out_bp_prev && out_bp)
            for (int j=0;j<3;j++)  assert (beta[j] == beta_q[j])
                else $error("Regression: output stall overwrite");
        end
    end


    // Implement the sticky check with a one-cycle flag
    logic singular_sticky_prev;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            singular_sticky_prev <= 1'b0;
        end else begin
            singular_sticky_prev <= singular_err && !(skid_m_valid && skid_m_ready);
            if (singular_sticky_prev)
            assert (singular_err)
                else $error("Regression: singular_err not sticky within solve");
        end
    end

    // Stage2 desync guard: when accepting barrier+v2, mat2 must not change vs previous sample
    logic signed [WIDTH-1:0] mat2_q [0:2][0:3];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int r=0;r<3;r++) for (int c=0;c<4;c++) mat2_q[r][c] <= '0;
        end else if (!(v2 && stage2_barrier_ready)) begin
            for (int r=0;r<3;r++) for (int c=0;c<4;c++) mat2_q[r][c] <= mat2[r][c];
        end
    end

    logic hold_s2_prev, hold_s2;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            hold_s2_prev <= 1'b0; hold_s2 <= 1'b0;
        end else begin
            hold_s2_prev <= hold_s2;
            hold_s2      <= v2 && stage2_barrier_ready;
            if (hold_s2_prev && hold_s2)
            for (int r=0;r<3;r++) for (int c=0;c<4;c++)
                assert (mat2[r][c] == mat2_q[r][c])
                else $error("Regression: stage2 desync on stall");
        end
    end

endmodule
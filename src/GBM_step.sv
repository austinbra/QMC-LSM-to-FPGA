module GBM_step #(
    parameter int WIDTH              = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT               = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC              = fpga_cfg_pkg::FP_QFRAC,
    parameter int MUL_LATENCY_ALWAYS = fpga_cfg_pkg::FP_MUL_ALWAYS_LATENCY,
    parameter int DIV_LATENCY        = fpga_cfg_pkg::FP_DIV_LATENCY,
    parameter int SQRT_LATENCY       = fpga_cfg_pkg::FP_SQRT_LATENCY,
    parameter int LUT_BITS           = fpga_cfg_pkg::FP_LUT_BITS
)(
    input  logic                       clk,
    input  logic                       rst_n,
    input  logic                       valid_in,
    input  logic signed [WIDTH-1:0]    z,
    input  logic signed [WIDTH-1:0]    S_0,
    input  logic signed [WIDTH-1:0]    r,
    input  logic signed [WIDTH-1:0]    sigma,
    input  logic signed [WIDTH-1:0]    t,
    output logic                       valid_out,
    output logic signed [WIDTH-1:0]    S_1
);
    import fpga_cfg_pkg::*;

    localparam signed [WIDTH-1:0] HALF_Q16 = 32'sd32768;
    localparam signed [WIDTH-1:0] ONE_Q16  = 32'sh0001_0000;

    // ---------------------------
    // 1. DRIFT = (r-0.5σ²)·t
    // ---------------------------
    logic v1a, v1b, v2;
    logic signed [WIDTH-1:0] sigma2, half_sigma2, drift;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_sigma2 (
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(sigma), .b(sigma), .valid_out(v1a), .result(sigma2)
    );
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_half (
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(sigma2), .b(HALF_Q16), .valid_out(v1b), .result(half_sigma2)
    );
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_drift (
        .clk(clk), .rst_n(rst_n), .valid_in(v1b), .a(r - half_sigma2), .b(t), .valid_out(v2), .result(drift)
    );

    logic drift_ready;
    logic signed [WIDTH-1:0] drift_hold;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            drift_ready <= 1'b0;
            drift_hold  <= '0;
        end else begin
            // latch drift when complete
            if (v2) begin
                drift_hold  <= drift;
                drift_ready <= 1'b1;
            end
            // clear when used with diffusion
            if (drift_ready && diffusion_done_pulse)
                drift_ready <= 1'b0;
        end
    end

    // ---------------------------
    // 2. DIFFUSION = σ√t·Z
    // ---------------------------
    logic v3a, v3b, v3c;
    logic signed [WIDTH-1:0] sqrt_t, sigma_sqrt_t, diffusion;
    fxSqrt #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(DIV_LATENCY)) sqrt_blk (
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(t), .valid_out(v3a), .sqrt_out(sqrt_t)
    );
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_sigma_sqrt (
        .clk(clk), .rst_n(rst_n), .valid_in(v3a), .a(sqrt_t), .b(sigma), .valid_out(v3b), .result(sigma_sqrt_t)
    );
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_diffusion (
        .clk(clk), .rst_n(rst_n), .valid_in(v3b), .a(sigma_sqrt_t), .b(z), .valid_out(v3c), .result(diffusion)
    );

    logic diffusion_done_pulse;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            diffusion_done_pulse <= 1'b0;
        else
            diffusion_done_pulse <= v3c;
    end

    // ---------------------------
    // 3. EXPONENT ARGUMENT
    // ---------------------------
    logic signed [WIDTH-1:0] exp_arg;
    logic v_exp_arg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            exp_arg  <= '0;
            v_exp_arg <= 1'b0;
        end else begin
            v_exp_arg <= diffusion_done_pulse && drift_ready;
            if (diffusion_done_pulse && drift_ready)
                exp_arg <= diffusion + drift_hold;
        end
    end

    // ---------------------------
    // 4. EXP CALCULATION
    // ---------------------------
    logic signed [WIDTH-1:0] exp_mag;
    logic exp_neg_pipe[0:DIV_LATENCY];
    integer j;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (j = 0; j <= DIV_LATENCY; j++)
                exp_neg_pipe[j] <= 1'b0;
            exp_mag <= '0;
        end else begin
            if (v_exp_arg) begin
                exp_neg_pipe[0] <= exp_arg[WIDTH-1];
                exp_mag <= exp_arg[WIDTH-1] ? -exp_arg : exp_arg;
            end
            for (j = 1; j <= DIV_LATENCY; j++)
                exp_neg_pipe[j] <= exp_neg_pipe[j-1];
        end
    end

    logic v_exp_abs;
    logic signed [WIDTH-1:0] exp_abs;
    fxExpLUT #(.WIDTH(WIDTH), .QINT(QINT), .LUT_BITS(LUT_BITS)) exp_lut (//main exp
        .clk(clk), .rst_n(rst_n), .valid_in(v_exp_arg), .a(exp_mag), .valid_out(v_exp_abs), .result(exp_abs)
    );

    logic v_recip;
    logic signed [WIDTH-1:0] exp_recip;
    fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(DIV_LATENCY)) recip_div (//only when exp is negative
        .clk(clk), .rst_n(rst_n), .valid_in(v_exp_abs && exp_neg_pipe[0]), .numerator(ONE_Q16), .denominator(exp_abs), .valid_out(v_recip), .result(exp_recip)
    );

    logic v_pos_pipe[0:DIV_LATENCY-1];
    logic signed [WIDTH-1:0] exp_abs_pipe[0:DIV_LATENCY-1];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (j = 0; j < DIV_LATENCY; j++) begin
                v_pos_pipe[j] <= 1'b0;
                exp_abs_pipe[j] <= '0;
            end
        end else begin
            v_pos_pipe[0] <= v_exp_abs && ~exp_neg_pipe[0];
            exp_abs_pipe[0] <= exp_abs;
            for (j = 1; j < DIV_LATENCY; j++) begin
                v_pos_pipe[j] <= v_pos_pipe[j-1];
                exp_abs_pipe[j] <= exp_abs_pipe[j-1];
            end
        end
    end

    logic v_exp_final;
    logic signed [WIDTH-1:0] exp_final;
    assign v_exp_final = exp_neg_pipe[DIV_LATENCY] ? v_recip : v_pos_pipe[DIV_LATENCY-1];
    assign exp_final   = exp_neg_pipe[DIV_LATENCY] ? exp_recip : exp_abs_pipe[DIV_LATENCY-1];

    //---------------------------
    // 5. OUTPUT PRICE S1
    // ---------------------------
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_out (
        .clk(clk), .rst_n(rst_n), .valid_in(v_exp_final), .a(exp_final), .b(S_0), .valid_out(valid_out), .result(S_1)
    );

endmodule
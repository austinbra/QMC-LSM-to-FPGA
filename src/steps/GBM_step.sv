module GBM_step #(
    parameter int WIDTH       = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT        = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC       = fpga_cfg_pkg::FP_QFRAC,
    parameter int DIV_LATENCY = fpga_cfg_pkg::FP_DIV_LATENCY
)(
    input  logic                       clk,
    input  logic                       rst_n,

    // upstream handshake ----------------------------------------------------
    input  logic                       valid_in,
    output logic                       ready_out,

    // downstream handshake --------------------------------------------------
    output logic                       valid_out,
    input  logic                       ready_in,

    // data ------------------------------------------------------------------
    input  logic signed [WIDTH-1:0]    z,
    input  logic signed [WIDTH-1:0]    S,
    input  logic signed [WIDTH-1:0]    r,
    input  logic signed [WIDTH-1:0]    sigma,
    input  logic signed [WIDTH-1:0]    dt,
    output logic signed [WIDTH-1:0]    S_next
);

    // ----------------------------------------------------------------------
    // 0. One-deep skid buffer to absorb upstream bursts
    // ----------------------------------------------------------------------
    typedef struct packed {
        logic signed [WIDTH-1:0] z;
        logic signed [WIDTH-1:0] S;
        logic signed [WIDTH-1:0] r;
        logic signed [WIDTH-1:0] sigma;
        logic signed [WIDTH-1:0] dt;
    } sample_t;

    sample_t in_buf;
    logic    buf_valid;

    // ready when buffer empty and internal pipe ready
    wire pipe_ready = ready_in;
    assign ready_out = ~buf_valid | pipe_ready;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 1'b0;
        end else begin
            // Load new sample when upstream is valid and we have space
            if (valid_in && ready_out) begin
                in_buf    <= '{z,S,r,sigma,dt};
                buf_valid <= 1'b1;
            end
            // Drop buffer flag when sample finishes entire path
            if (buf_valid && pipe_ready && valid_out) begin
                buf_valid <= 1'b0;
            end
        end
    end

    // ----------------------------------------------------------------------
    // 1. DRIFT branch :  (r – 0.5 σ²) * dt
    // ----------------------------------------------------------------------
    logic drift_v_in  = buf_valid;
    logic drift_r_in;
    logic drift_v_out;
    logic signed [WIDTH-1:0] sigma2, half_sigma2, drift;

    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT)) mul_sigma2 (
        .clk(clk), .rst_n(rst_n),
        .valid_in (drift_v_in),     .ready_in (drift_r_in),
        .valid_out(drift_v_out),    .ready_out(/*unused*/),
        .a(in_buf.sigma), .b(in_buf.sigma),
        .result(sigma2)
    );

    assign half_sigma2 = sigma2 >>> 1;   // multiply by 0.5 via shift

    logic drift2_v, drift2_r;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT)) mul_drift (
        .clk(clk), .rst_n(rst_n),
        .valid_in (drift_v_out), .ready_in(drift2_r),
        .valid_out(drift2_v),    .ready_out(/*unused*/),
        .a(in_buf.r - half_sigma2), .b(in_buf.dt),
        .result(drift)
    );

    // ----------------------------------------------------------------------
    // 2. DIFFUSION branch : σ √dt · z
    // ----------------------------------------------------------------------
    logic diff_v_in = buf_valid;
    logic diff_r_in;
    logic diff_v_out;
    logic signed [WIDTH-1:0] sqrt_dt, sigma_sqrt_dt, diffusion;

    fxSqrt #(.WIDTH(WIDTH), .QINT(QINT)) sqrt_blk (
        .clk(clk), .rst_n(rst_n),
        .valid_in (diff_v_in),  .ready_in(diff_r_in),
        .valid_out(diff_v_out), .ready_out(/*unused*/),
        .y(in_buf.dt),
        .sqrt_out(sqrt_dt)
    );

    logic diff2_v, diff2_r;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT)) mul_sigma_sqrt (
        .clk(clk), .rst_n(rst_n),
        .valid_in (diff_v_out), .ready_in(diff2_r),
        .valid_out(diff2_v),    .ready_out(/*unused*/),
        .a(sqrt_dt), .b(in_buf.sigma),
        .result(sigma_sqrt_dt)
    );

    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT)) mul_diffusion (
        .clk(clk), .rst_n(rst_n),
        .valid_in (diff2_v), .ready_in(1'b1),   // terminal branch
        .valid_out(diffusion_v), .ready_out(/*open*/),
        .a(sigma_sqrt_dt), .b(in_buf.z),
        .result(diffusion)
    );

    // ----------------------------------------------------------------------
    // 3. Join drift + diffusion  (requires both branches ready)
    // ----------------------------------------------------------------------
    logic join_valid = drift2_v & diffusion_v;
    logic join_ready = pipe_ready;             // back-pressure from stage 4

    // No additional buffering: both sub-branches stay asserted until accepted
    assign drift2_r     = join_ready & diffusion_v;
    assign diff2_r      = join_ready & drift2_v;
    assign drift_r_in   = 1'b1;                // early stages never stall
    assign diff_r_in    = 1'b1;

    logic signed [WIDTH-1:0] exp_arg;
    always_ff @(posedge clk) begin
        if (join_valid & join_ready)
            exp_arg <= drift + diffusion;
    end

    // ----------------------------------------------------------------------
    // 4.  e^(exp_arg)  (CORDIC-lite LUT) and reciprocal for negative arg
    // ----------------------------------------------------------------------
    logic signed [WIDTH-1:0] abs_arg;
    logic sign_bit;

    assign sign_bit = exp_arg[WIDTH-1];
    assign abs_arg  = sign_bit ? -exp_arg : exp_arg;

    logic exp_v, exp_r, recip_v;
    logic signed [WIDTH-1:0] e_pos, e_neg;

    fxExpLUT #(.WIDTH(WIDTH), .QINT(QINT)) explut (
        .clk(clk), .rst_n(rst_n),
        .valid_in (join_valid), .ready_in(exp_r),
        .valid_out(exp_v),      .ready_out(/*unused*/),
        .a(abs_arg),
        .result(e_pos)
    );

    fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(DIV_LATENCY)) recip (
        .clk(clk), .rst_n(rst_n),
        .valid_in (exp_v),   .ready_in(1'b1),
        .valid_out(recip_v), .ready_out(exp_r),
        .numerator({1'b0, {QFRAC{1'b1}}}),  // 1.0 in Q format
        .denominator(e_pos),
        .result(e_neg)
    );

    wire signed [WIDTH-1:0] e_final = sign_bit ? e_neg : e_pos;

    // ----------------------------------------------------------------------
    // 5.  Final price  S_next = S · e^(drift+diff)
    // ----------------------------------------------------------------------
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT)) mul_price (
        .clk(clk), .rst_n(rst_n),
        .valid_in (recip_v),  .ready_in(pipe_ready),
        .valid_out(valid_out), .ready_out(/*unused*/),
        .a(e_final), .b(in_buf.S),
        .result(S_next)
    );

endmodule

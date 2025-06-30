
module inverseCDF #(
    parameter int WIDTH              = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT               = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC              = fpga_cfg_pkg::FP_QFRAC
)(
    input logic clk,
    input logic rst_n,         
    input logic valid_in,
    input logic signed [WIDTH-1:0] u_in,        // Q11.21 input in [0,1) sobol sequence numbers
    output logic valid_out,
    output logic signed [WIDTH-1:0] z_out       // Q11.21 output z-score
);

    localparam signed [WIDTH-1:0] TWO = 'sd2;   // +2.0
    localparam int STEP1_LATENCY = 1;
    localparam int LN_LUT_LATENCY = 1;


    // Step 1: Convert sobol sequence number to x ∈ (0,0.5]
    logic [WIDTH-1:0] x;
    logic negate;
    logic v1;

    inverseCDF_step1 #() step1 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .u(u_in),
        .valid_out(v1),
        .x(x),
        .negate(negate)
    );

    // Step 2: Compute ln(x) using LUT and find sqrt(y) = sqrt(-2 * ln(x))
    logic [WIDTH-1:0] ln_x;
    logic v2a;

    fxlnLUT #() loglut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v1),
        .x(x),
        .valid_out(v2a),
        .ln_out(ln_x)
    );

    logic [WIDTH-1:0] neg2_ln_x;
    logic v2b;

    fxMul #() mul_neg2(
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(v2a),
        .a(ln_x),
		.b($signed(-(TWO << QINT))),
		.result(neg2_ln_x),
		.valid_out(v2b));   

    logic [WIDTH-1:0] t;
    logic v3;

    fxSqrt #() sqrt_unit (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2b),
        .a(neg2_ln_x),
        .valid_out(v3),
        .sqrt_out(t)
    );

    // Delay negate signal to align with t 
    localparam int NEG_DELAY = STEP1_LATENCY + LN_LUT_LATENCY + MUL_LATENCY + SQRT_LATENCY;
    /* verilator lint_off UNUSED */
    logic [NEG_DELAY-1:0] negate_pipe;  // 10 stages to align with when fxInvCDF_ZS needs it
    /* verilator lint_on UNUSED */

    always_ff @(posedge clk) begin
        if (!rst_n)
            negate_pipe <= '0;
        else
            negate_pipe <= {negate_pipe[NEG_DELAY-2:0], negate};
    end

    // Step 3: Rational approximation (Zelen & Severo)
    logic signed [WIDTH-1:0] z;
    logic v4;

    fxInvCDF_ZS #(WIDTH, QINT) rational (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v3),
        .t(t),
        .negate(negate_pipe[NEG_DELAY-1]),
        .valid_out(v4),
        .z(z));

    assign z_out = z;
    assign valid_out = v4;

endmodule

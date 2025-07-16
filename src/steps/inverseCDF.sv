
module inverseCDF #(
    parameter int WIDTH              = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT               = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC              = fpga_cfg_pkg::FP_QFRAC,
    parameter int SQRT_LATENCY       = fpga_cfg_pkg::FP_SQRT_LATENCY,
    parameter int MUL_LATENCY        = fpga_cfg_pkg::FP_MUL_LATENCY

)(
    input logic clk,
    input logic rst_n,

    input logic valid_in,
    output logic ready_out,

    input logic signed [WIDTH-1:0] u_in,        // input in [0,1) sobol sequence numbers

    output logic valid_out,
    input logic ready_in,

    output logic signed [WIDTH-1:0] z_out       //  output z-score
);

    localparam signed [WIDTH-1:0] NEG_TWO = -((1'sd2) << QFRAC);
    localparam int STEP1_LATENCY = 1;
    localparam int LN_LATENCY = 2;
    localparam int NEG_DELAY = STEP1_LATENCY + LN_LATENCY + MUL_LATENCY + SQRT_LATENCY;


    // Step 1: Convert sobol sequence number to (0,0.5] saving 
    logic [WIDTH-1:0] x;
    logic negate;
    logic v1, r1;

    inverseCDF_step1 #() step1 (    //save above or below .5 by whther to negate
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .ready_in(r1),
        .u(u_in),       //prob
        .valid_out(v1),
        .ready_out(ready_out),
        .x(x),
        .negate(negate)
    );

    // Step 2: find sqrt(y) = sqrt(-2 * ln(x))
    logic [WIDTH-1:0] ln_x;
    logic r2a, v2a;

    fxlnLUT #() loglut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v1),
        .ready_in(r2a),
        .x(x),
        .valid_out(v2a),
        .ready_out(r1),   // connect ready from next stage
        .ln_out(ln_x)
    );

    logic [WIDTH-1:0] neg2_ln_x;
    logic v2b, r2b;

    fxMul_always #() mul_neg2(
        .clk(clk), 
        .rst_n(rst_n),
        .valid_in(v2a),  
        .ready_in(r2b),
        .a(ln_x), 
        .b(NEG_TWO),
        .result(neg2_ln_x),
        .valid_out(v2b), 
        .ready_out(r2a));   

    logic [WIDTH-1:0] t;
    logic v3, r3;

    fxSqrt #() sqrt_unit (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2b),
        .ready_in(r3),
        .a(neg2_ln_x),
        .valid_out(v3),
        .ready_out(r2b),
        .sqrt_out(t)
    );

    // Delay negate signal to align with t 
    logic [NEG_DELAY-1:0] negate_pipe;  // stages to align with when fxInvCDF_ZS needs it cuz constant feed in (whole thing pipelined)

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            negate_pipe <= '0;
        else if (v2b && r3)
            negate_pipe <= {negate_pipe[NEG_DELAY-2:0], negate};
    end

    // Step 3: Rational approximation (Zelen & Severo)

    fxInvCDF_ZS #(WIDTH, QINT) rational (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v3),
        .ready_in(ready_in),
        .t(t),
        .negate(negate_pipe[NEG_DELAY-1]),
        .valid_out(valid_out),
        .ready_out(r3),
        .z(z_out));


endmodule

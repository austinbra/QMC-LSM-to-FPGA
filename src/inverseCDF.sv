//-----------------------------------------------------------
// inverse cumulative distribution function for the normal distribution
//-----------------------------------------------------------
module inverseCDF #(
    parameter WIDTH = 32,
    parameter FRAC = 16         // number of fractional bits in fixed point format
)(
    input logic clk,
    input logic rst_n,          // active low reset
    input logic valid_in,
    input logic signed [WIDTH-1:0] u_in,        // Q11.21 input in [0,1) sobol sequence numbers
    output logic valid_out,
    output logic signed [WIDTH-1:0] z_out       // Q11.21 output z-score
);

// Step 1: Convert sobol sequence number to x ∈ (0,0.5]
logic [WIDTH-1:0] x;
logic negate;
logic v1;

inverseCDF_step1 #(WIDTH, FRAC) step1 (
    .clk(clk),
    .rst_n(rst_n),
    .valid_in(valid_in),
    .u(u_in),
    .x(x),
    .negate(negate),
    .valid_out(v1)
);

// Step 2: Compute ln(x) using LUT and find sqrt(y) = sqrt(-2 * ln(x))
logic [WIDTH-1:0] ln_x;
logic v2a;

fxLogLUT #(WIDTH, FRAC) loglut (
    .clk(clk),
    .rst_n(rst_n),
    .valid_in(v1),
    .x(x),
    .ln_out(ln_x),
    .valid_out(v2a)
);

logic [WIDTH-1:0] neg2_ln_x;
logic v2b;

fxMul #(WIDTH, FRAC) mul_neg2 (
    .clk(clk),
    .rst_n(rst_n),
    .a(ln_x),
    .b(-(2 << FRAC)),       // -2.0 in Q16.16
    .result(neg2_ln_x)
);

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) v2b <= 0;
    else v2b <= v2a;
end

logic [WIDTH-1:0] t;
logic v3;

fxSqrt #(WIDTH, FRAC) sqrt_unit (
    .clk(clk),
    .rst_n(rst_n),
    .valid_in(v2b),
    .y(neg2_ln_x),
    .sqrt_out(t),
    .valid_out(v3)
);

// Delay the negate signal to align with t
logic [2:0] negate_pipe;
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) negate_pipe <= 0;
    else negate_pipe <= {negate_pipe[1:0], negate};

// Step 3: Rational approximation (Zelen & Severo)
logic signed [WIDTH-1:0] z;
logic v4;

fxInvCDF_ZS #(WIDTH, FRAC) rational (
    .clk(clk),
    .rst_n(rst_n),
    .valid_in(v3),
    .t(t),
    .negate(negate),
    .z(z),
    .valid_out(v4)
);

assign z_out = z;
assign valid_out = v4;

endmodule

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

fxlnLUT #(WIDTH, FRAC) loglut (
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
    .b($signed(-(32'sd2 << FRAC))),       // -2.0 in Q16.16
    .result(neg2_ln_x)
);

// Properly delay v2a to account for multiplication pipeline (2 cycles)
logic [1:0] v2_pipe;
always_ff @(posedge clk) begin
    if (!rst_n) 
        v2_pipe <= 2'b00;
    else 
        v2_pipe <= {v2_pipe[0], v2a};
end
assign v2b = v2_pipe[1];

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

// Delay negate signal to align with t  
/* verilator lint_off UNUSED */
logic [9:0] negate_pipe;  // 10 stages to align with when fxInvCDF_ZS needs it
/* verilator lint_on UNUSED */

always_ff @(posedge clk) begin
    if (!rst_n)
        negate_pipe <= 10'b0;
    else
        negate_pipe <= {negate_pipe[8:0], negate};
end

// Step 3: Rational approximation (Zelen & Severo)
logic signed [WIDTH-1:0] z;
logic v4;

fxInvCDF_ZS #(WIDTH, FRAC) rational (
    .clk(clk),
    .rst_n(rst_n),
    .valid_in(v3),
    .t(t),
    .negate(negate_pipe[9]),  // 10 cycles of delay
    .z(z),
    .valid_out(v4)
);

assign z_out = z;
assign valid_out = v4;

endmodule

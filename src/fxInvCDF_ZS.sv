//-----------------------------------------------------------
// Approximates Z score using Zelen & Severo rational polynomial
//-----------------------------------------------------------

module fxInvCDF_ZS #(
    parameter WIDTH = 32,
    parameter FRAC = 16
)(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [WIDTH-1:0] t,          // Q16.16 input from sqrt module
    input logic negate,                 // negate flag in step 1
    output logic valid_out,
    output logic signed [WIDTH-1:0] z   // Q16.16 z-score
);

    // pre determined constants in Q16.16
    localparam  [WIDTH-1:0] C0 = 32'sd164835;   // 2.515517
    localparam [WIDTH-1:0] C1 = 32'sd52584;     // 0.802853
    localparam [WIDTH-1:0] C2 = 32'sd678;       // 0.010328

    localparam [WIDTH-1:0] D1 = 32'sd93912;   // 1.432788
    localparam [WIDTH-1:0] D2 = 32'sd12393;   // 0.189269
    localparam [WIDTH-1:0] D3 = 32'sd86;      // 0.001308

    logic [WIDTH-1:0] t2, t3;
    logic [WIDTH-1:0] num, den, ratio;
    logic [WIDTH-1:0] z_unsigned;

    // Multipliers
    fxMul #(WIDTH, FRAC) mul_t_t(.clk(clk), .rst_n(rst_n), .a(t), .b(t), .result(t2));    // t^2
    fxMul #(WIDTH, FRAC) mult_t_t2(.clk(clk), .rst_n(rst_n), .a(t), .b(t2), .result(t3));  // t^3

    // Numerator: C0 + C1 * t + C2 * t2
    logic [WIDTH-1:0] c1t, c2t2;
    fxMul #(WIDTH, FRAC) mul_c1t(.clk(clk), .rst_n(rst_n), .a(C1), .b(t), .result(c1t));
    fxMul #(WIDTH, FRAC) mul_c2t2(.clk(clk), .rst_n(rst_n), .a(C2), .b(t2), .result(c2t2));

    assign num = C0 + c1t + c2t2;

    // Denominator: 1 + D1 * t + D2 * t2 + D3 * t3
    logic [WIDTH-1:0] d1t, d2t2, d3t3;
    fxMul #(WIDTH, FRAC) mul_d1t(.clk(clk), .rst_n(rst_n), .a(D1), .b(t), .result(d1t));
    fxMul #(WIDTH, FRAC) mul_d2t2(.clk(clk), .rst_n(rst_n), .a(D2), .b(t2), .result(d2t2));
    fxMul #(WIDTH, FRAC) mul_d3t3(.clk(clk), .rst_n(rst_n), .a(D3), .b(t3), .result(d3t3));

    assign den = (1 << FRAC) + d1t + d2t2 + d3t3;   // "1" in Q16.16

    // Divide numerator by denominator
    fxDiv #(WIDTH, FRAC) div_nd (.clk(clk), .rst_n(rst_n), .num(num), .denom(den), .result(ratio));

    // final z-score: z = t - ratio
    assign z_unsigned = t - ratio;
    assign z = negate ? -$signed(z_unsigned) : $signed(z_unsigned);

    // Pipeline delay tracker
    logic [3:0] valid_pipe;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            valid_pipe <= 4'b0000;
        else
            valid_pipe <= {valid_pipe[2:0], valid_in};
    end

    assign valid_out = valid_pipe[3];   // aligned with final z output

endmodule
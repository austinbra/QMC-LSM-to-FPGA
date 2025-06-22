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
    localparam [WIDTH-1:0] C2 = 32'sd677;       // 0.010328

    localparam [WIDTH-1:0] D1 = 32'sd93912;   // 1.432788
    localparam [WIDTH-1:0] D2 = 32'sd12393;   // 0.189269
    localparam [WIDTH-1:0] D3 = 32'sd86;      // 0.001308
    localparam signed [WIDTH-1:0] ONE_Q16 = 32'sh0001_0000; // 1.0 in Q16.16


    // Multipliers
    logic [WIDTH-1:0] t2, t3;
    fxMul_always #(WIDTH, FRAC) mul_t_t(.clk(clk), .rst_n(rst_n), .a(t), .b(t), .result(mul1_out));    // t^2
    fxMul_always #(WIDTH, FRAC) mult_t_t2(.clk(clk), .rst_n(rst_n), .a(t), .b(t2), .result(mul2_out));  // t^3

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            t2  <= '0;
            t3  <= '0;
        end else begin
            t2  <= mul1_out;
            t3  <= mul2_out;
        end
    end

    // Numerator: C0 + C1 * t + C2 * t2
    logic [WIDTH-1:0] c1t, c2t2, num;
    fxMul_always #(WIDTH, FRAC) mul_c1t(.clk(clk), .rst_n(rst_n), .a(C1), .b(t), .result(c1t));
    fxMul_always #(WIDTH, FRAC) mul_c2t2(.clk(clk), .rst_n(rst_n), .a(C2), .b(t2), .result(c2t2));
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num <= 0;
        end else begin
            num <= C0 + c1t + c2t2;
        end
    end
    
    // Denominator: 1 + D1 * t + D2 * t2 + D3 * t3
    logic [WIDTH-1:0] d1t, d2t2, d3t3, den;
    fxMul_always #(WIDTH, FRAC) mul_d1t(.clk(clk), .rst_n(rst_n), .a(D1), .b(t), .result(d1t));
    fxMul_always #(WIDTH, FRAC) mul_d2t2(.clk(clk), .rst_n(rst_n), .a(D2), .b(t2), .result(d2t2));
    fxMul_always #(WIDTH, FRAC) mul_d3t3(.clk(clk), .rst_n(rst_n), .a(D3), .b(t3), .result(d3t3));
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            den <= 0;
        end else begin
            den <= ONE_Q16 + d1t + d2t2 + d3t3;
        end
    end

    // Divide numerator by denominator
    logic [WIDTH-1:0] ratio;
    fxDiv_always #(WIDTH, FRAC) div_nd (.clk(clk), .rst_n(rst_n), .numerator(num), .denominator(den), .result(ratio));
    
    logic signed [WIDTH-1:0] z_raw;
    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
        z_raw <= '0;
      else
        z_raw <= t - ratio;
    end

    // change the sign
    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
        z <= '0;
      else
        z <= negate ? -z_raw : z_raw;
    end

    // 6 stage pipeline + 1 for init
    logic [6:0] vpipe;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)     
            vpipe <= 7'b0;
        else
            vpipe <= {vpipe[5:0], valid_in};//on each clock shift left by one and bring in the current valid_in bit at the least sig bit
        valid_out <= vpipe[6]; //when 6 cycles are done this is high
    end

endmodule
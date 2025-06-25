//-----------------------------------------------------------
// Approximates Z score using Zelen & Severo rational polynomial
//-----------------------------------------------------------

module fxInvCDF_ZS #(
    parameter int WIDTH = 32,
    parameter int QINT = 16,
    parameter int QFRAC = WIDTH - QINT,
    parameter int MUL_LATENCY_ALWAYS = 1,
    parameter int DIV_LATENCY = 3
    )(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [WIDTH-1:0] t,          //  input from sqrt module
    input logic negate,                 // negate flag in step 1
    output logic valid_out,
    output logic signed [WIDTH-1:0] z   //  z-score
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
    logic v1a, v1b;       // valid_out of stage 1
    logic [WIDTH-1:0] t2, t3;   
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_t_t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(t), .b(t), .valid_out(v1a), .result(t2));    // t^2
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mult_t_t2(
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(t), .b(t2), .valid_out(v1b), .result(t3));  // t^3

    // Numerator: C0 + C1 * t + C2 * t2
    logic v2a, v2b;
    logic [WIDTH-1:0] c1t, c2t2, num;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_c1t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(C1), .b(t), .valid_out(v2a), .result(c1t));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_c2t2(
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(C2), .b(t2), .valid_out(v2b), .result(c2t2));
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num <= '0;
        end else if (v2b) begin
            num <= C0 + c1t + c2t2;
        end
    end
    
    // Denominator: 1 + D1 * t + D2 * t2 + D3 * t3
    logic v3a, v3b, v3c;
    logic [WIDTH-1:0] d1t, d2t2, d3t3, den;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_d1t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(D1), .b(t), .valid_out(v3a), .result(d1t));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_d2t2(
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(D2), .b(t2), .valid_out(v3b), .result(d2t2));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_LATENCY_ALWAYS)) mul_d3t3(
        .clk(clk), .rst_n(rst_n), .valid_in(v1b), .a(D3), .b(t3), .valid_out(v3c), .result(d3t3));
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            den <= '0;
        end else if (v3c) begin
            den <= ONE_Q16 + d1t + d2t2 + d3t3;
        end
    end

    // Divide numerator by denominator
    logic v4;
    logic [WIDTH-1:0] ratio;
    fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(DIV_LATENCY)) div_nd (
        .clk(clk), .rst_n(rst_n), .valid_in(v2b && v3c), .numerator(num), .denominator(den), .valid_out(v4), .result(ratio));
    
    // piplin the negate flag through 5 stages 
    logic [4:0] negate_pipe;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            negate_pipe <= 0;
        else
            negate_pipe <= {negate_pipe[3:0], valid_in ? negate : 1'd0};
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            z <= 0;
            valid_out <= 0;
        end else begin
            valid_out <= v4;
            if (v4)
                z <= negate_pipe[4] ? -(t - ratio) : (t - ratio);
        end
    end

endmodule
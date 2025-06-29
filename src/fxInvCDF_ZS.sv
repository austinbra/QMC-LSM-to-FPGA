//-----------------------------------------------------------
// Approximates Z score using Zelen & Severo rational polynomial
//-----------------------------------------------------------

module fxInvCDF_ZS #(
    parameter int WIDTH                 = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT                  = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC                 = fpga_cfg_pkg::FP_QFRAC,
    parameter int MUL_ALWAYS_LATENCY    = fpga_cfg_pkg::FP_MUL_ALWAYS_LATENCY,
    parameter int DIV_LATENCY           = fpga_cfg_pkg::FP_DIV_LATENCY
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
    localparam signed [WIDTH-1:0] C0 = 'sd164835;   // 2.515517
    localparam signed [WIDTH-1:0] C1 = 'sd52584;     // 0.802853
    localparam signed [WIDTH-1:0] C2 = 'sd677;       // 0.010328

    localparam signed [WIDTH-1:0] D1 = 'sd93912;   // 1.432788
    localparam signed [WIDTH-1:0] D2 = 'sd12393;   // 0.189269
    localparam signed [WIDTH-1:0] D3 = 'sd86;      // 0.001308
    localparam signed [WIDTH-1:0] ONE = 'sd65536 ; // 1.0


    // Multipliers
    logic v1a, v1b;       // valid_out of stage 1
    logic [WIDTH-1:0] t2, t3;   
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_t_t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(t), .b(t), .valid_out(v1a), .result(t2));    // t^2
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_t_t2(
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(t), .b(t2), .valid_out(v1b), .result(t3));  // t^3

    // Numerator: C0 + C1 * t + C2 * t2
    logic v2a, v2b;
    logic [WIDTH-1:0] c1t, c2t2, num;
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_c1t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(C1), .b(t), .valid_out(v2a), .result(c1t));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_c2t2(
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
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_d1t(
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in), .a(D1), .b(t), .valid_out(v3a), .result(d1t));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_d2t2(
        .clk(clk), .rst_n(rst_n), .valid_in(v1a), .a(D2), .b(t2), .valid_out(v3b), .result(d2t2));
    fxMul_always #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(MUL_ALWAYS_LATENCY)) mul_d3t3(
        .clk(clk), .rst_n(rst_n), .valid_in(v1b), .a(D3), .b(t3), .valid_out(v3c), .result(d3t3));
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            den <= '0;
        end else if (v3c) begin
            den <= ONE + d1t + d2t2 + d3t3;
        end
    end

    // Divide numerator by denominator
    logic v4;
    logic [WIDTH-1:0] ratio;
    fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .LATENCY(DIV_LATENCY)) div_nd (
        .clk(clk), 
        .rst_n(rst_n), 
        .valid_in(v3c), 
        .numerator(num), 
        .denominator(den),
        .valid_out(v4), 
        .result(ratio));
    
    // piplin the negate flag through 5 stages 
    localparam int INV_LATENCY = 3*MUL_ALWAYS_LATENCY + DIV_LATENCY;
    logic [INV_LATENCY-1:0] negate_pipe;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            negate_pipe <= '0;
        else
            negate_pipe <= {negate_pipe[INV_LATENCY-2:0], valid_in ? negate : 1'd0};
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            z <= 0;
            valid_out <= 0;
        end else begin
            valid_out <= v4;
            if (v4)
                z <= negate_pipe[INV_LATENCY-1] ? -(t - ratio) : (t - ratio);
        end
    end

endmodule
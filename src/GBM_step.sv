module GBM_step #(
    parameter WIDTH = 32,
    parameter QINT = 16,
    parameter int QFRAC = WIDTH - QINT,
    parameter LUT_BITS = 10
)(
    input logic clk,
    input logic rst_n,
    input logic signed [WIDTH-1:0] z,      //z value from inverse CDF
    input logic [WIDTH-1:0] S_0,    //init stock price
    input logic [WIDTH-1:0] r,      //rate
    input logic [WIDTH-1:0] sigma,  //volatility
    input logic [WIDTH-1:0] t,      //time step stize
    input logic valid_in,
    output logic valid_out,
    output logic [WIDTH-1:0] S_1    
);
    logic [WIDTH-1:0] step1;
    fxMul_always #(WIDTH, QINT) mul_t_t(.clk(clk), .rst_n(rst_n), .a(t), .b(t), .result(mul1_out));    // t^2


    logic [WIDTH-1:0] step2, step3;
    fxMul_always #(WIDTH, QINT) mul_t_t(.clk(clk), .rst_n(rst_n), .a(t), .b(t), .result(mul1_out));    // t^2
    fxMul_always #(WIDTH, QINT) mult_t_t2(.clk(clk), .rst_n(rst_n), .a(t), .b(t2), .result(mul2_out));  // t^3

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            t2  <= '0;
            t3  <= '0;
        end else begin
            t2  <= mul1_out;
            t3  <= mul2_out;
        end
    end
    
    
    logic signed [WIDTH-1:0] exp_result;
    fxExpLUT #(WIDTH, QINT, QFRAC, LUT_BITS) exp(
        .clk(clk),
        .rst_n(rst_n),
        .valid_in()
    )

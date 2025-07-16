module lsm_decision #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT  = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC
)(
    input  logic                     clk,
    input  logic                     rst_n,

    //per-path inputs
    input  logic                     valid_in,   // high once per path at time-t
    input  logic signed [WIDTH-1:0]  S_t,
    input  logic signed [WIDTH-1:0]  beta [0:2],
    input  logic signed [WIDTH-1:0]  strike,     // K or strike price
    input  logic signed [WIDTH-1:0]  disc,       // discount to current day = exp(-r * t)

    output logic                     valid_out,
    output logic signed [WIDTH-1:0]  PV   // chosen best value
);

    // continuation value
    //------------------------------------- 
    logic v1, v2;
    logic signed [WIDTH-1:0] S_sq, b1S, b2S2, C_val;

    fxMul_always #() mul_S_S  (
        .clk(clk),.rst_n(rst_n), .valid_in(valid_in), .a(S_t), .b(S_t), .valid_out(v1), .result(S_sq));

    fxMul_always #() mul_b1S  (
        .clk(clk),.rst_n(rst_n), .valid_in(valid_in), .a(beta[1]), .b(S_t), .valid_out( ), .result(b1S));

    fxMul_always #() mul_b2S2 (
        .clk(clk),.rst_n(rst_n), .valid_in(v1), .a(beta[2]), .b(S_sq), .valid_out(v2), .result(b2S2));

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            C_val <= '0;
        else if (v2) 
            C_val <= beta[0] + b1S + b2S2;
    end

    // immediate exercise payoff
    //-----------------------------------------
    logic signed [WIDTH-1:0] payoff;
    always_comb begin
        payoff = (strike > S_t) ? strike - S_t : '0;
    end

    // decision & output cash-flow
    //-----------------------------------------
    logic v_compare;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PV <= '0;
            valid_out <= 1'b0;
        end
        else if (v2) begin
            valid_out <= 1'b1;
            PV <= (payoff >= C_val) ? payoff :  // exercise now
                          ((C_val * disc) >>> QFRAC);   // hold (discounted)
        end
        else
            valid_out <= 1'b0;
    end

endmodule

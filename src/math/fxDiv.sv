`timescale 1ns/1ps
// Fixed-point divider. Uses a Xilinx DIV_GEN (DSP48E1) core with pipeline depth

module fxDiv #(
    parameter int WIDTH    = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT     = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC    = fpga_cfg_pkg::FP_QFRAC,
    parameter int LATENCY  = fpga_cfg_pkg::FP_DIV_LATENCY          
) (
    input  logic clk,
    input  logic rst_n,

    input  logic valid_in,
    output logic ready_out,
    output logic valid_out,
    input  logic ready_in,

    input  logic signed [WIDTH-1:0] numerator,
    input  logic signed [WIDTH-1:0] denominator,
    output logic signed [WIDTH-1:0] result
);

// Skid buffer (one-deep for backpressure)
logic skid_valid;
logic signed [WIDTH-1:0] skid_numerator;
logic signed [WIDTH-1:0] skid_denominator;

logic accept_to_skid;
assign accept_to_skid = valid_in && ready_out && (ready_in || !skid_valid);

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        skid_valid <= 1'b0;
        skid_numerator <= '0;
        skid_denominator <= '0;
    end else if (accept_to_skid) begin
        skid_numerator <= numerator;
        skid_denominator <= (denominator == 0) ? (1 <<< QFRAC) : denominator;
        skid_valid <= 1'b1;
    end else if (ready_in && skid_valid) begin
        skid_valid <= 1'b0;
    end
end

// Valid signal pipeline
logic [LATENCY-1:0] valid_pipe;
logic shift_en;
assign shift_en = ready_in || !valid_pipe[LATENCY-1];

// Input staging (from skid or direct)
logic signed [WIDTH-1:0] num_reg, den_reg;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        num_reg <= '0;
        den_reg <= '0;
    end else if ((skid_valid || valid_in) && ready_out) begin
        num_reg <= skid_valid ? skid_numerator : numerator;
        den_reg <= skid_valid ? skid_denominator : ((denominator == 0) ? (1 <<< QFRAC) : denominator);
    end
end

// Xilinx DIV_GEN core wrapper (generate in Vivado IP Catalog as per comments)
logic core_nd, core_rfd, core_ready;
logic signed [WIDTH-1:0] core_result;

assign core_nd  = (skid_valid || valid_in) && ready_out; // new data
assign core_rfd = ready_out;            // core ready for data

fxDiv_core div_u (
    .aclk   (clk),
    .s_axis_divisor_tdata (den_reg),
    .s_axis_divisor_tvalid(core_nd),
    .s_axis_dividend_tdata(num_reg),
    .s_axis_dividend_tvalid(core_nd),
    .m_axis_dout_tdata    (core_result),
    .m_axis_dout_tvalid   (core_ready)
);

// Pipeline valid-bit shift
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        valid_pipe <= '0;
    else if (shift_en)
        valid_pipe <= {valid_pipe[LATENCY-2:0], core_ready};
end

assign valid_out = valid_pipe[LATENCY-1];
assign result = core_result;

// Standard ready_out pattern
assign ready_out = !valid_pipe[0] || shift_en || !skid_valid;


initial begin
    assert property (no_div_zero) else $error("Divide by zero propagated");
    

    assert property (@(posedge clk) disable iff (!rst_n) valid_in && (denominator == 0) |-> !valid_out) 
        else $error("Divide by zero propagated");
    

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(result)) 
        else $error("fxDiv: Backpressure violation - result overwritten");
    

    assert property (@(posedge clk) disable iff (!rst_n) skid_valid && !ready_in |=> $stable(skid_numerator)) 
        else $error("fxDiv skid stall overwrite");
    
end

endmodule
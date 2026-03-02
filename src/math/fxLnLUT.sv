timeunit 1ns; timeprecision 1ps;
module fxlnLUT #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS  = 12,
    parameter string LUT_FILE = "src/gen/ln_lut_4096.mem"
)(
    input logic clk,
    input logic rst_n,

    input  logic valid_in,
    output logic ready_out,
    output logic valid_out,
    input  logic ready_in,

    input logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] result
);

    localparam [WIDTH-1:0] A_MIN = 1 << (QFRAC-LUT_BITS);
    localparam [WIDTH-1:0] A_MAX = 2 << QFRAC;

    (* rom_style="block" *)
    logic [WIDTH-1:0] lut [0:(1<<LUT_BITS)-1];
    initial $readmemh(LUT_FILE, lut);

    // Stage 1: clamp + register a_bound (valid pulse s1_valid)
    logic                s1_valid;
    logic [WIDTH-1:0]    a_bound;
    logic                s1_can_accept;

    // Stage 2: LUT read + output register (valid pulse v_reg)
    logic                v_reg;
    logic [WIDTH-1:0]    result_reg;

    // Stage 2 can drain when downstream is ready or output slot is empty
    wire s2_can_drain = ready_in || !v_reg;
    // Stage 1 can drain into stage 2 when stage 2 can accept
    wire s1_can_drain = !s1_valid || s2_can_drain;

    assign ready_out = s1_can_drain;

    // Stage 1: clamp input, register a_bound and s1_valid
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s1_valid <= 1'b0;
            a_bound  <= '0;
        end else begin
            if (s1_valid && s2_can_drain) begin
                s1_valid <= 1'b0;
            end
            if (valid_in && ready_out) begin
                s1_valid <= 1'b1;
                if (a == '0 || a < A_MIN)
                    a_bound <= A_MIN;
                else if (a > A_MAX)
                    a_bound <= A_MAX;
                else
                    a_bound <= a;
            end
        end
    end

    // LUT index derived from registered a_bound (valid in stage 2)
    logic [LUT_BITS-1:0] lut_index;
    assign lut_index = a_bound[QFRAC-1 -: LUT_BITS];

    // Stage 2: read LUT using now-valid a_bound, output result
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v_reg      <= 1'b0;
            result_reg <= '0;
        end else begin
            if (v_reg && ready_in)
                v_reg <= 1'b0;

            if (s1_valid && s2_can_drain) begin
                v_reg      <= 1'b1;
                result_reg <= (a_bound < (1 << QFRAC)) ? -lut[lut_index] : lut[lut_index];
            end
        end
    end

    assign valid_out = v_reg;
    assign result    = result_reg;

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(result))
        else $error("LnLUT stall overwrite");
    initial begin
        assert (QFRAC >= LUT_BITS)
            else $error("fxlnLUT: QFRAC < LUT_BITS");
    end
endmodule

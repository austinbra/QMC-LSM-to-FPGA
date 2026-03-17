timeunit 1ns; timeprecision 1ps;
// Synthesizable fixed-point natural logarithm via range decomposition + BRAM LUT
// with linear interpolation for full Q16.16 accuracy.
//
// Algorithm:
//   1. Find MSB position k of input a  (priority encoder)
//   2. int_log2 = k - QFRAC            (integer part of log2(a))
//   3. Normalize: shift a so MSB is at bit 31, extract LUT_BITS fractional bits
//   4. LUT stores ln(1 + frac) for frac in [0, 1)
//   5. Linear interpolation between adjacent LUT entries using sub-fractional bits
//   6. result = int_log2 * LN2 + interpolated_LUT_value
//
// 3-stage pipeline with ready/valid handshaking. No DSP required.
// Input a is unsigned Q16.16 (must be > 0 for meaningful result).
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
    localparam signed [WIDTH-1:0] LN2_Q = 32'sd45426;            // ln(2) * 65536
    localparam signed [WIDTH-1:0] LN_ZERO_CLAMP = -32'sd1310720; // -20.0 * 65536
    localparam int SUB_BITS = WIDTH - 1 - LUT_BITS;              // 19 for W=32, LUT=12

    // synthesis translate_off
    initial begin : check_ln_constants
        automatic int fp;
        fp = fpga_cfg_pkg::fp_from_real(0.693147180559945);
        assert(LN2_Q >= fp-1 && LN2_Q <= fp+1)
            else $error("LN2_Q mismatch: %0d vs ~%0d", LN2_Q, fp);
        fp = fpga_cfg_pkg::fp_from_real(-20.0);
        assert(LN_ZERO_CLAMP >= fp-1 && LN_ZERO_CLAMP <= fp+1)
            else $error("LN_ZERO_CLAMP mismatch: %0d vs ~%0d", LN_ZERO_CLAMP, fp);
    end
    // synthesis translate_on

    logic [WIDTH-1:0] lut [0:(1<<LUT_BITS)-1];
    initial $readmemh(LUT_FILE, lut);

    // ---------------------------------------------------------------
    // Priority encoder: find position of highest set bit.
    // Returns 0 for input 0 (handled by zero flag).
    // ---------------------------------------------------------------
    function automatic [4:0] find_msb(input [31:0] v);
        find_msb = 5'd0;
        for (int i = 0; i < 32; i++)
            if (v[i]) find_msb = i[4:0];
    endfunction

    // ---------------------------------------------------------------
    // Combinational: MSB position, barrel shift, LUT address
    // ---------------------------------------------------------------
    logic [4:0]       msb_pos;
    logic [WIDTH-1:0] a_norm;

    assign msb_pos = find_msb(a);
    assign a_norm  = a << (5'd31 - msb_pos);

    // ---------------------------------------------------------------
    // Stage 1: register MSB info, LUT addresses, sub-fractional bits
    // ---------------------------------------------------------------
    logic               s1_valid;
    logic               s1_zero;
    logic signed [5:0]  s1_int_log2;
    logic [LUT_BITS-1:0] s1_lut_addr;
    logic [LUT_BITS-1:0] s1_lut_addr_next;
    logic [SUB_BITS-1:0] s1_sub_frac;

    // ---------------------------------------------------------------
    // Stage 2: register LUT values, compute delta
    // ---------------------------------------------------------------
    logic               s2_valid;
    logic               s2_zero;
    logic signed [5:0]  s2_int_log2;
    logic [SUB_BITS-1:0] s2_sub_frac;
    logic signed [WIDTH-1:0] s2_lut_val;
    logic signed [WIDTH-1:0] s2_delta;

    // ---------------------------------------------------------------
    // Stage 3: output registers
    // ---------------------------------------------------------------
    logic               s3_valid;
    logic [WIDTH-1:0]   s3_result;

    // ---------------------------------------------------------------
    // Handshake: 3-stage pipeline
    // ---------------------------------------------------------------
    wire s3_accept = !s3_valid || ready_in;
    wire s2_accept = !s2_valid || s3_accept;
    wire s1_accept = !s1_valid || s2_accept;

    assign ready_out = s1_accept;
    assign valid_out = s3_valid;
    assign result    = s3_result;

    // ---------------------------------------------------------------
    // Stage 1: normalize input, compute addresses
    // ---------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s1_valid <= 1'b0;
        end else if (s1_accept) begin
            if (valid_in) begin
                s1_valid         <= 1'b1;
                s1_zero          <= (a == '0);
                s1_int_log2      <= $signed({1'b0, msb_pos}) - $signed(6'(QFRAC));
                s1_lut_addr      <= a_norm[WIDTH-2 -: LUT_BITS];
                s1_lut_addr_next <= a_norm[WIDTH-2 -: LUT_BITS] + 1'b1;
                s1_sub_frac      <= a_norm[WIDTH-2-LUT_BITS -: SUB_BITS];
            end else begin
                s1_valid <= 1'b0;
            end
        end
    end

    // ---------------------------------------------------------------
    // Stage 2: read LUT entries, compute delta
    // ---------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s2_valid <= 1'b0;
        end else if (s2_accept) begin
            if (s1_valid) begin
                s2_valid     <= 1'b1;
                s2_zero      <= s1_zero;
                s2_int_log2  <= s1_int_log2;
                s2_sub_frac  <= s1_sub_frac;
                s2_lut_val   <= $signed({1'b0, lut[s1_lut_addr][WIDTH-2:0]});
                s2_delta     <= $signed({1'b0, lut[s1_lut_addr_next][WIDTH-2:0]})
                              - $signed({1'b0, lut[s1_lut_addr][WIDTH-2:0]});
            end else begin
                s2_valid <= 1'b0;
            end
        end
    end

    // ---------------------------------------------------------------
    // Stage 3: interpolate and compute final result
    //   result = int_log2 * LN2 + lut_val + (sub_frac * delta) >> SUB_BITS
    // ---------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s3_valid  <= 1'b0;
            s3_result <= '0;
        end else if (s3_accept) begin
            if (s2_valid) begin
                s3_valid <= 1'b1;
                if (s2_zero)
                    s3_result <= LN_ZERO_CLAMP;
                else begin
                    logic signed [WIDTH+SUB_BITS-1:0] interp_product;
                    logic signed [WIDTH-1:0] interp_correction;
                    logic signed [WIDTH-1:0] base_val;

                    interp_product = $signed({{(WIDTH){1'b0}}, s2_sub_frac}) * s2_delta;
                    interp_correction = interp_product[SUB_BITS +: WIDTH];
                    base_val = s2_int_log2 * LN2_Q + s2_lut_val;
                    s3_result <= base_val + interp_correction;
                end
            end else begin
                s3_valid <= 1'b0;
            end
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(result))
        else $error("LnLUT stall overwrite");
endmodule

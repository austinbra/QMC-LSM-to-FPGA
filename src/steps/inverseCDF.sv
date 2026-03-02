timeunit 1ns; timeprecision 1ps;
module inverseCDF #(
    parameter int WIDTH              = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT               = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC              = fpga_cfg_pkg::FP_QFRAC,
    parameter int LANE_ID            = 0
)(
    input logic clk,
    input logic rst_n,

    input logic valid_in,
    output logic ready_out,

    input logic signed [WIDTH-1:0] u_in,

    output logic valid_out,
    input logic ready_in,

    output logic signed [WIDTH-1:0] z_out
);

    localparam signed [WIDTH-1:0] NEG_TWO = -(2 << QFRAC);

    // Skid buffer
    logic buf_valid;
    logic signed [WIDTH-1:0] buf_u_in;

    logic step1_ready, loglut_ready, mul_neg2_ready, sqrt_unit_ready, rational_ready;
    logic barrier_ready;

    assign barrier_ready = step1_ready && loglut_ready && mul_neg2_ready && sqrt_unit_ready && rational_ready;
    assign ready_out = (!buf_valid || barrier_ready);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 0;
            buf_u_in  <= 0;
        end else begin
            if (valid_in && ready_out) begin
                buf_u_in  <= u_in;
                buf_valid <= 1;
            end else if (buf_valid && barrier_ready && ready_in) begin
                buf_valid <= 0;
            end
        end
    end

    // Step 1: fold U(0,1) into (0,0.5] + negate flag
    logic [WIDTH-1:0] x;
    logic negate;
    logic v1;

    inverseCDF_fold #() fold_stage (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(buf_valid),
        .valid_out(v1),
        .ready_in(loglut_ready),
        .ready_out(step1_ready),
        .u(buf_u_in),
        .x(x),
        .negate(negate)
    );

    // Step 2: sqrt(-2 * ln(x))
    logic [WIDTH-1:0] ln_x;
    logic v2a;

    fxlnLUT #() loglut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v1),
        .valid_out(v2a),
        .ready_in(mul_neg2_ready),
        .ready_out(loglut_ready),
        .a(x),
        .result(ln_x)
    );

    logic [WIDTH-1:0] neg2_ln_x;
    logic v2b;

    fxMul #() mul_neg2(
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2a),
        .valid_out(v2b),
        .ready_in(sqrt_unit_ready),
        .ready_out(mul_neg2_ready),
        .a(ln_x),
        .b(NEG_TWO),
        .result(neg2_ln_x)
    );

    logic [WIDTH-1:0] t_val;
    logic v3;

    fxSqrt #() sqrt_unit (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2b),
        .valid_out(v3),
        .ready_in(rational_ready),
        .ready_out(sqrt_unit_ready),
        .a(neg2_ln_x),
        .result(t_val)
    );

    // Negate alignment FIFO: push on fold output, pop on sqrt output.
    // This keeps the negate flag in sync with the data flowing through
    // ln -> mul -> sqrt, regardless of per-stage stall behavior.
    logic [0:0] neg_push [0:0];
    logic [0:0] neg_pop  [0:0];
    logic       neg_fifo_full, neg_fifo_empty;

    assign neg_push[0] = negate;

    event_align_fifo_arr #(.N(1), .DW(1), .DEPTH(4)) u_negate_align (
        .clk       (clk),
        .rst_n     (rst_n),
        .push_en   (v1),
        .push_data (neg_push),
        .pop_en    (v3 && rational_ready),
        .pop_data  (neg_pop),
        .full      (neg_fifo_full),
        .empty     (neg_fifo_empty)
    );

    wire negate_aligned = neg_pop[0];

    // Step 3: Zelen & Severo rational approximation
    // fxInvCDF_ZS captures t and negate internally (one-at-a-time processing)
    fxInvCDF_ZS #(.WIDTH(WIDTH), .QINT(QINT)) rational (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v3),
        .valid_out(valid_out),
        .ready_in(ready_in),
        .ready_out(rational_ready),
        .t(t_val),
        .negate(negate_aligned),
        .z(z_out)
    );

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(z_out))
        else $error("InvCDF: Stall overwrite");
endmodule

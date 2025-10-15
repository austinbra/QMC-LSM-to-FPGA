timeunit 1ns; timeprecision 1ps;
module fxSqrt #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS = 8,
    parameter int LATENCY = fpga_cfg_pkg::FP_SQRT_LATENCY
)(
    input  logic            clk,
    input  logic            rst_n,
    input  logic            valid_in,
    output logic            ready_out,
    output logic            valid_out,
    input  logic            ready_in,
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] result
);
    // Skid buffer
    logic skid_valid;
    logic [WIDTH-1:0] skid_a;

    // Stage-0 forward-ready (next stage can accept)
    logic mul1_ready;

    // Single driver for ready_out
    assign ready_out = !skid_valid || mul1_ready;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skid_valid <= 1'b0;
            skid_a     <= '0;
        end else if (valid_in && ready_out) begin
            skid_valid <= 1'b1;
            skid_a     <= a;
        end else if (skid_valid && mul1_ready) begin
            skid_valid <= 1'b0;
        end
    end

    logic [WIDTH-1:0] a_in = skid_valid ? skid_a : a;

    // Control
    logic v0, v1, v2, v3, v4;
    logic accept = valid_in && ready_out;

    localparam signed [WIDTH-1:0] ONE_POINT_FIVE = (3 << (QFRAC-1));
    localparam signed [WIDTH-1:0] HALF          = 1 << (QFRAC-1);

    // Normalization
    logic [WIDTH-1:0] a_norm, a_norm_reg;
    logic [$clog2(QINT+1)-1:0] exp_adj, exp_adj_reg;

    always_comb begin
        a_norm = a_in;
        exp_adj = '0;
        for (int s = 0; s < QINT; s++) begin
            if (a_norm[QINT+QFRAC-1] == 1'b0) begin
                a_norm  = a_norm << 1;
                exp_adj = exp_adj + 1;
            end
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            a_norm_reg <= '0;
            exp_adj_reg <= '0;
        end else if (accept) begin
            a_norm_reg <= a_norm;
            exp_adj_reg <= exp_adj;
        end
    end

    // LUT
    logic [LUT_BITS-1:0] lut_index = a_norm_reg[QFRAC + LUT_BITS - 1 : QFRAC];

    (* rom_style="block" *) logic signed [WIDTH-1:0] sqrt_lut [0:(1<<LUT_BITS)-1];
    initial $readmemh("sqrt_lut_256.mem", sqrt_lut);

    logic signed [WIDTH-1:0] v0_result, a_v0;
    assign v0 = accept;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            a_v0      <= '0;
            v0_result <= '0;
        end else if (v0) begin
            a_v0      <= a_in;
            v0_result <= sqrt_lut[lut_index];
        end
    end

    // Mul1: r0^2
    logic mul2_ready;
    logic signed [WIDTH-1:0] mul1_result;

    fxMul #(.LATENCY(2)) mul1 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v0),
        .ready_out (mul1_ready),
        .valid_out (v1),
        .ready_in  (mul2_ready),
        .a         (v0_result),
        .b         (v0_result),
        .result    (mul1_result)
    );

    logic signed [WIDTH-1:0] v1_result, a_v1;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v1_result <= '0;
            a_v1      <= '0;
        end else if (v1 && mul2_ready) begin
            v1_result <= (mul1_result + HALF) >>> QFRAC;  // signed
            a_v1      <= a_v0;
        end
    end

    // Mul2: a * r0^2
    logic signed [WIDTH-1:0] mul2_result;
    logic mul3_ready, mul4_ready;
    logic mul_barrier_ready = mul3_ready && mul4_ready;

    fxMul #(.LATENCY(2)) mul2 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v1),
        .ready_out (mul2_ready),
        .valid_out (v2),
        .ready_in  (mul3_ready),
        .a         (a_v1),
        .b         (v1_result),
        .result    (mul2_result)
    );

    logic signed [WIDTH-1:0] v2_result, a_v2, r0_hold_1, r0_hold_2;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r0_hold_1 <= '0;
            r0_hold_2 <= '0;
        end else if (v0) begin
            r0_hold_1 <= v0_result;
        end else if (v1) begin
            r0_hold_2 <= r0_hold_1;
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v2_result <= '0;
            a_v2      <= '0;
        end else if (v2 && mul3_ready) begin
            v2_result <= mul2_result >>> QFRAC;  // signed
            a_v2      <= a_v1;
        end
    end

    // Mul3: r1 = r0 * (1.5 - 0.5 * a*r0^2)
    wire signed [WIDTH-1:0] term = ONE_POINT_FIVE - (v2_result >>> 1);
    logic signed [WIDTH-1:0] mul3_result;

    fxMul #(.LATENCY(2)) mul3 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v2),
        .ready_out (mul3_ready),
        .valid_out (v3),
        .ready_in  (mul_barrier_ready),
        .a         (r0_hold_2),
        .b         (term),
        .result    (mul3_result)
    );

    logic signed [WIDTH-1:0] v3_result, a_v3;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v3_result <= '0;
            a_v3      <= '0;
        end else if (v3 && mul4_ready) begin
            v3_result <= (mul3_result + HALF) >>> QFRAC;  // signed
            a_v3      <= a_v2;
        end
    end

    // Mul4: result = a * r1
    logic signed [WIDTH-1:0] mul4_result;

    fxMul #(.LATENCY(2)) mul4 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v3),
        .ready_out (mul4_ready),
        .valid_out (v4),
        .ready_in  (ready_in),
        .a         (a_v3),
        .b         (v3_result),
        .result    (mul4_result)
    );

    logic signed [WIDTH-1:0] v4_result;
    logic [WIDTH-1:0] tmp;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v4_result <= '0;
        end else if (v4 && ready_in) begin
            tmp       <= (mul4_result + HALF) >>> QFRAC;  // signed
            v4_result <= tmp >> (exp_adj_reg >> 1);
        end
    end

    assign valid_out = v4;
    assign result    = v4_result;

    // Assertions
    property stall_stable;
        @(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(result);
    endproperty
    initial begin
        assert property (stall_stable) else $error("fxSqrt stall overwrite");
    end
endmodule
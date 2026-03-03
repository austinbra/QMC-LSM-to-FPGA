timeunit 1ns; timeprecision 1ps;
module lsm_decision #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int LANE_ID   = 0
)(
    input  logic                     clk,
    input  logic                     rst_n,

    input  logic                     valid_in,
    output logic                     valid_out,
    input  logic                     ready_in,
    output logic                     ready_out,

    input  logic signed [WIDTH-1:0]  S_t,
    input  logic signed [WIDTH-1:0]  beta[0:2],
    input  logic signed [WIDTH-1:0]  strike,
    input  logic signed [WIDTH-1:0]  cont_value,
    input  logic                     option_type,  // 0=CALL max(S-K,0), 1=PUT max(K-S,0)

    output logic signed [WIDTH-1:0]  PV
);
    // Skid buffer
    typedef struct packed {
        logic signed [WIDTH-1:0] S_t;
        logic signed [WIDTH-1:0] strike;
        logic signed [WIDTH-1:0] cont_value;
    } input_t;
    logic signed [WIDTH-1:0] beta_reg[0:2];

    input_t in_buf;
    logic buf_valid;
    logic shift_en;
    assign shift_en = ready_in && buf_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= '0;
            in_buf <= '{0, 0, 0};
            for (int i = 0; i < 3; i++)
                beta_reg[i] <= '0;
        end else begin
            if (valid_in && ready_out) begin
                in_buf <= '{S_t, strike, cont_value};
                for (int i = 0; i < 3; i++)
                    beta_reg[i] <= beta[i];
                buf_valid <= 1;
            end else if (shift_en) begin
                buf_valid <= '0;
            end
        end
    end

    logic mul_S_S_ready, mul_b1S_ready, mul_b2S2_ready;
    logic barrier_ready;

    assign barrier_ready = mul_S_S_ready && mul_b1S_ready && mul_b2S2_ready;
    assign ready_out = (!buf_valid || (barrier_ready && ready_in));

    // Continuation estimate: C = beta[0] + beta[1]*S + beta[2]*S^2
    logic v1, v2;
    logic signed [WIDTH-1:0] S_sq, b1S, b2S2;
    logic signed [WIDTH-1:0] c_val_next;

    fxMul #() mul_S_S (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (buf_valid),
        .valid_out  (v1),
        .ready_in   (mul_b2S2_ready),
        .ready_out  (mul_S_S_ready),
        .a          (in_buf.S_t),
        .b          (in_buf.S_t),
        .result     (S_sq)
    );

    fxMul #() mul_b1S (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (buf_valid),
        .valid_out  (),
        .ready_in   (ready_in),
        .ready_out  (mul_b1S_ready),
        .a          (beta_reg[1]),
        .b          (in_buf.S_t),
        .result     (b1S)
    );

    fxMul #() mul_b2S2 (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (v1),
        .valid_out  (v2),
        .ready_in   (ready_in),
        .ready_out  (mul_b2S2_ready),
        .a          (beta_reg[2]),
        .b          (S_sq),
        .result     (b2S2)
    );

    assign c_val_next = beta_reg[0] + b1S + b2S2;

    // Immediate exercise payoff: CALL max(S-K,0), PUT max(K-S,0)
    logic signed [WIDTH-1:0] payoff;
    logic signed [WIDTH-1:0] diff_call, diff_put;
    localparam signed [WIDTH-1:0] MAX_POS = {1'b0, {(WIDTH-1){1'b1}}};

    assign diff_call = in_buf.S_t - in_buf.strike;
    assign diff_put  = in_buf.strike - in_buf.S_t;

    always_comb begin
        if (option_type) begin
            // PUT: max(K - S, 0)
            payoff = (in_buf.strike > in_buf.S_t) ? ((diff_put > MAX_POS) ? MAX_POS : diff_put) : '0;
        end else begin
            // CALL: max(S - K, 0)
            payoff = (in_buf.S_t > in_buf.strike) ? ((diff_call > MAX_POS) ? MAX_POS : diff_call) : '0;
        end
    end

    // Decision & output
    // Proper LSMC: regression estimate is used for the DECISION only.
    // The actual cashflow uses:
    //   - exercise: immediate payoff
    //   - continue: actual continuation value (input, not regression estimate)
    logic hold_valid;
    logic signed [WIDTH-1:0] hold_pv;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PV         <= '0;
            hold_pv    <= '0;
            hold_valid <= 1'b0;
            valid_out  <= 1'b0;
        end else begin
            if (!hold_valid && v2 && barrier_ready && shift_en) begin
                hold_valid <= 1'b1;
                hold_pv    <= (payoff >= c_val_next) ? payoff : in_buf.cont_value;
            end else if (hold_valid && ready_in) begin
                hold_valid <= 1'b0;
            end

            valid_out <= hold_valid;
            if (hold_valid)
                PV <= hold_pv;
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(PV))
        else $error("Decision: Stall violation");
endmodule

module lsm_decision #( //sequential
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int LANE_ID   = 0
)(
    input  logic                     clk,
    input  logic                     rst_n,

    //per-path inputs
    input  logic                     valid_in,  
    output logic                     valid_out,
    input  logic                     ready_in,  
    output logic                     ready_out,
    
    input  logic signed [WIDTH-1:0]  S_t,
    input  logic signed [WIDTH-1:0]  beta[0:2],
    input  logic signed [WIDTH-1:0]  strike,     // K or strike price
    input  logic signed [WIDTH-1:0]  disc,       // discount to current day = exp(-r * t)

    output logic signed [WIDTH-1:0]  PV   // chosen best value
);
    //BUFFER
    typedef struct packed { 
        logic signed [WIDTH-1:0] S_t, 
        logic signed [WIDTH-1:0] beta[0:2];
        logic signed [WIDTH-1:0] strike;
        logic signed [WIDTH-1:0] disc;
    } input_t;

    input_t in_buf;
    logic buf_valid;
    logic shift_en;
    assign shift_en = ready_in && buf_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= '0;
            in_buf <= '{0, {0,0,0}, 0, 0};
        end else begin
            if (valid_in && ready_out) begin
                in_buf <= '{S_t, beta, strike, disc};
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
    // continuation value
    //------------------------------------- 
    logic v1, v2;
    logic signed [WIDTH-1:0] S_sq, b1S, b2S2, C_val;

    

    fxMul #() mul_S_S  (
        .clk(clk),.rst_n(rst_n), 
        .valid_in   (valid_in), 
        .valid_out  (v1),
        .ready_in   (mul_b2S2_ready),
        .ready_out  (mul_S_S_ready),
        .a          (in_buf.S_t), 
        .b          (in_buf.S_t), 
        .result     (S_sq)
    );

    fxMul #() mul_b1S  (
        .clk(clk),.rst_n(rst_n), 
        .valid_in   (valid_in), 
        .valid_out  (), 
        .ready_in   (ready_in),
        .ready_out  (mul_b1S_ready),
        .a          (in_buf.beta[1]), 
        .b          (in_buf.S_t), 
        .result     (b1S)
    );

    fxMul #() mul_b2S2 (
        .clk(clk),.rst_n(rst_n), 
        .valid_in   (v1), 
        .valid_out  (v2),
        .ready_in   (ready_in),
        .ready_out  (mul_b2S2_ready),
        .a          (in_buf.beta[2]), 
        .b          (S_sq), 
        .result     (b2S2)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            C_val <= '0;
        else if (v2 && barrier_ready && shift_en) 
            C_val <= in_buf.beta[0] + b1S + b2S2;
    end

    // immediate exercise payoff
    //-----------------------------------------
    logic signed [WIDTH-1:0] payoff;
    always_comb begin
        logic signed [WIDTH-1:0] diff = in_buf.strike - in_buf.S_t;
        payoff = (in_buf.strike > in_buf.S_t) ? ((diff > (1 << (WIDTH-1)-1)) ? (1 << (WIDTH-1)-1) : diff) : '0;
    end

    // decision & output cash-flow
    //-----------------------------------------
    logic v_compare;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PV <= '0;
            valid_out <= 1'b0;
        end
        else if (v2 && barrier_ready && shift_en && ready_in) begin
            valid_out <= 1'b1;
            PV <= (payoff >= C_val) ? payoff :  // exercise now
                ((C_val * in_buf.disc) >>> QFRAC);   // hold (discounted)
        end
        else
            valid_out <= 1'b0;
    end
    initial begin
	    assert property (@(posedge clk) C_val >= 0) 
            else $error("Negative C_val in decision");
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(PV)) 
            else $error("Decision: Stall violation");
    end
endmodule

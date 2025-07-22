`timescale 1ns/1ps
// Accumulator for quadratic LSM regression (β0 + β1·S + β2·S²)
module accumulator #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int N_SAMPLES = 10000,
    parameter int LANE_ID   = 0
)(
    input  logic                     clk,
    input  logic                     rst_n,

    input  logic                     valid_in,
    output logic                     valid_out,
    input  logic                     ready_in,
    output logic                     ready_out,

    // stream from GBM / decision
    input  logic signed [WIDTH-1:0]  x_in,   // S_t
    input  logic signed [WIDTH-1:0]  y_in,   // discounted payoff

    // β’s once per exercise date
    output logic signed [WIDTH-1:0]  beta [0:2]


);

    localparam int IDLE = 0, SOLVE = 1, WAIT = 2;
    logic [1:0] state;
    
    
    //dumb skid buffer
    typedef struct packed {
        logic signed [WIDTH-1:0] x_in;
        logic signed [WIDTH-1:0] y_in;
    } input_t;

    input_t in_buf;
    logic buf_valid;
    logic shift_en;
    assign shift_en = ready_in && buf_valid;  // Standard clear trigger

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 0;
            in_buf <= '{0, 0};  // Explicit reset
        end else begin
            if (valid_in && ready_out) begin
                in_buf <= '{x_in, y_in};
                buf_valid <= 1;
            end else if (shift_en) begin
                buf_valid <= '0;
            end
        end
    end

    //stuff
    

    logic mul_x_x_ready, mul_x_y_ready, mul_x2_y_ready, mul_x2_x_ready, mul_x2_x2_ready;
    logic solver_ready,div_mean_ready;
    logic parallel_barrier;
    logic accum_barrier_ready;

    assign parallel_barrier = mul_x_x_ready && mul_x_y_ready;
    assign accum_barrier_ready = mul_x2_y_ready && mul_x2_x_ready && mul_x2_x2_ready;
    assign ready_out = (!buf_valid || (parallel_barrier && accum_barrier_ready && solver_ready && (state == IDLE)));


    logic v_x2, v_acc;
    logic signed [WIDTH-1:0] x2, xy, x2y, x3, x4;
    fxMul #() mul_x_x (
        .clk (clk), .rst_n (rst_n),
        .valid_in  (valid_in),
        .valid_out (v_x2),
        .ready_in  (ready_in && (state == IDLE)),
        .ready_out (mul_x_x_ready),
        .a         (in_buf.x_in),
        .b         (in_buf.x_in),
        .result    (x2)
    );

    fxMul #() mul_x_y (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (valid_in), 
        .valid_out  (/*unused*/),
        .ready_in   (ready_in && (state == IDLE)),
        .ready_out  (mul_x_y_ready),
        .a          (in_buf.x_in), 
        .b          (in_buf.y_in), 
        .result     (xy)
    );



    fxMul #() mul_x2_y (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (v_x2), 
        .valid_out  (v_acc),
        .ready_in   (mul_x_x_ready && ready_in && (state == IDLE)),
        .ready_out  (mul_x2_y_ready),
        .a          (x2), 
        .b          (in_buf.y_in), 
        .result     (x2y)
    );

    // extra mults fed by x2 so they line-up with v_acc
    fxMul #() mul_x2_x (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (v_x2), 
        .valid_out  (/*unused*/),
        .ready_in   (mul_x_x_ready && ready_in && (state == IDLE)), 
        .ready_out  (mul_x2_x_ready),
        .a          (x2), 
        .b          (in_buf.x_in), 
        .result     (x3)
    );

    fxMul #() mul_x2_x2 (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (v_x2), 
        .valid_out  (/*unused*/),
        .ready_in   (mul_x_x_ready && ready_in && (state == IDLE)), 
        .ready_out  (mul_x2_x2_ready),
        .a          (x2), 
        .b          (x2), 
        .result     (x4)
    );

    // ------------------------------------------------------------
    // 2) 64-bit accumulators
    // ------------------------------------------------------------
    typedef logic signed [63:0] acc_t;

    function acc_t extended (input logic signed [WIDTH-1:0] v);
        extended = {{(64-WIDTH){v[WIDTH-1]}}, v};
    endfunction

    acc_t sum1, sumx, sumx2, sumx3, sumx4, sumy, sumxy, sumx2y;
    logic [$clog2(N_SAMPLES):0] count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sum1    <= '0; 
            sumx    <= '0; 
            sumx2   <= '0; 
            sumx3   <= '0; 
            sumx4   <= '0;
            sumy    <= '0; 
            sumxy   <= '0; 
            sumx2y  <= '0; 
            count   <= '0;
        end else if (v_acc && parallel_barrier && accum_barrier_ready && shift_en) begin
            sum1    <= sum1     + 1;
            sumx    <= sumx     + extended(in_buf.x_in);
            sumx2   <= sumx2    + extended(x2);
            sumx3   <= sumx3    + extended(x3);
            sumx4   <= sumx4    + extended(x4);
            sumy    <= sumy     + extended(in_buf.y_in);
            sumxy   <= sumxy    + extended(xy);
            sumx2y  <= sumx2y   + extended(x2y);
            count   <= count    + 1;
        end
    end

    // ------------------------------------------------------------
    // 3) do solver when all sums complete
    // ------------------------------------------------------------
    logic start_solver, solver_done;
    logic signed [WIDTH-1:0] mat_flat [0:11];
    logic signed [WIDTH-1:0] beta_s [0:2];
    logic singular_err;

    regression solver (
        .clk(clk), 
        .rst_n(rst_n),
        .valid_in(start_solver),
        .mat_flat(mat_flat),
        .ready_in(ready_in),
        .ready_out(solver_ready),
        .valid_out(solver_done),
        .singular_err(singular_err),
        .beta(beta_s)
    );

    logic fallback_trigger;
    logic signed [WIDTH-1:0] mean_payoff;
    logic mean_done;

    fxDiv #() div_mean (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (fallback_trigger),
        .numerator  (sumy << QFRAC), 
        .denominator(sum1[WIDTH-1:0]),
        .result     (mean_payoff), 
        .valid_out  (mean_done),
        .ready_in   (ready_in), 
        .ready_out  (div_mean_ready)  // Chain ready
    );

    function logic signed [WIDTH-1:0] saturate(acc_t val);
        automatic logic signed [WIDTH-1:0] max_pos = (1 <<< (WIDTH-1)) - 1;
        automatic logic signed [WIDTH-1:0] max_neg = -(1 <<< (WIDTH-1));
        if (val > max_pos) 
            saturate = max_pos;
        else if (val < max_neg) 
            saturate = max_neg;
        else 
            saturate = val[WIDTH-1:0];
    endfunction

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || singular_err) begin
            state <= IDLE;
            start_solver <= '0;
            valid_out <= '0;
            fallback_trigger <= '0;
        end else case (state)
            IDLE:
                if (count == N_SAMPLES && ready_out) begin  // ts took me so long, so confusing
                    // Row 0 (signed saturation to prevent overflow)
                    mat_flat[0] = saturate(sum1);
                    mat_flat[1] = saturate(sumx);
                    mat_flat[2] = saturate(sumx2);
                    mat_flat[3] = saturate(sumy);
                    // Row 1
                    mat_flat[4] = saturate(sumx);
                    mat_flat[5] = saturate(sumx2);
                    mat_flat[6] = saturate(sumx3);
                    mat_flat[7] = saturate(sumxy);
                    // Row 2
                    mat_flat[8] = saturate(sumx2);
                    mat_flat[9] = saturate(sumx3);
                    mat_flat[10] = saturate(sumx4 );
                    mat_flat[11] = saturate(sumx2y);
                    start_solver <= 1;
                    state <= SOLVE;
                end
            SOLVE:
                if (solver_ready) begin
                    start_solver <= '0;
                    state <= WAIT;
                  end
            WAIT: 
                if (solver_done && ready_in) begin
                    logic fallback;
                    assign fallback = singular_err;

                    // fallback: beta[0] = mean payoff; beta[1] = beta[2] = 0
                    if (fallback) begin
                        fallback_trigger <= 1;
                        if (mean_done && ready_in) begin
                            fallback_trigger <= '0;
                            beta[0] <= mean_payoff;
                            beta[1] <= '0;
                            beta[2] <= '0;
                            valid_out <= 1;
                        end else
                            valid_out <= '0;
                    end else begin // normal case: use solver output beta's
                        beta <= beta_s;
                        valid_out <= 1;
                    end
                    // reset for next date
                    sum1 <= '0;
                    sumx <= '0;
                    sumx2 <= '0;
                    sumx3 <= '0;
                    sumx4 <= '0;
                    sumy <= '0;
                    sumxy <= '0;
                    sumx2y <= '0;
                    count <= '0;
                    state <= IDLE;
                end else
                    valid_out <= '0;
        endcase
    end

    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) v_acc && accum_barrier_ready |-> $stable(x2) && $stable(xy) && $stable(x2y) && $stable(x3) && $stable(x4)) 
            else $error("Mul desync on stall"); //sync
        

        assert property (@(posedge clk) disable iff (!rst_n) !ready_out |-> !valid_out) //handsjake invar
            else $error("Output valid while not ready");
        

        assert property (@(posedge clk) disable iff (!rst_n) singular_err |=> singular_err) //singluar stickiness
            else $error("singular_err not sticky");
        
        
	    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(beta)) 
            else $error("Accumulator: Output stall overwrite");
        

        assert property (@(posedge clk) disable iff (!rst_n) v_x2 |-> v_x2) 
            else $error("Desync in initial muls");

        
    end
endmodule

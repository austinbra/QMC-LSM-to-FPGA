// Accumulator for quadratic LSM regression (β0 + β1·S + β2·S²)
module accumulator #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int N_SAMPLES = 10000
)(
    input  logic                     clk,
    input  logic                     rst_n,

    input  logic                     valid_in;
    output logic                     valid_out;
    input  logic                     ready_in;
    output logic                     ready_out;

    // stream from GBM / decision
    input  logic signed [WIDTH-1:0]  x_in,   // S_t
    input  logic signed [WIDTH-1:0]  y_in,   // discounted payoff

    // β’s once per exercise date
    output logic signed [WIDTH-1:0]  beta [0:2],


);
    logic shift_en;

    logic v_x2, v_acc;
    logic signed [WIDTH-1:0] x2, xy, x2y, x3, x4;

    logic mul_x_x_ready, mul_x_y_ready, mul_x2_y_ready, mul_x2_x_ready, mul_x2_x2_ready;

    wire barrier_ready = mul_x_x_ready && mul_x_y_ready && mul_x2_y_ready && mul_x2_x_ready && mul_x2_x2_ready;
    
    assign ready_out = (shift_en && barrier_ready) && (state == IDLE);
    assign shift_en = ready_in || !valid_out && barrier_ready;

    fxMul_always #() mul_x_x (
        .clk (clk), .rst_n (rst_n),
        .valid_in  (valid_in),
        .valid_out (v_x2),
        .ready_in  (ready_in && (state == IDLE)),
        .ready_out (mul_x_x_ready),
        .a         (x_in),
        .b         (x_in),
        .result    (x2)
    );

    fxMul_always #() mul_x_y (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (valid_in), 
        .valid_out  (/*unused*/),
        .ready_in   (ready_in && (state == IDLE)),
        .ready_out  (mul_x_y_ready),
        .a          (x_in), 
        .b          (y_in), 
        .result     (xy)
    );



    fxMul_always #() mul_x2_y (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (v_x2), 
        .valid_out  (v_acc),
        .ready_in   (mul_x_x_ready && ready_in && (state == IDLE)),
        .ready_out  (mul_x2_y_ready),
        .a          (x2), 
        .b          (y_in), 
        .result     (x2y)
    );

    // extra mults fed by x2 so they line-up with v_acc
    fxMul_always #() mul_x2_x (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (v_x2), 
        .valid_out  (/*unused*/),
        .ready_in   (mul_x_x_ready && ready_in && (state == IDLE)), 
        .ready_out  (mul_x2_x_ready),
        .a          (x2), 
        .b          (x_in), 
        .result     (x3)
    );

    fxMul_always #() mul_x2_x2 (
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
        end
        else if (v_acc && shift_en && barrier_ready) begin
            sum1    <= sum1     + 1;
            sumx    <= sumx     + extended(x_in);
            sumx2   <= sumx2    + extended(x2);
            sumx3   <= sumx3    + extended(x3);
            sumx4   <= sumx4    + extended(x4);
            sumy    <= sumy     + extended(y_in);
            sumxy   <= sumxy    + extended(xy);
            sumx2y  <= sumx2y   + extended(x2y);
            count   <= count    + 1;
        end
    end

    // ------------------------------------------------------------
    // 3) do solver when all sums complete
    // ------------------------------------------------------------
    localparam int IDLE = 0, SOLVE = 1, WAIT = 2;
    logic [1:0] state;
    logic start_solver, solver_done;
    logic signed [WIDTH-1:0] mat_flat [0:11];
    logic signed [WIDTH-1:0] beta_s [0:2];
    logic singular_err;
    logic solver_ready;

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
    logic div_mean_ready;

    fxDiv #() div_mean (
        .clk(clk), .rst_n(rst_n), 
        .valid_in   (fallback_trigger && barrier_ready),  // Gate with barrier for sync
        .numerator  (sumy <<< QFRAC), 
        .denominator(sum1[WIDTH-1:0]),
        .result     (mean_payoff), 
        .valid_out  (mean_done),
        .ready_in   (ready_in), 
        .ready_out  (div_mean_ready)  // Chain ready
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || singular_err) begin
            state <= IDLE;
            start_solver <= 0;
            valid_out <= 0;
            fallback_trigger <= 0;
        end else case (state)
            IDLE:
                if (count == N_SAMPLES && barrier_ready) begin  // ts took me so long, so confusing
                    // Row 0 (signed saturation to prevent overflow)
                    mat_flat[0] = (sum1 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sum1 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sum1[WIDTH-1:0];
                    mat_flat[1] = (sumx > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx[WIDTH-1:0];
                    mat_flat[2] = (sumx2 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx2 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx2[WIDTH-1:0];
                    mat_flat[3] = (sumy > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumy < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumy[WIDTH-1:0];
                    // Row 1
                    mat_flat[4] = (sumx > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx[WIDTH-1:0];
                    mat_flat[5] = (sumx2 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx2 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx2[WIDTH-1:0];
                    mat_flat[6] = (sumx3 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx3 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx3[WIDTH-1:0];
                    mat_flat[7] = (sumxy > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumxy < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumxy[WIDTH-1:0];
                    // Row 2
                    mat_flat[8] = (sumx2 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx2 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx2[WIDTH-1:0];
                    mat_flat[9] = (sumx3 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx3 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx3[WIDTH-1:0];
                    mat_flat[10] = (sumx4 > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx4 < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx4[WIDTH-1:0];
                    mat_flat[11] = (sumx2y > (1 <<< (WIDTH-1)-1)) ? ((1 <<< (WIDTH-1))-1) : (sumx2y < -(1 <<< (WIDTH-1))) ? -(1 <<< (WIDTH-1)) : sumx2y[WIDTH-1:0];
                    start_solver <= 1;
                    state <= SOLVE;
                end
            SOLVE:
                if (ready_in) begin
                    start_solver <= '0;
                    state <= WAIT;
                  end
            WAIT: 
                if (solver_done) begin
                    logic fallback = singular_err;

                    // fallback: beta[0] = mean payoff; beta[1] = beta[2] = 0
                    if (fallback) begin
                        fallback_trigger <= 1;
                        if (mean_done && ready_in) begin
                            fallback_trigger <= 0;
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
        assert property (@(posedge clk) disable iff (!rst_n) v_acc && barrier_ready |-> $stable(x2) && $stable(xy) && $stable(x2y) && $stable(x3) && $stable(x4)) 
            else $error("Mul desync on stall"); //sync

        assert property (@(posedge clk) disable iff (!rst_n) !ready_out |-> !valid_out) //handsjake invar
            else $error("Output valid while not ready");

        assert property (@(posedge clk) disable iff (!rst_n) singular_err |=> singular_err) //singluar stickiness
            else $error("singular_err not sticky");
    end
endmodule

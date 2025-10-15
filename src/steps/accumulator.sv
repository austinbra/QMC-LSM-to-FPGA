timeunit 1ns; timeprecision 1ps;
// Accumulator for quadratic LSM regression (β0 + β1·S + β2·S²)
module accumulator #(
    parameter int WIDTH       = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT        = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC       = fpga_cfg_pkg::FP_QFRAC,
    parameter int N_SAMPLES   = 10000,
    // Align FIFO depth should be >= fxMul pipeline latency
    parameter int ALIGN_DEPTH = fpga_cfg_pkg::FP_MUL_LATENCY,
    parameter int LANE_ID     = 0
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // per-path input stream
    input  logic                     valid_in,
    output logic                     ready_out,

    // downstream (solver) handshake
    output logic                     valid_out,
    input  logic                     ready_in,

    // stream from GBM / decision
    input  logic signed [WIDTH-1:0]  x_in,   // S_t
    input  logic signed [WIDTH-1:0]  y_in,   // discounted payoff

    // β’s once per exercise date
    output logic signed [WIDTH-1:0]  beta [0:2]
);
    // FSM
    localparam int IDLE  = 0;
    localparam int SOLVE = 1;
    localparam int WAIT  = 2;
    logic [1:0] state;

    // Skid buffer I/F (array form): [0]=x, [1]=y
    logic                     skid_s_ready;
    logic                     skid_m_valid;
    logic                     skid_m_ready;
    logic [WIDTH-1:0]         skid_s_data [0:1];
    logic [WIDTH-1:0]         skid_m_data [0:1];

    // Head/tail mul barrier handshakes
    logic mul_x_x_ready;
    logic mul_x_y_ready;
    logic mul_x2_y_ready;
    logic mul_x2_x_ready;
    logic mul_x2_x2_ready;

    logic parallel_barrier;
    logic accum_barrier_ready;
    logic head_tail_ready;

    // Launch/done counters (batch control)
    logic [$clog2(N_SAMPLES+1)-1:0] cnt_launch;
    logic [$clog2(N_SAMPLES+1)-1:0] cnt_done;

    // Launch control and source to head
    logic                           fire_head;
    logic signed [WIDTH-1:0]        src_x;
    logic signed [WIDTH-1:0]        src_y;

    // Align FIFO outputs
    logic [WIDTH-1:0]               align_push [0:1];
    logic [WIDTH-1:0]               align_pop  [0:1];
    logic                           q_full;
    logic                           q_empty;

    // Math datapath
    logic                           v_x2;
    logic                           v_acc;
    logic signed [WIDTH-1:0]        x2;
    logic signed [WIDTH-1:0]        xy;
    logic signed [WIDTH-1:0]        x2y;
    logic signed [WIDTH-1:0]        x3;
    logic signed [WIDTH-1:0]        x4;
    logic signed [WIDTH-1:0]        x2_reg;
    logic signed [WIDTH-1:0]        xy_reg;
    wire  signed [WIDTH-1:0]        x_aligned = align_pop[0];
    wire  signed [WIDTH-1:0]        y_aligned = align_pop[1];

    // Solver I/F
    logic                      start_solver;
    logic                      solver_done;
    logic                      solver_ready;
    logic signed [WIDTH-1:0]   mat_flat [0:11];
    logic                      singular_err;
    logic signed [WIDTH-1:0]   beta_s [0:2];

    logic batch_clear;
    assign batch_clear = (state == WAIT) && solver_done && ready_in;


    // Accumulators (64-bit)
    typedef logic signed [63:0] acc_t;
    function automatic acc_t extended (input logic signed [WIDTH-1:0] v);
        return {{(64-WIDTH){v[WIDTH-1]}}, v};
    endfunction

    acc_t sum1;
    acc_t sumx;
    acc_t sumx2;
    acc_t sumx3;
    acc_t sumx4;
    acc_t sumy;
    acc_t sumxy;
    acc_t sumx2y;

    // Saturate down to WIDTH (signed)
    function automatic logic signed [WIDTH-1:0]
        saturate (input acc_t val);
        logic signed [WIDTH-1:0] max_pos;
        logic signed [WIDTH-1:0] min_neg;
        begin
            max_pos = {1'b0, {WIDTH-1{1'b1}}};
            min_neg = {1'b1, {WIDTH-1{1'b0}}};
            if (val > max_pos)      return max_pos;
            else if (val < min_neg) return min_neg;
            else                    return val[WIDTH-1:0];
        end
    endfunction

    // ----------------------------------------------------------------------------
    // Handshake/barrier logic
    // ----------------------------------------------------------------------------
    assign parallel_barrier     = mul_x_x_ready && mul_x_y_ready;
    assign accum_barrier_ready  = mul_x2_y_ready && mul_x2_x_ready && mul_x2_x2_ready;
    assign head_tail_ready      = accum_barrier_ready; // tie fxMul head ready_in

    // Batch acceptance gating
    wire accept_allowed = (state == IDLE) && (cnt_launch < N_SAMPLES);

    // Connect upstream to skid
    assign skid_s_data[0] = x_in;
    assign skid_s_data[1] = y_in;

    // Pop skid only when head can fire (both barriers) and batch accept allowed
    assign skid_m_ready = parallel_barrier && accum_barrier_ready && accept_allowed;

    // Upstream ready is skid ready (with accept gating inside)
    rv_skid_arr_gate #(.N(2), .DW(WIDTH)) u_skid (
        .clk         (clk),
        .rst_n       (rst_n),
        .s_valid     (valid_in),
        .s_ready     (ready_out),
        .s_data      (skid_s_data),
        .gate_accept (accept_allowed),
        .m_valid     (skid_m_valid),
        .m_ready     (skid_m_ready),
        .m_data      (skid_m_data)
    );

    // Head fire/pop condition
    assign fire_head = skid_m_valid && skid_m_ready;
    assign src_x     = skid_m_data[0];
    assign src_y     = skid_m_data[1];

    // ----------------------------------------------------------------------------
    // Head multipliers (launch on fire_head), drain into tail barrier
    // ----------------------------------------------------------------------------
    fxMul #() mul_x_x (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (fire_head),
        .ready_out (mul_x_x_ready),
        .ready_in  (head_tail_ready),
        .valid_out (v_x2),
        .a         (src_x),
        .b         (src_x),
        .result    (x2)
    );

    fxMul #() mul_x_y (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (fire_head),
        .ready_out (mul_x_y_ready),
        .ready_in  (head_tail_ready),
        .valid_out (/*unused*/),
        .a         (src_x),
        .b         (src_y),
        .result    (xy)
    );

    // Track launches, capture x2/xy when head result valid,
    // and align x/y to the v_x2 timing using the event-align FIFO.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cnt_launch <= '0;
            x2_reg     <= '0;
            xy_reg     <= '0;
        end else begin
            if (batch_clear) begin
                cnt_launch <= '0;
            end else if (fire_head) begin
                cnt_launch <= cnt_launch + 1;
            end
            if (v_x2) begin
                x2_reg <= x2;
                xy_reg <= xy;
            end
        end
    end

    assign align_push[0] = src_x;
    assign align_push[1] = src_y;

    event_align_fifo_arr #(.N(2), .DW(WIDTH), .DEPTH(ALIGN_DEPTH)) u_align (
        .clk       (clk),
        .rst_n     (rst_n),
        .push_en   (fire_head),
        .push_data (align_push),
        .pop_en    (v_x2),
        .pop_data  (align_pop),
        .full      (q_full),
        .empty     (q_empty)
    );

    // ----------------------------------------------------------------------------
    // Tail multipliers (drain unconditionally)
    // ----------------------------------------------------------------------------
    fxMul #() mul_x2_y (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v_x2),
        .ready_out (mul_x2_y_ready),
        .ready_in  (1'b1),
        .valid_out (v_acc),
        .a         (x2_reg),
        .b         (y_aligned),
        .result    (x2y)
    );

    fxMul #() mul_x2_x (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v_x2),
        .ready_out (mul_x2_x_ready),
        .ready_in  (1'b1),
        .valid_out (/*unused*/),
        .a         (x2_reg),
        .b         (x_aligned),
        .result    (x3)
    );

    fxMul #() mul_x2_x2 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v_x2),
        .ready_out (mul_x2_x2_ready),
        .ready_in  (1'b1),
        .valid_out (/*unused*/),
        .a         (x2_reg),
        .b         (x2_reg),
        .result    (x4)
    );

    // ----------------------------------------------------------------------------
    // Accumulate (on v_acc)
    // ----------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || batch_clear) begin
            sum1     <= '0;
            sumx     <= '0;
            sumx2    <= '0;
            sumx3    <= '0;
            sumx4    <= '0;
            sumy     <= '0;
            sumxy    <= '0;
            sumx2y   <= '0;
            cnt_done <= '0;
        end else if (v_acc) begin
            sum1     <= sum1   + acc_t'(1);
            sumx     <= sumx   + extended(x_aligned);
            sumx2    <= sumx2  + extended(x2_reg);
            sumx3    <= sumx3  + extended(x3);
            sumx4    <= sumx4  + extended(x4);
            sumy     <= sumy   + extended(y_aligned);
            sumxy    <= sumxy  + extended(xy_reg);
            sumx2y   <= sumx2y + extended(x2y);
            cnt_done <= cnt_done + 1;
        end
    end

    // ----------------------------------------------------------------------------
    // Regression solver
    // ----------------------------------------------------------------------------
    regression solver (
        .clk         (clk),
        .rst_n       (rst_n),
        .valid_in    (start_solver),
        .ready_out   (solver_ready),
        .ready_in    (ready_in),
        .mat_flat    (mat_flat),
        .valid_out   (solver_done),
        .singular_err(singular_err),
        .beta        (beta_s)
    );

    // ----------------------------------------------------------------------------
    // FSM: pack matrix and run solver after batch done
    // ----------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state        <= IDLE;
            start_solver <= 1'b0;
            valid_out    <= 1'b0;
            beta[0]      <= '0;
            beta[1]      <= '0;
            beta[2]      <= '0;
        end else begin
            valid_out    <= 1'b0;
            start_solver <= 1'b0;

            unique case (state)
                IDLE: begin
                    if (cnt_done == N_SAMPLES) begin
                        // Pack normal equations (saturated)
                        mat_flat[0]  <= saturate(sum1);
                        mat_flat[1]  <= saturate(sumx);
                        mat_flat[2]  <= saturate(sumx2);
                        mat_flat[3]  <= saturate(sumy);
                        mat_flat[4]  <= saturate(sumx);
                        mat_flat[5]  <= saturate(sumx2);
                        mat_flat[6]  <= saturate(sumx3);
                        mat_flat[7]  <= saturate(sumxy);
                        mat_flat[8]  <= saturate(sumx2);
                        mat_flat[9]  <= saturate(sumx3);
                        mat_flat[10] <= saturate(sumx4);
                        mat_flat[11] <= saturate(sumx2y);
                        // Handshake with solver
                        if (solver_ready) begin
                            start_solver <= 1'b1;
                            state        <= SOLVE;
                        end
                    end
                end

                SOLVE: begin
                    // De-assert start next cycle by default logic
                    if (solver_ready) begin
                        state <= WAIT;
                    end
                end

                WAIT: begin
                    if (solver_done && ready_in) begin
                        // Regression handles fallback internally; just pass β’s
                        beta[2]   <= beta_s[2];
                        beta[1]   <= beta_s[1];
                        beta[0]   <= beta_s[0];
                        valid_out <= 1'b1;

                        state     <= IDLE;
                    end
                end
            endcase
        end
    end

    // ----------------------------------------------------------------------------
    // Assertions
    // ----------------------------------------------------------------------------
    initial begin
        assert (ALIGN_DEPTH >= fpga_cfg_pkg::FP_MUL_LATENCY)
            else $error("Accumulator: ALIGN_DEPTH (%0d) must be >= fxMul latency (%0d)", ALIGN_DEPTH, fpga_cfg_pkg::FP_MUL_LATENCY);
        
        assert (N_SAMPLES > 0)
            else $error("Accumulator: N_SAMPLES must be > 0");
    end

    always_ff @(posedge clk) if (rst_n) begin
        if (valid_out && !ready_in)
            assert ($stable(beta)) else $error("Accumulator: Output stall overwrite");

        assert (!(cnt_launch == N_SAMPLES && ready_out))
            else $error("Accumulator: ready_out high after N_SAMPLES");

        assert (!(q_full && fire_head))
            else $error("Accumulator: x/y align FIFO overflow");

        assert (!(q_empty && v_x2))
            else $error("Accumulator: x/y align FIFO underflow");
    end

endmodule
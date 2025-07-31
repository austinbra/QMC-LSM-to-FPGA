// ============================================================================
//  tb_fxDiv.sv  -  minimal self-checking test-bench for fxDiv
//                 * 20 random divisions
//                 * checks every result and prints PASS / FAIL
//                 * first-result trace kept for eye-balling
// ----------------------------------------------------------------------------
//  Vivado / XSim 2025.x - zero synthesis constructs, pure simulation
// ============================================================================

`timescale 1ns/1ps
module tb_fxDiv;

    //------------------------------------------------------------------
    //  USER-TUNABLE CONSTANTS
    //------------------------------------------------------------------
    localparam int CLK_PERIOD_NS = 10;      // 100 MHz sim clock
    localparam int WIDTH         = 32;      // must match fxDiv.sv
    localparam int QFRAC         = 16;
    localparam int N_VECTORS     = 20;      // number of random tests

    //------------------------------------------------------------------
    //  Clock & reset
    //------------------------------------------------------------------
    logic clk = 1'b0;   always #(CLK_PERIOD_NS/2) clk = ~clk;

    logic rst_n = 1'b0;
    initial repeat (3) @(posedge clk) rst_n = 1'b1;   // release reset

    //------------------------------------------------------------------
    //  DUT interface signals
    //------------------------------------------------------------------
    logic                       valid_in , ready_out;
    logic                       valid_out, ready_in = 1'b1;
    logic signed [WIDTH-1:0]    numerator , denominator;
    logic signed [WIDTH-1:0]    result;

    //------------------------------------------------------------------
    //  Device-under-test
    //------------------------------------------------------------------
    fxDiv #(.WIDTH(WIDTH), .QFRAC(QFRAC)) dut (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (valid_in),
        .ready_out  (ready_out),
        .numerator  (numerator),
        .denominator(denominator),
        .valid_out  (valid_out),
        .ready_in   (ready_in),
        .result     (result)
    );

    //------------------------------------------------------------------
    //  Stimulus generator
    //------------------------------------------------------------------
    int sent = 0;
    initial begin
        valid_in = 1'b0;
        wait (rst_n);

        /* simple back-to-back traffic until N_VECTORS sent */
        forever begin
            // random operands   (den ≠ 0)
            automatic int n = $urandom_range(-200, 200);
            automatic int d;  do d = $urandom_range(-200, 200); while (d == 0);

            // wait until core is ready
            @(posedge clk);
            if (ready_out && sent < N_VECTORS) begin
                numerator    = n <<< QFRAC;   // convert to Q16.16
                denominator  = d <<< QFRAC;
                valid_in     = 1'b1;
                @(posedge clk);
                valid_in     = 1'b0;
                sent++;
            end
            if (sent == N_VECTORS) begin
                // stop driving ­after the last vector
                numerator  = '0; denominator = '0; valid_in = 1'b0;
                disable fork;
            end
        end
    end

    // ----------  SCORE-BOARD  ---------------------------------------------------
    localparam int LATENCY_EFF = 17;          // 16-cycle IP + 1 handshake

    logic signed [WIDTH-1:0] exp_q[$];       // golden FIFO
    int seen = 0;
    int errs = 0;

    // 17-deep shift-register that tracks “a reference is due in N cycles”
    logic [LATENCY_EFF-1:0] ref_vld_sr;       // one bit per cycle delay
    logic signed [WIDTH-1:0] ref_pipe [LATENCY_EFF-1:0];

    /* 1)  capture the reference when the request fires */
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ref_vld_sr <= '0;
        end
        else begin
            // shift every cycle
            ref_vld_sr <= {ref_vld_sr[LATENCY_EFF-2:0], 1'b0};

            if (valid_in && ready_out) begin
                // compute reference and load stage 0 of the pipe
                automatic longint q64 = (longint'(numerator) <<< QFRAC) / longint'(denominator);
                ref_pipe[0] <= q64[WIDTH-1:0];
                ref_vld_sr[0] <= 1'b1;
            end
        end
    end

    /* 2)  move reference data along the delay pipe */
    generate
        for (genvar i = 1; i < LATENCY_EFF; i++) begin
            always_ff @(posedge clk or negedge rst_n)
                if (!rst_n) ref_pipe[i] <= '0;
                else        ref_pipe[i] <= ref_pipe[i-1];
        end
    endgenerate

    /* 3)  when the bit reaches the tail, push into the FIFO */
    always_ff @(posedge clk)
        if (rst_n && ref_vld_sr[LATENCY_EFF-1])
            exp_q.push_back(ref_pipe[LATENCY_EFF-1]);

    /* 4)  pop + compare whenever the core produces a result */
    always_ff @(posedge clk)
        if (rst_n && valid_out && ready_in && exp_q.size() > 1) begin
            automatic logic signed [WIDTH-1:0] gold = exp_q.pop_front();
            if (result !== gold) begin
                $error("idx=%0d  got=%h  exp=%h", seen, result, gold);
                errs++;
            end
            else if (seen == 0)
                $display("FIRST RESULT  t=%0t  res=%h", $time, result);
            seen++;
        end

    //------------------------------------------------------------------
    //  Finish + summary
    //------------------------------------------------------------------
    always @(posedge clk)
        if (rst_n && seen == N_VECTORS) begin
            $display("\n========== fxDiv test summary ==========");
            if (errs == 0)
                $display("PASS - all %0d results correct.", N_VECTORS);
            else
                $display("FAIL - %0d errors out of %0d tests.", errs, N_VECTORS);
            $finish;
        end

    // 2 µs watchdog (prevents an infinite sim if something hangs)
    initial #2us $fatal(1, "Timeout - divider produced fewer than %0d results.", N_VECTORS);

endmodule

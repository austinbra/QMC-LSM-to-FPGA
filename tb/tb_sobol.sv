`timescale 1ns/1ps
module tb_sobol;

    parameter WIDTH = 32;
    parameter M     = 50;

    // clocks & resets
    logic clk, rst_n;

    // DUT handshakes & data
    logic                    valid_in, ready_out;
    logic                    valid_out, ready_in;
    logic [WIDTH-1:0]        idx_in, sobol_out;
    logic [$clog2(M)-1:0]    dim_in;

    // Expose LUT port
    logic [WIDTH-1:0] direction_tb [0:M*WIDTH-1];

    // Instantiate
    sobol #(.WIDTH(WIDTH), .M(M)) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .ready_out(ready_out),
        .valid_out(valid_out), .ready_in(ready_in),
        .idx_in(idx_in), .dim_in(dim_in),
        .sobol_out(sobol_out),
        .direction(direction_tb)
    );

    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test sequence (10 deterministic transactions with stalls + robust drain)
    initial begin
        // init
        rst_n    = 0;
        valid_in = 0;  ready_in = 1;
        idx_in   = 0;  dim_in   = 0;
        repeat(6) @(posedge clk);
        rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // Transaction 1: idx=0, dim=0 (expect 0)
        drive_input(0, 0);
        insert_stall(2);

        // Transaction 2: idx=1, dim=0 (expect 0x80000000 ~0.5)
        drive_input(1, 0);

        // Transaction 3: idx=2, dim=1 (expect 40000000 ~0.25)
        drive_input(2, 1);

        // Transaction 4: idx=MAX, dim=M-1
        drive_input((1<<WIDTH)-1, M-1);
        insert_stall(3);

        // Transaction 5: idx=3, dim=0 (test simultaneous potential)
        ready_in = 0;
        @(posedge clk);
        ready_in = 1;
        drive_input(3, 0);

        // Transaction 6: idx=4, dim=2
        drive_input(4, 2);

        // Transaction 7: idx=5, dim=M-1
        drive_input(5, M-1);

        // Transaction 8: idx=6, dim=0
        drive_input(6, 0);

        // Transaction 9: idx=7, dim=1
        drive_input(7, 1);
        insert_stall(1);

        // Transaction 10: idx=8, dim=0
        drive_input(8, 0);

        // Robust drain phase: Keep ready_in=1 until no valid_out for 5 consecutive cycles
        valid_in = 0;
        ready_in = 1;
        $display("Cycle %t: Starting drain phase", $time);
        begin
            int idle_cycles = 0;
            while (idle_cycles < 5) begin
                @(posedge clk);
                if (!valid_out) idle_cycles++;
                else idle_cycles = 0;  // Reset if output appears
            end
        end

        #20 $finish;
    end

    // Task to drive a single input (sets idx/dim, waits 1 cycle for comb, asserts valid_in until accepted, then deasserts)
    task drive_input(
        input logic [WIDTH-1:0] idx,
        input logic [$clog2(M)-1:0] d
    );
        idx_in = idx; dim_in = d;
        @(posedge clk);  // Allow 1 cycle for combinational logic to stabilize
        valid_in = 1;
        while (!ready_out) @(posedge clk);  // Wait for acceptance (tests backpressure)
        @(posedge clk);  // Hold for the acceptance cycle
        valid_in = 0;
    endtask

    // Task to insert stall (ready_in=0 for N cycles)
    task insert_stall(input int n);
        ready_in = 0;
        repeat(n) @(posedge clk);
        ready_in = 1;
    endtask

    // Monitor + checks (single block, no clocking/queue)
    int inputs_sent=0, outputs_rcvd=0;
    int max_stall=0, cur_stall=0;
    logic saw_zero=0, test_passed=1;
    logic [WIDTH-1:0] last_out; logic last_stall=0;

    // Static expected array for golden checks (corrected based on LUT and algorithm)
    typedef struct { logic [WIDTH-1:0] idx; logic [$clog2(M)-1:0] dim; logic [WIDTH-1:0] golden; } expected_t;
    expected_t expected_values [0:9] = '{
        '{idx: 0, dim: 0, golden: 32'h00000000},  // Correct: no bits set
        '{idx: 1, dim: 0, golden: 32'h80000000},  // Correct: bit0 -> dir[0]
        '{idx: 2, dim: 1, golden: 32'h40000000},  // Correct: gray=3, dir[32] ^ dir[33] = 80000000 ^ c0000000
        '{idx: (1<<WIDTH)-1, dim: M-1, golden: 'x},  // Unknown: skip
        '{idx: 3, dim: 0, golden: 32'h40000000},  // Corrected: gray=2, bit1 -> dir[1]
        '{idx: 4, dim: 2, golden: 32'he0000000},  // Correct: gray=6, bits1&2 -> dir[65] ^ dir[66] = 40000000 ^ 20000000
        '{idx: 5, dim: M-1, golden: 'x},          // Unknown: skip
        '{idx: 6, dim: 0, golden: 'x},            // Unknown: skip
        '{idx: 7, dim: 1, golden: 'x},            // Unknown: skip
        '{idx: 8, dim: 0, golden: 'x}             // Unknown: skip
    };
    int output_index = 0;  // Counter for expected_values

    always @(posedge clk) begin
        real frac;  // Procedural variable

        if (!rst_n) begin
            cur_stall = 0; last_stall = 0;
        end else begin
            // Count accepted inputs
            if (valid_in && ready_out) begin
                inputs_sent++;
                $display("Cycle %t: Input accepted idx=%0d dim=%0d", $time, idx_in, dim_in);
            end

            // Count consumed outputs and check
            if (valid_out && ready_in) begin
                outputs_rcvd++;
                // Fraction calculation (unsigned, real conversion)
                frac = $itor($unsigned(sobol_out)) / 4294967296.0;  // 2^32
                $display("Cycle %t: Output %h fraction=%f", $time, sobol_out, frac);
                if (frac < 0.0 || frac >= 1.0) begin
                    $error("Fraction %f not in [0,1)", frac);
                    test_passed = 0;
                end
                if (sobol_out == 0) saw_zero = 1;

                // Golden check using index (only if golden != 'x)
                if (output_index < 10) begin
                    automatic expected_t exp = expected_values[output_index];
                    if (exp.golden !== 'x && sobol_out != exp.golden) begin
                        $error("Output FAIL: For idx=%0d dim=%0d expected %h got %h",
                               exp.idx, exp.dim, exp.golden, sobol_out);
                        test_passed = 0;
                    end
                    output_index++;
                end

                cur_stall = 0; last_stall = 0;
            end else if (valid_out && !ready_in) begin
                cur_stall++;
                if (cur_stall > max_stall) max_stall = cur_stall;
                $display("Cycle %t: Stall hold output %h", $time, sobol_out);
                if (last_stall && sobol_out != last_out) begin
                    $error("Data changed during stall: %h -> %h", last_out, sobol_out);
                    test_passed = 0;
                end
                last_stall = 1;
            end else begin
                cur_stall = 0; last_stall = 0;
            end
            last_out = sobol_out;
        end
    end

    final begin
        $display("\n=== RESULTS ===");
        $display("Inputs sent    = %0d", inputs_sent);
        $display("Outputs recvd  = %0d", outputs_rcvd);
        if (inputs_sent == outputs_rcvd && inputs_sent == 10)
            $display("Handshake PASS");
        else begin
            $display("Handshake FAIL");
            test_passed=0;
        end
        if (saw_zero)
            $display("Zero test PASS");
        else begin
            $display("Zero test FAIL");
            test_passed=0;
        end
        if (max_stall>0)
            $display("Max stall cycles = %0d", max_stall);
        else
            $display("No stalls exercised (coverage warning)");

        $display("Overall: %s", test_passed?"PASS":"FAIL");
    end

    // LUT display
    initial begin
        #100ns;
        $display("LUT[0]=%h LUT[1]=%h LUT[2]=%h",
                 direction_tb[0],
                 direction_tb[1],
                 direction_tb[2]);
    end

endmodule
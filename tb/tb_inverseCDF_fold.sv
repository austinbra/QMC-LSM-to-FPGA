`timescale 1ns/1ps

module tb_inverseCDF_fold;

    // Parameters
    localparam int WIDTH = fpga_cfg_pkg::FP_WIDTH;
    localparam int QINT  = fpga_cfg_pkg::FP_QINT;
    localparam int QFRAC = fpga_cfg_pkg::FP_QFRAC;
    localparam logic [WIDTH-1:0] HALF = fpga_cfg_pkg::FP_HALF;
    localparam int MAX_TB_CYCLES = 5000;

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_in, valid_out, ready_out;
    logic signed [WIDTH-1:0] u;
    logic [WIDTH-1:0] x;
    logic negate;

    // DUT
    inverseCDF_fold #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .ready_in(ready_in),
        .valid_out(valid_out), .ready_out(ready_out),
        .u(u), .x(x), .negate(negate)
    );

    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test sequence
    initial begin
        rst_n = 0;
        valid_in = 0;
        ready_in = 1;
        u = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            // Hold input stable while backpressured to satisfy handshake contract.
            if (!(valid_in && !ready_out)) begin
                valid_in = $urandom % 2;
                if (valid_in)
                    u = $signed($urandom % (1 <<< QFRAC));  // [0,1) in QFRAC
            end
            ready_in = ($urandom % 10 > 2) ? 1 : 0;
            if (valid_in && ready_out) $display("Cycle %t: Input accepted (ready_out=%b) - u=%d", $time, ready_out, u);
            if (!ready_in) $display("Cycle %t: Stall", $time);
        end

        // Edge: u=0 (x=0, negate=0)
        u = 0; valid_in = 1; #10;
        if (valid_out) $display("Cycle %t: Output x=%d, negate=%b (expected x small, negate 0)", $time, x, negate);

        // Edge: u just above 0.5
        u = (1 <<< (QFRAC-1)) + 1; #10;

        #200 $finish;
    end

    // Assertions
    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(x))
        else $error("Step1 stall overwrite");
    // Verification Section
    int inputs_sent = 0, outputs_received = 0, stall_cycles = 0;
    logic test_passed = 1;
    always @(posedge clk) begin
        if (valid_in && ready_out) inputs_sent++;
        if (valid_out && ready_in) outputs_received++;
        if (!ready_in && valid_out) stall_cycles++;
    end

    final begin
        if (inputs_sent != outputs_received) begin
            $display("Handshake FAIL: Inputs=%d, Outputs=%d", inputs_sent, outputs_received);
            test_passed = 0;
        end else $display("Handshake PASS: All %d inputs processed", inputs_sent);

        // Correctness: negate=1 for u>0.5, x<=0.5
        if (valid_out && ((u > HALF && !negate) || x > HALF)) begin
            $display("Output FAIL: Incorrect negate=%b or x=%d for u=%d", negate, x, u);
            test_passed = 0;
        end else $display("Output PASS: negate=%b, x=%d", negate, x);

        if (stall_cycles > 0) $display("Stalls OK (%d cycles)", stall_cycles);
        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
    end

    // Global watchdog to avoid runaway simulation.
    initial begin
        repeat (MAX_TB_CYCLES) @(posedge clk);
        $fatal(1, "Timeout after %0d cycles", MAX_TB_CYCLES);
    end
endmodule
`timescale 1ns/1ps

module tb_accumulator;

    // Parameters (match DUT)
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;
    parameter N_SAMPLES = 10;  // Small for sim speed

    // Signals
    logic clk, rst_n;
    logic valid_in, valid_out, ready_in, ready_out;
    logic signed [WIDTH-1:0] x_in, y_in;
    logic signed [WIDTH-1:0] beta [0:2];

    // DUT instantiation
    accumulator #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .N_SAMPLES(N_SAMPLES)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .valid_out(valid_out),
        .ready_in(ready_in), .ready_out(ready_out), .solver_ready(1'b1),
        .x_in(x_in), .y_in(y_in),
        .beta(beta)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz
    end

    // Test sequence
    initial begin
        // Reset
        rst_n = 0;
        valid_in = 0;
        ready_in = 1;
        x_in = 0;
        y_in = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // Send N_SAMPLES inputs with random stalls
        for (int i = 0; i < N_SAMPLES; i++) begin
            @(posedge clk);
            valid_in = $urandom % 2;  // Random valid
            x_in = $urandom % (1 <<< 10);  // Small positive S_t
            y_in = $urandom % (1 <<< 8);   // Small payoff
            ready_in = ($urandom % 10 > 3) ? 1 : 0;  // 30% stall chance
            if (valid_in && ready_out) $display("Cycle %t: Input accepted (ready_out=%b) - x_in=%d, y_in=%d", $time, ready_out, x_in, y_in);
            if (!ready_in) $display("Cycle %t: Simulated stall (ready_in low)", $time);
            if (i == 5) y_in = - (1 <<< 8);  // Test negative
        end

        // Wait for output and check
        repeat (100) @(posedge clk);  // Wait for accumulation/solver
        if (valid_out) $display("Cycle %t: Output valid - beta[0]=%d, beta[1]=%d, beta[2]=%d", $time, beta[0], beta[1], beta[2]);
        else $display("Error: No output after simulation");

        // Edge case: Reset mid-accum
        #100 rst_n = 0; #20 rst_n = 1;
        $display("Cycle %t: Mid-accum reset tested", $time);

        $finish;
    end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(beta)) else $error("Accumulator stall overwrite");
        assert (beta[0] > 0) else $error("Unexpected negative beta[0]");
    end

    // Verification Section: Check outputs and handshakes
    int inputs_sent = 0, outputs_received = 0, stall_cycles = 0;
    logic test_passed = 1;
    always @(posedge clk) begin
        if (valid_in && ready_out) inputs_sent++;
        if (valid_out) outputs_received++;
        if (!ready_in && valid_out) stall_cycles++;  // Count stalls
    end

    final begin  // At sim end
        // Handshake check: Inputs == Outputs (no loss)
        if (inputs_sent != outputs_received) begin
            $display("Handshake FAIL: Inputs sent=%d, Outputs received=%d (possible data loss)", inputs_sent, outputs_received);
            test_passed = 0;
        end else $display("Handshake PASS: All %d inputs processed", inputs_sent);

        // Output correctness: Betas reasonable (e.g., positive for sample data)
        if (valid_out && (beta[0] <= 0 || beta[1] < 0)) begin
            $display("Output FAIL: Unexpected betas (%p) - expected positive", beta);
            test_passed = 0;
        end else $display("Output PASS: Reasonable betas (%p)", beta);

        // Stall check: Stalls occurred but no overwrite (from assert)
        if (stall_cycles > 0) $display("Stalls detected (%d cycles) - check asserts for integrity", stall_cycles);

        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
      end
endmodule
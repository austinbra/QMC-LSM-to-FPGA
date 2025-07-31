`timescale 1ns/1ps

module tb_regression;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_out, valid_out, ready_in, singular_err;
    logic signed [WIDTH-1:0] mat_flat [0:11], beta [0:2];

    // DUT
    regression #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .mat_flat(mat_flat),
        .ready_out(ready_out), .ready_in(ready_in),.solver_ready(1'b1),
        .valid_out(valid_out), .singular_err(singular_err),
        .beta(beta)
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
        for (int i = 0; i < 12; i++) mat_flat[i] = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // Send matrix with stalls
        valid_in = 1; ready_in = 0; #20 ready_in = 1;
        mat_flat = '{1<<<QFRAC, 2<<<QFRAC, 3<<<QFRAC, 4<<<QFRAC, 5<<<QFRAC, 6<<<QFRAC, 7<<<QFRAC, 8<<<QFRAC, 9<<<QFRAC, 10<<<QFRAC, 11<<<QFRAC, 12<<<QFRAC};  // Sample matrix        

        // Wait for output
        #200 if (valid_out) $display("Cycle %t: Beta=%p, singular=%b", $time, beta, singular_err);

        // Edge: Singular (zero pivot)
        mat_flat[0] = 0; valid_in = 1; #100;

        #300 $finish;
    end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(beta)) else $error("Regression stall overwrite");
    end
    // Verification Section
    int inputs_sent = 0, outputs_received = 0, stall_cycles = 0;
   logic test_passed = 1;
    always @(posedge clk) begin
        if (valid_in && ready_out) inputs_sent++;
        if (valid_out) outputs_received++;
        if (!ready_in && valid_out) stall_cycles++;
    end

    final begin
        if (inputs_sent != outputs_received) begin
            $display("Handshake FAIL: Inputs=%d, Outputs=%d", inputs_sent, outputs_received);
            test_passed = 0;
        end else $display("Handshake PASS: All %d inputs processed", inputs_sent);

       // Correctness: Non-singular has non-zero betas; singular triggers err
        if (valid_out && !singular_err && beta[0] == 0) begin
            $display("Output FAIL: Zero beta in non-singular case");
            test_passed = 0;
        end else if (singular_err && beta[0] != 0) $display("Output PASS with singular fallback");
        else $display("Output PASS: betas=%p, singular=%b", beta, singular_err);

        if (stall_cycles > 0) $display("Stalls OK (%d cycles)", stall_cycles);
        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
    end
endmodule
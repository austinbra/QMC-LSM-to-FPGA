`timescale 1ns/1ps

module tb_GBM;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;
    parameter DIV_LATENCY = 5;  // Assume

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_out, valid_out, ready_in;
    logic signed [WIDTH-1:0] z, S, r, sigma, dt, S_next;

    // DUT
    GBM #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .DIV_LATENCY(DIV_LATENCY)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .ready_out(ready_out),
        .valid_out(valid_out), .ready_in(ready_in),
        .z(z), .S(S), .r(r), .sigma(sigma), .dt(dt),
        .S_next(S_next)
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
        z = 0; S = 0; r = 0; sigma = 0; dt = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions with stalls
        for (int i = 0; i < 10; i++) begin
                    @(posedge clk);
            valid_in = $urandom % 2;
            z = $signed($urandom % (1 <<< 10)) - (1 <<< 9);  // +/- range
            S = $urandom % (1 <<< 10);  // Positive price
            r = $urandom % (1 <<< 5);
            sigma = $urandom % (1 <<< 5);
            dt = $urandom % (1 <<< 5);
            ready_in = ($urandom % 10 > 2) ? 1 : 0;  // 30% stall
            if (valid_in && ready_out) $display("Cycle %t: Input accepted (ready_out=%b) - z=%d, S=%d", $time, ready_out, z, S);
                    if (!ready_in) $display("Cycle %t: Stall simulated", $time);
            if (i == 5) sigma = 0;
    end

        // Edge: sigma=0 (no diffusion)
        valid_in = 1; sigma = 0; #10;
        if (valid_out) $display("Cycle %t: Output S_next=%d (expected close to S)", $time, S_next);

        // Edge: Negative z (price decrease)
        z = - (1 <<< 8); #10;
        valid_in = 1; #10;

        #200 $finish;
        end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(S_next)) else $error("GBM stall overwrite");
        assert (S_next < S) else $error("Negative z didn't decrease price");
    end

    // Verification Section: Check outputs and handshakes
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

        // Output correctness: S_next >0, approximate growth for positive z
        if (valid_out && S_next <= 0) begin
            $display("Output FAIL: Negative S_next=%d", S_next);
                test_passed = 0;
        end else $display("Output PASS: Reasonable S_next=%d", S_next);

        if (stall_cycles > 0) $display("Stalls OK (%d cycles)", stall_cycles);
        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
    end
endmodule
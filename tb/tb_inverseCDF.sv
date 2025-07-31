`timescale 1ns/1ps

module tb_inverseCDF;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_out, valid_out, ready_in;
    logic signed [WIDTH-1:0] u_in, z_out;

    // DUT
    inverseCDF #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .ready_out(ready_out),
        .u_in(u_in), .valid_out(valid_out), .ready_in(ready_in),
        .z_out(z_out)
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
        u_in = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            valid_in = $urandom % 2;
            u_in = $urandom % (1 <<< QFRAC);  // [0,1)
            ready_in = ($urandom % 10 > 2) ? 1 : 0;
            if (valid_in && ready_out) $display("Cycle %t: Input accepted  - u_in=%d", $time, u_in);
            if (!ready_in) $display("Cycle %t: Stall", $time);
        end

        // Edge: u_in=0 (z_out ≈ -inf, but clamped)
        u_in = 0; valid_in = 1; #50;
        if (valid_out) $display("Cycle %t: Output z_out=%d (expected large negative)", $time, z_out);
        

        // Edge: u_in close to 1 (z_out positive)
        u_in = (1 <<< QFRAC) - 1; #50;

        #500 $finish;
    end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(z_out)) else $error("InvCDF stall overwrite");
        assert (z_out < 0) else $error("Zero u_in didn't produce negative z");
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

        // Correctness: z_out symmetric around 0 for u_in 0.5
        if (valid_out && z_out == 0 && u_in != (1 <<< (QFRAC-1))) begin
            $display("Output FAIL: Unexpected zero z_out for u_in=%d", u_in);
            test_passed = 0;
        end else $display("Output PASS: z_out=%d", z_out);

        if (stall_cycles > 0) $display("Stalls OK (%d cycles)", stall_cycles);
        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
    end
endmodule
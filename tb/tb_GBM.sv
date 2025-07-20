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
            if (valid_in && ready_out) $display("Cycle %t: Input accepted - z=%d, S=%d", $time, z, S);
            if (!ready_in) $display("Cycle %t: Stall simulated", $time);
        end

        // Edge: sigma=0 (no diffusion)
        valid_in = 1; sigma = 0; #10;
        if (valid_out) $display("Cycle %t: Output S_next=%d (expected close to S)", $time, S_next);

        // Edge: Negative z (price decrease)
        z = - (1 <<< 8); #10;

        #200 $finish;
    end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(S_next)) else $error("GBM stall overwrite");
    end

endmodule
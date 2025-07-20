`timescale 1ns/1ps

module tb_inverseCDF_step1;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_in, valid_out, ready_out;
    logic signed [WIDTH-1:0] u;
    logic [WIDTH-1:0] x;
    logic negate;

    // DUT
    inverseCDF_step1 #(
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
            valid_in = $urandom % 2;
            u = $signed($urandom % (1 <<< QFRAC));  // [0,1) in QFRAC
            ready_in = ($urandom % 10 > 2) ? 1 : 0;
            if (valid_in && ready_out) $display("Cycle %t: Input accepted - u=%d", $time, u);
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
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(x)) else $error("Step1 stall overwrite");
    end

endmodule
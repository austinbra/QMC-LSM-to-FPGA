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
        .ready_out(ready_out), .ready_in(ready_in),
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
        valid_in = 1;
        mat_flat = '{1<<<QFRAC, 2<<<QFRAC, 3<<<QFRAC, 4<<<QFRAC, 5<<<QFRAC, 6<<<QFRAC, 7<<<QFRAC, 8<<<QFRAC, 9<<<QFRAC, 10<<<QFRAC, 11<<<QFRAC, 12<<<QFRAC};  // Sample matrix
        ready_in = 0; #20 ready_in = 1;  // Stall
        $display("Cycle %t: Input sent with stall", $time);

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

endmodule
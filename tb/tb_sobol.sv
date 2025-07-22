`timescale 1ns/1ps

module tb_sobol;

    // Parameters
    parameter WIDTH = 32;
    parameter M = 50;

    // Signals
    logic clk, rst_n;
    logic valid_in, ready_out, valid_out, ready_in;
    logic [WIDTH-1:0] idx_in, sobol_out;
    logic [$clog2(M)-1:0] dim_in;

    // DUT
    sobol #(
        .WIDTH(WIDTH), .M(M)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .ready_out(ready_out),
        .valid_out(valid_out), .ready_in(ready_in),
        .idx_in(idx_in), .dim_in(dim_in),
        .sobol_out(sobol_out)
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
        idx_in = 0; dim_in = 0;
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            valid_in = $urandom % 2;
            idx_in = i;
            dim_in = $urandom % M;
            ready_in = ($urandom % 10 > 2) ? 1 : 0;
            if (valid_in && ready_out) $display("Cycle %t: Input accepted (ready_out=%b) - idx=%d, dim=%d", $time, ready_out, idx_in, dim_in);
            if (!ready_in) $display("Cycle %t: Stall", $time);
        end

        // Edge: idx=0 (should be 0)
        idx_in = 0; valid_in = 1; #10;
        if (valid_out) $display("Cycle %t: sobol_out=%d (expected 0)", $time, sobol_out);

        // Edge: Max idx
        idx_in = (1 <<< WIDTH) - 1; #10;

        #200 $finish;
    end

    // Assertions
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(sobol_out)) else $error("Sobol stall overwrite");
        assert (sobol_out == 0) else $error("Zero idx didn't produce 0");
    end

endmodule
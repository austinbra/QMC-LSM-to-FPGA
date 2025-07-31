`timescale 1ns/1ps

module tb_uart32_loopback;

    parameter int CLK_FREQ_HZ = 100_000_000;
    parameter int BAUD_RATE   = 115200;
    localparam int CLKS_PER_BIT = CLK_FREQ_HZ / BAUD_RATE;
    localparam int NUM_TESTS = 10;

    logic clk = 0;
    logic rst_n = 0;

    logic        valid_in;
    logic [31:0] data_in;
    logic        ready_out;

    logic        tx;
    logic        tx_busy;

    logic        valid_out;
    logic [31:0] data_out;

    always #5 clk = ~clk;

    // DUTs
    uart_tx32 #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) dut_tx32 (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .data_in(data_in),
        .ready_out(ready_out),
        .tx(tx),
        .tx_busy(tx_busy)
    );

    uart_rx32 #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) dut_rx32 (
        .clk(clk),
        .rst_n(rst_n),
        .rx(tx),
        .valid_out(valid_out),
        .data_out(data_out)
    );

    int i;
    int pass_count = 0;
    logic [31:0] test_vals [NUM_TESTS];

    initial begin
        $display("=== UART 32-bit Loopback Test ===");

        // Reset
        clk = 0;
        rst_n = 0;
        valid_in = 0;
        data_in = 0;
        #100;
        rst_n = 1;
        #100;

        // Generate test inputs
        test_vals[0] = 32'sh00000000; // 0.0
        test_vals[1] = 32'sh00010000; // 1.0
        test_vals[2] = 32'shFFFF0000; // -1.0
        test_vals[3] = 32'sh00018000; // 1.5
        for (i = 4; i < NUM_TESTS; i++) begin
            test_vals[i] = $urandom;
        end

        for (i = 0; i < NUM_TESTS; i++) begin
            wait (ready_out == 1);
            @(posedge clk);

            data_in = test_vals[i];
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;

            $display("[%0t ns] 📨 TX sent word = 0x%08h", $time, data_in);

            // Wait for RX to receive full word
            wait (valid_out == 1);
            @(posedge clk);

            $display("[%0t ns] 📥 RX received word = 0x%08h", $time, data_out);

            if (data_out === data_in) begin
                $display("[%0t ns] ✅ PASS", $time);
                pass_count++;
            end else begin
                $display("[%0t ns] ❌ FAIL: Expected 0x%08h, got 0x%08h", $time, data_in, data_out);
            end

            #1000;
        end

        $display("=== UART 32-bit Loopback Complete: %0d / %0d Passed ===", pass_count, NUM_TESTS);
        $finish;
    end

endmodule

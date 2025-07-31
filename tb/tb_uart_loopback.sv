// IMPORTANT: Run simulation for 1,000,000ns or more
`timescale 1ns / 1ps

module tb_uart_loopback;

    parameter CLK_FREQ_HZ = 100_000_000;
    parameter BAUD_RATE   = 115200;
    localparam int CLKS_PER_BIT = CLK_FREQ_HZ / BAUD_RATE;
    localparam int NUM_TESTS = 10;

    logic clk = 0;
    logic rst_n = 0;

    logic tx_start;
    logic [7:0] tx_data;
    logic tx;
    logic tx_busy;

    logic [7:0] rx_data;
    logic rx_valid;

    // Clock generation: 100 MHz
    always #5 clk = ~clk;

    // Instantiate DUTs
    uart_tx #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) dut_tx (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_start(tx_start),
        .tx(tx),
        .tx_busy(tx_busy)
    );

    uart_rx #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) dut_rx (
        .clk(clk),
        .rst_n(rst_n),
        .rx(tx),
        .rx_data(rx_data),
        .rx_valid(rx_valid)
    );

    int i;
    byte tx_values [NUM_TESTS];
    int pass_count = 0;

    initial begin
        $display("=== UART Loopback Test Started ===");
        tx_start = 0;
        tx_data = 8'h00;
        rst_n = 0;
        #100;
        rst_n = 1;
        #100;

        // Define test inputs
        tx_values[0] = 8'h00;  // edge case
        tx_values[1] = 8'hFF;  // edge case
        tx_values[2] = 8'hA5;  // alternating
        tx_values[3] = 8'h5A;  // inverse
        for (i = 4; i < NUM_TESTS; i++) begin
            tx_values[i] = $urandom_range(0, 255);
        end

        for (i = 0; i < NUM_TESTS; i++) begin
            // Wait until transmitter is ready
            wait (tx_busy == 0);
            @(posedge clk);

            tx_data = tx_values[i];
            tx_start = 1;
            @(posedge clk);
            tx_start = 0;

            $display("[%0t ns] TX sent byte 0x%0h", $time, tx_data);

            // Wait long enough for RX to see full frame
            #(CLKS_PER_BIT * 11);

            // Wait for rx_valid
            wait (rx_valid == 1);
            @(posedge clk);

            if (rx_data === tx_data) begin
                $display("[%0t ns] ✅ PASS: Received 0x%0h", $time, rx_data);
                pass_count++;
            end else begin
                $display("[%0t ns] ❌ FAIL: Expected 0x%0h, got 0x%0h", $time, tx_data, rx_data);
            end

            // Small gap between tests
            #1000;
        end

        $display("=== UART Loopback Complete: %0d / %0d Passed ===", pass_count, NUM_TESTS);
        $finish;
    end

endmodule

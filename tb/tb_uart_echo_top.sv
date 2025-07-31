`timescale 1ns/1ps

module tb_uart32_7param_echo;

    parameter int CLK_FREQ_HZ = 100_000_000;
    parameter int BAUD_RATE   = 115200;
    localparam int NUM_WORDS = 7;

    logic clk = 0;
    logic rst_n = 0;

    logic        valid_in;
    logic [31:0] data_in;
    logic        ready_out;
    logic        tx;
    logic        tx_busy;

    logic        valid_out;
    logic [31:0] data_out;
    logic        rx;

    // Loopback connection
    assign rx = tx;

    // Clock generation
    always #5 clk = ~clk;

    // TX and RX modules
    uart_tx32 #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) tx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .data_in(data_in),
        .ready_out(ready_out),
        .tx(tx),
        .tx_busy(tx_busy)
    );

    uart_rx32 #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) rx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .valid_out(valid_out),
        .data_out(data_out)
    );

    // Data storage and test control
    logic [31:0] send_vals [NUM_WORDS];
    logic [31:0] recv_vals [NUM_WORDS];
    int i, errors;

    initial begin
        $display("=== Sending RX Words ===");
        clk = 0;
        rst_n = 0;
        valid_in = 0;
        data_in = 0;
        errors = 0;
        #100;
        rst_n = 1;
        #100;

        // Define 7 Q16.16 values
        send_vals[0] = 32'h00002710;  // 10.0
        send_vals[1] = 32'h00000032;  // 0.00048828125
        send_vals[2] = 32'h00640000;  // 100.0
        send_vals[3] = 32'h00640000;  // 100.0 again
        send_vals[4] = 32'h0000ccc0;  // ~0.8
        send_vals[5] = 32'h00033333;  // ~0.2
        send_vals[6] = 32'h00010000;  // 1.0

        // Send each word
        for (i = 0; i < NUM_WORDS; i++) begin
            wait (ready_out);
            @(posedge clk);
            data_in = send_vals[i];
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            $display("TX->FPGA: Word %0d = 0x%08h", i, send_vals[i]);

            wait (valid_out);
            @(posedge clk);
            recv_vals[i] = data_out;
            $display("FPGA->TX: Word %0d = 0x%08h", i, data_out);
        end

        // Comparison results
        $display("\n=== Echo Comparison Results ===");
        for (i = 0; i < NUM_WORDS; i++) begin
            if (recv_vals[i] !== send_vals[i]) begin
                $display("❌ Word %0d mismatch: Sent = 0x%08h | Got = 0x%08h",
                         i, send_vals[i], recv_vals[i]);
                errors++;
            end else begin
                $display("✅ Word %0d match: 0x%08h", i, send_vals[i]);
            end
        end

        if (errors == 0)
            $display("\n✅ All %0d words echoed back correctly!", NUM_WORDS);
        else
            $display("\n❌ %0d word(s) failed echo check.", errors);

        $finish;
    end

endmodule

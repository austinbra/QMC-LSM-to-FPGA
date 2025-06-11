`timescale 1ns / 1ps

module solveRegression3x3_tb;

    parameter WIDTH = 32;
    parameter MUL_LATENCY = 2;
    parameter DIV_LATENCY = 3;

    reg clk = 0, rst = 1, start = 0;

    reg signed [WIDTH-1:0] A_flat [0:8];
    reg signed [WIDTH-1:0] B_flat [0:2];

    wire done;
    wire signed [WIDTH-1:0] beta [0:2];

    // Clock generator
    always #5 clk = ~clk;

    solveRegression3x3 #(
        .WIDTH(WIDTH),
        .MUL_LATENCY(MUL_LATENCY),
        .DIV_LATENCY(DIV_LATENCY)
    ) dut (
        .clk(clk),
        .rst(rst),
        .start(start),
        .A_flat(A_flat),
        .B_flat(B_flat),
        .done(done),
        .beta(beta)
    );

    function signed [WIDTH-1:0] real_to_fixed(input real r);
        real scale = 2147483648.0;
        begin
            real_to_fixed = $rtoi(r * scale);
        end
    endfunction

    initial begin
        static int i = 0;
        // Reset pulse
        #10 rst = 0;

        // Load matrix A and B
        // A = [1 2 3; 2 4 6; 1 0 1], B = [14; 28; 6]
        A_flat[0] = real_to_fixed(1.0);
        A_flat[1] = real_to_fixed(2.0);
        A_flat[2] = real_to_fixed(3.0);
        A_flat[3] = real_to_fixed(2.0);
        A_flat[4] = real_to_fixed(4.0);
        A_flat[5] = real_to_fixed(6.0);
        A_flat[6] = real_to_fixed(1.0);
        A_flat[7] = real_to_fixed(0.0);
        A_flat[8] = real_to_fixed(1.0);

        B_flat[0] = real_to_fixed(14.0);
        B_flat[1] = real_to_fixed(28.0);
        B_flat[2] = real_to_fixed(6.0);

        // Start the computation
        #10 start = 1;
        #10 start = 0;

        // Wait for the computation to finish
        #10000;  // wait 10,000 ns (or whatever is enough to let FSM run)
        $display("Still waiting for DONE...");
        wait(done);

        // Add your own checks here to verify the correctness of beta
        // For example, you can compare the computed beta values with
        // the expected values using $display or other means.

        // Finish the simulation
        #10 $finish;
    end

endmodule

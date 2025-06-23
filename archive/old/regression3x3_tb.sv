`timescale 1ns / 1ps

module regression3x3_tb;

    parameter int WIDTH        = 32;
    parameter int MUL_LATENCY  = 1;
    parameter int DIV_LATENCY  = 1;

    // Clock, reset, start
    reg  clk   = 0;
    reg  rst_n   = 1;
    reg  start = 0;

    // Input matrices
    reg signed [WIDTH-1:0] A_flat [0:8];
    reg signed [WIDTH-1:0] B_flat [0:2];

    // Outputs
    wire done;
    wire signed [WIDTH-1:0] beta [0:2];

    // Clock generator: 100 MHz
    always #5 clk = ~clk;

    // DUT instantiation
    solveRegression3x3 #(
        .WIDTH(WIDTH),
        .MUL_LATENCY(MUL_LATENCY),
        .DIV_LATENCY(DIV_LATENCY)
    ) dut (
        .clk    (clk),
        .rst_n    (~rst_n),
        .start  (start),
        .A_flat (A_flat),
        .B_flat (B_flat),
        .done   (done),
        .beta   (beta)
    );

    // Convert a real (floating) to Q16.16 fixed-point
    function automatic signed [WIDTH-1:0] real_to_fixed(input real r);
        real scale;
        begin
            scale = 2.0**16;
            real_to_fixed = $rtoi(r * scale);
        end
    endfunction

    // Convert Q16.16 back to real for display/check
    function real fixed_to_real(input signed [WIDTH-1:0] x);
        real scale;
        begin
            scale = 2.0**16;
            fixed_to_real = x / (scale);
        end
    endfunction

    initial begin
        integer i;
        // Initialize reset
        #10 rst_n = 0;  // release reset after 10 ns
        #1  rst_n = 1;  // then assert reset to clear DUT
        #10 rst_n = 0;  // deassert for normal operation

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

        // Kick off the computation
        #20 start = 1;
        #10 start = 0;

        // Wait for done
        wait (done);
        #10; // let outputs settle

        // Display results
        $display("Computed beta (fixed): %0d, %0d, %0d",
                 beta[0], beta[1], beta[2]);
        $display("Computed beta (real) : %f, %f, %f",
                 fixed_to_real(beta[0]),
                 fixed_to_real(beta[1]),
                 fixed_to_real(beta[2]));

        // Expected solution: solving Ax = B gives x = [1;2;3]
        // Check with a simple pass/fail
        if ($abs(fixed_to_real(beta[0]) - 1.0) < 1e-3 &&
            $abs(fixed_to_real(beta[1]) - 2.0) < 1e-3 &&
            $abs(fixed_to_real(beta[2]) - 3.0) < 1e-3)
            $display("PASS: Regression result correct");
        else
            $display("FAIL: Regression result incorrect");

        #10 $finish;
    end

endmodule

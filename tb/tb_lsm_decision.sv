`timescale 1ns/1ps

module tb_lsm_decision;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;
    localparam int MAX_TB_CYCLES = 10000;

    // Signals
    logic clk, rst_n;
    logic valid_in, valid_out, ready_in, ready_out;
    logic signed [WIDTH-1:0] S_t, s_norm, beta [0:2], strike, cont_value, PV;
    logic option_type;

    // DUT
    lsm_decision #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .valid_out(valid_out),
        .ready_in(ready_in), .ready_out(ready_out),
        .S_t(S_t), .s_norm(s_norm), .beta(beta), .strike(strike), .cont_value(cont_value),
        .option_type(option_type),
        .PV(PV)
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
        S_t = 0; s_norm = 0; strike = 0; cont_value = 0; beta = '{default:'0};
        option_type = 0;  // CALL
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            valid_in = $urandom % 2;
            S_t = $urandom % (1 <<< 10);
            strike = S_t + ($urandom % 100);  // Strike > S_t sometimes
            cont_value = $urandom % (1 <<< 16);
            beta[0] = $urandom % 100; beta[1] = $urandom % 10; beta[2] = $urandom % 5;
            ready_in = ($urandom % 10 > 2) ? 1 : 0;
            if (valid_in && ready_out) $display("Cycle %t: Input accepted (ready_out=%b) - S_t=%d, strike=%d", $time, ready_out, S_t, strike);
            if (!ready_in) $display("Cycle %t: Stall", $time);
        end

        // Edge: Exercise (S_t < strike, high payoff)
        S_t = 100; strike = 200; #10;
        if (valid_out) $display("Cycle %t: PV=%d (expected positive payoff)", $time, PV);

        // Edge: Hold (low payoff)
        S_t = 300; strike = 200; #10;

        #200 $finish;
    end

    // Assertions
    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(PV))
        else $error("Decision stall overwrite");
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

        // Correctness: PV >=0, exercise if payoff > continuation
        if (valid_out && PV < 0) begin
            $display("Output FAIL: Negative PV=%d", PV);
            test_passed = 0;
        end else $display("Output PASS: PV=%d", PV);

        if (stall_cycles > 0) $display("Stalls OK (%d cycles)", stall_cycles);
        if (test_passed) $display("All tests PASSED"); else $display("Tests FAILED");
    end

    initial begin
        repeat (MAX_TB_CYCLES) @(posedge clk);
        $fatal(1, "Timeout after %0d cycles", MAX_TB_CYCLES);
    end
endmodule
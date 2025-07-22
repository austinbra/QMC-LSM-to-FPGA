`timescale 1ns/1ps

module tb_lsm_decision;

    // Parameters
    parameter WIDTH = 32;
    parameter QINT = 16;
    parameter QFRAC = 16;

    // Signals
    logic clk, rst_n;
    logic valid_in, valid_out, ready_in, ready_out;
    logic signed [WIDTH-1:0] S_t, beta [0:2], strike, disc, PV;

    // DUT
    lsm_decision #(
        .WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC)
    ) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_in(valid_in), .valid_out(valid_out),
        .ready_in(ready_in), .ready_out(ready_out),
        .S_t(S_t), .beta(beta), .strike(strike), .disc(disc),
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
        S_t = 0; strike = 0; disc = (1 <<< QFRAC); beta = '{default:'0};
        #20 rst_n = 1;
        $display("Cycle %t: Reset deasserted", $time);

        // 10 transactions
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            valid_in = $urandom % 2;
            S_t = $urandom % (1 <<< 10);
            strike = S_t + ($urandom % 100);  // Strike > S_t sometimes
            disc = (1 <<< QFRAC) - ($urandom % 100);  // <1.0
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
    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(PV)) else $error("Decision stall overwrite");
        assert (PV > 0) else $error("Exercise case didn't yield positive PV");
    end

endmodule
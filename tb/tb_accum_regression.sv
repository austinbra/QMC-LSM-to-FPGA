`default_nettype none
timeunit 1ns; timeprecision 1ps;

module tb_accum_regression;
  // Clock/reset
  logic clk   = 1'b0;
  logic rst_n = 1'b0;
  always #5 clk = ~clk; // 100 MHz

  // TB parameters
  localparam int WIDTH   = fpga_cfg_pkg::FP_WIDTH;
  localparam int QFRAC   = fpga_cfg_pkg::FP_QFRAC;
  localparam int QINT    = fpga_cfg_pkg::FP_QINT;
  localparam int N_S     = 16;   // small for TB speed
  localparam int TOL_LSB = 200;  // tolerance in LSB
  localparam int MAX_WAIT_CYCLES = 20000;
  localparam int MAX_TB_CYCLES   = 100000;

  // DUT I/O
  logic                     valid_in;
  logic                     ready_out;
  logic                     valid_out;
  logic                     ready_in = 1'b1;  // always ready downstream
  logic signed [WIDTH-1:0]  x_in, y_in;
  logic signed [WIDTH-1:0]  beta [0:2];

  // DUT
  accumulator #(
    .WIDTH     (WIDTH),
    .QINT      (QINT),
    .QFRAC     (QFRAC),
    .N_SAMPLES (N_S)
  ) dut (
    .clk            (clk),
    .rst_n          (rst_n),
    .valid_in       (valid_in),
    .ready_out      (ready_out),
    .valid_out      (valid_out),
    .ready_in       (ready_in),
    .x_in           (x_in),
    .y_in           (y_in),
    .n_samples_cfg  ('0),
    .beta           (beta),
    .regression_singular()
  );

  // -------------------------
  // Fixed-point helpers
  // -------------------------
  function automatic logic signed [WIDTH-1:0] to_fx(input real r);
    logic signed [WIDTH-1:0] ret;
    longint s;
    real scaled;
    begin
      scaled = r * real'(1 <<< QFRAC);
      if (scaled >= 0.0) s = longint'(scaled + 0.5);
      else               s = longint'(scaled - 0.5);

      if (s >  ( (1 <<< (WIDTH-1)) - 1)) ret = ( (1 <<< (WIDTH-1)) - 1);
      else if (s < -( (1 <<< (WIDTH-1))     )) ret = -(1 <<< (WIDTH-1));
      else ret = $signed(s[WIDTH-1:0]);

      return ret;
    end
  endfunction

  function automatic real fx_to_real(input logic signed [WIDTH-1:0] fx);
    return fx / real'(1 <<< QFRAC);
  endfunction

  // -------------------------
  // Send one sample (holds valid until accepted)
  // -------------------------
  task automatic send_sample(input logic signed [WIDTH-1:0] x,
                             input logic signed [WIDTH-1:0] y);
    int waited;
    begin
      @(posedge clk);
      valid_in <= 1'b1;
      x_in     <= x;
      y_in     <= y;
      // Keep asserting until accepted
      waited = 0;
      while (!ready_out && waited < MAX_WAIT_CYCLES) begin
        @(posedge clk);
        waited++;
      end
      if (!ready_out) $fatal(1, "send_sample timeout waiting for ready_out");
      @(posedge clk);
      valid_in <= 1'b0;
      x_in     <= '0;
      y_in     <= '0;
    end
  endtask

  // -------------------------
  // Wait for beta output
  // -------------------------
  task automatic wait_for_result(output logic signed [WIDTH-1:0] b0,
                                 output logic signed [WIDTH-1:0] b1,
                                 output logic signed [WIDTH-1:0] b2);
    int waited;
    begin
      waited = 0;
      while (!(valid_out && ready_in) && waited < MAX_WAIT_CYCLES) begin
        @(posedge clk);
        waited++;
      end
      if (!(valid_out && ready_in)) $fatal(1, "wait_for_result timeout waiting for valid_out");
      b0 = beta[0];
      b1 = beta[1];
      b2 = beta[2];
    end
  endtask

  // -------------------------
  // Compare within tolerance in LSBs
  // -------------------------
  task automatic check_close(input string name,
                             input logic signed [WIDTH-1:0] got,
                             input logic signed [WIDTH-1:0] exp_v,
                             input int tol);
    int diff;
    begin
      diff = $signed(got) - $signed(exp_v);
      if (diff < 0) diff = -diff;
      if (diff > tol) begin
        $display("[%0t] ERROR %s: got=%0f expect=%0f (|diff|=%0d LSB > %0d)",
                 $time, name, fx_to_real(got), fx_to_real(exp_v), diff, tol);
        $fatal(1);
      end else begin
        $display("[%0t] PASS  %s: got=%0f expect=%0f (|diff|=%0d LSB <= %0d)",
                 $time, name, fx_to_real(got), fx_to_real(exp_v), diff, tol);
      end
    end
  endtask

  // -------------------------
  // Scenario 1: Non-singular (recover known β)
  // -------------------------
  task automatic scenario_nonsingular;
    real rb0;
    real rb1;
    real rb2;
    logic signed [WIDTH-1:0] b0_fx;
    logic signed [WIDTH-1:0] b1_fx;
    logic signed [WIDTH-1:0] b2_fx;
    logic signed [WIDTH-1:0] out_b0, out_b1, out_b2;
    int k;
    real rx, ry;
    begin
      $display("\n--- Scenario 1: Non-singular β recovery ---");
      rb0  = 1.25;
      rb1  = -0.50;
      rb2  = 0.25;
      b0_fx = to_fx(rb0);
      b1_fx = to_fx(rb1);
      b2_fx = to_fx(rb2);

      for (k = 1; k <= N_S; k++) begin
        rx = k;
        ry = rb0 + rb1*rx + rb2*rx*rx;
        send_sample(to_fx(rx), to_fx(ry));
      end

      wait_for_result(out_b0, out_b1, out_b2);
      check_close("beta0", out_b0, b0_fx, TOL_LSB);
      check_close("beta1", out_b1, b1_fx, TOL_LSB);
      check_close("beta2", out_b2, b2_fx, TOL_LSB);
    end
  endtask

  // -------------------------
  // Scenario 2: Singular (fallback → mean payoff)
  // -------------------------
  task automatic scenario_singular;
    logic signed [WIDTH-1:0] out_b0, out_b1, out_b2;
    logic signed [WIDTH-1:0] mean_fx;
    real sumy;
    int k;
    real ry;
    begin
      $display("\n--- Scenario 2: Singular → fallback mean ---");
      sumy = 0.0;
      for (k = 0; k < N_S; k++) begin
        ry = 0.25 * k + 0.75; // arbitrary
        sumy += ry;
        send_sample(to_fx(2.0), to_fx(ry)); // constant x ⇒ singular
      end
      wait_for_result(out_b0, out_b1, out_b2);
      mean_fx = to_fx(sumy / N_S);
      check_close("beta0(mean)", out_b0, mean_fx, TOL_LSB);
      check_close("beta1==0",   out_b1, to_fx(0.0), TOL_LSB);
      check_close("beta2==0",   out_b2, to_fx(0.0), TOL_LSB);
    end
  endtask

  // -------------------------
  // Reset and run
  // -------------------------
  initial begin
    valid_in = 1'b0;
    x_in     = '0;
    y_in     = '0;

    repeat (5) @(posedge clk);
    rst_n = 1'b1;
    repeat (2) @(posedge clk);

    scenario_nonsingular();
    scenario_singular();

    $display("\nAll tests PASSED.");
    #20 $finish;
  end

`ifdef TB_ACCUM_REG_DEBUG
  initial begin
    $timeformat(-9, 3, " ns", 10);
    $display("time      rst v_in r_out v_out r_in   cnt_launch cnt_done start_s solver_done acc_state   sol_vin sol_rin sol_rout sol_vout sing_err   x_in(hex)   y_in(hex)   beta0(hex)  beta1(hex)  beta2(hex)");
    forever begin
      @(posedge clk);
      $display("%t  %0d   %0d    %0d     %0d    %0d    %0d        %0d        %0d       %0d         %0d       %0d       %0d       %0d       %0d       %0d    %08h   %08h   %08h   %08h   %08h",
               $realtime,
               rst_n, valid_in, ready_out, valid_out, ready_in,
               dut.cnt_launch, dut.cnt_done,
               dut.start_solver, dut.solver_done, dut.state,
               dut.solver.valid_in, dut.solver.ready_in,
               dut.solver.ready_out, dut.solver.valid_out,
               dut.singular_err,
               x_in, y_in, beta[0], beta[1], beta[2]);
    end
  end
`endif

  initial begin
    repeat (MAX_TB_CYCLES) @(posedge clk);
    $fatal(1, "Timeout after %0d cycles", MAX_TB_CYCLES);
  end

endmodule

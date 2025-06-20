// fxDiv.sv
// Fixed-point divider with QINT.QFRAC format,
// pipelined for DIV_LATENCY cycles, start/done handshake.

module fxDiv #(
  parameter int WIDTH    = 32,                 // total bits of Q-format
  parameter int QINT     = 16,                 // integer bits
  parameter int QFRAC    = WIDTH - QINT,       // fractional bits
  parameter int LATENCY  = 3                   // pipeline depth
)(
  input  logic                  clk,
  input  logic                  rst_n,        // active-low reset
  input  logic                  start,        // pulse to launch a divide
  input  logic signed [WIDTH-1:0] numerator,   // Q-format dividend
  input  logic signed [WIDTH-1:0] denominator, // Q-format divisor
  output logic signed [WIDTH-1:0] result,      // Q-format quotient
  output logic                  done          // pulses true when result is valid
);

  // Extend to full width for shift/divide
  localparam int FULLW = WIDTH + QFRAC;

  // sign-extended operands
  logic signed [FULLW-1:0] num_ext, den_ext;
  always_comb begin
    num_ext = {{QFRAC{numerator[WIDTH-1]}}, numerator};
    den_ext = {{QFRAC{denominator[WIDTH-1]}}, denominator};
  end

  // Compute raw FULLW-bit Q-format result, combinationally
  logic signed [FULLW-1:0] raw_div;
  always_comb begin
    // scale up by QFRAC, then integer divide
    raw_div = (num_ext <<< QFRAC) / den_ext;
  end

  // Pipeline registers for raw_div
  logic signed [FULLW-1:0] pipe_div [0:LATENCY];

  // Validity shift register
  logic valid_pipe [0:LATENCY];

  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // reset pipeline and flags
      for (i = 0; i <= LATENCY; i = i + 1) begin
        pipe_div[i]  <= '0;
        valid_pipe[i]<= 1'b0;
      end
      result <= '0;
      done   <= 1'b0;
    end else begin
      // shift the valid bit
      valid_pipe[0] <= start;
      for (i = 1; i <= LATENCY; i = i + 1)
        valid_pipe[i] <= valid_pipe[i-1];

      // inject raw_div into stage 0 only when start
      if (start)
        pipe_div[0] <= raw_div;
      else
        pipe_div[0] <= pipe_div[0];  // hold previous to keep simulation clean

      // shift the data pipeline
      for (i = 1; i <= LATENCY; i = i + 1)
        pipe_div[i] <= pipe_div[i-1];

      // done pulses when the valid bit emerges at the last stage
      done <= valid_pipe[LATENCY];

      // update result only when that valid arrives
      if (valid_pipe[LATENCY])
        result <= pipe_div[LATENCY][FULLW-1 -: WIDTH];
    end
  end

endmodule

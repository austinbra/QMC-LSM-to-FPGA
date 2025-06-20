// fxMul.sv
// Fixed-point multiplier with QINT.QFRAC format,
// pipelined for MUL_LATENCY cycles, start/done handshake.

module fxMul #(
  parameter int WIDTH    = 32,                 // total bits (signed)
  parameter int QINT     = 16,                 // integer bits
  parameter int QFRAC    = WIDTH - QINT,       // fractional bits
  parameter int LATENCY  = 2                   // pipeline depth
)(
  input  logic                  clk,
  input  logic                  rst_n,        // active-low reset
  input  logic                  start,        // pulse to launch a multiply
  input  logic signed [WIDTH-1:0] a,           // Q-format operand A
  input  logic signed [WIDTH-1:0] b,           // Q-format operand B
  output logic signed [WIDTH-1:0] result,      // Q-format product
  output logic                  done          // pulses true when result is valid
);

  // Wide raw product
  localparam int RAWW = 2*WIDTH;

  // compute raw product combinationally
  logic signed [RAWW-1:0] raw_mul;
  always_comb begin
    raw_mul = $signed(a) * $signed(b);
  end

  // pipeline registers for raw_mul
  logic signed [RAWW-1:0] pipe_mul [0:LATENCY];

  // validity shift register
  logic valid_pipe [0:LATENCY];

  integer i;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // reset all
      for (i = 0; i <= LATENCY; i = i + 1) begin
        pipe_mul[i]  <= '0;
        valid_pipe[i]<= 1'b0;
      end
      result <= '0;
      done   <= 1'b0;
    end else begin
      // shift valid bit
      valid_pipe[0] <= start;
      for (i = 1; i <= LATENCY; i = i + 1)
        valid_pipe[i] <= valid_pipe[i-1];

      // inject raw_mul on start
      if (start)
        pipe_mul[0] <= raw_mul;
      else
        pipe_mul[0] <= pipe_mul[0];

      // shift pipeline
      for (i = 1; i <= LATENCY; i = i + 1)
        pipe_mul[i] <= pipe_mul[i-1];

      // done when valid emerges
      done <= valid_pipe[LATENCY];

      // extract Q-format result when ready
      if (valid_pipe[LATENCY])
        result <= pipe_mul[LATENCY][QFRAC +: WIDTH];
    end
  end

endmodule

module fxMul_always #(
  parameter WIDTH=32, QINT=16, QFRAC=WIDTH-QINT, LATENCY=2
)(
  input  logic clk, rst_n,
  input  logic signed [WIDTH-1:0] a, b,
  output logic signed [WIDTH-1:0] result
);
  logic done_dummy;
  fxMul #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(LATENCY)) core(
    .clk(clk), .rst_n(rst_n),
    .start(1'b1), // always asserted
    .a(a),
    .b(b),
    .result(result),
    .done(done_dummy) // ignored
  );
endmodule

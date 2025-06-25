module fxDiv_always #(
    parameter int WIDTH = 32,
    parameter int QINT = 16,
    parameter int QFRAC = WIDTH - QINT,
    parameter int LATENCY = 3
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,     
    input  logic signed [WIDTH-1:0] numerator,
    input  logic signed [WIDTH-1:0] denominator,
    output logic valid_out,
    output logic signed [WIDTH-1:0] result
);
    logic core_valid_out;
    always_ff @(posedge clk)
        if (valid_in) $display("DIV: %0t  num=%0d  den=%0d", $time, numerator, denominator);

    fxDiv #(.WIDTH(WIDTH), .QINT(QINT), .QFRAC(QFRAC), .LATENCY(LATENCY)) core(
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),// always asserted
        .numerator(numerator),
        .denominator(denominator),
        .result(result),
        .valid_out(core_valid_out) // ignored
    );
    assign valid_out = core_valid_out;
endmodule

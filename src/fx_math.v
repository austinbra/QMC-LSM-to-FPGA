// fixed point divide and multiply in Q11.21 format

`timescale 1ns / 1ps

module fxDiv #(parameter WIDTH = 32, parameter FRAC_BITS = 21)(
    input signed [WIDTH-1:0] numerator,
    input signed [WIDTH-1:0] denominator,
    output signed [WIDTH-1:0] result
);
    wire signed [2*WIDTH-1:0] shifted_numerator;
    assign shifted_numerator = numerator <<< FRAC_BITS;
    assign result = shifted_numerator / denominator;
endmodule

module fxMul #(parameter WIDTH = 32, parameter FRAC_BITS = 21)(
    input signed [WIDTH-1:0] a,
    input signed [WIDTH-1:0] b,
    output signed [WIDTH-1:0] result
);
    wire signed [2*WIDTH-1:0] mult_result;
    assign mult_result = a * b;
    assign result = mult_result >>> FRAC_BITS;
endmodule
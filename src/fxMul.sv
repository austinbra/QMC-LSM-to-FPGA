module fxMul #(
    parameter WIDTH = 32
)(
    input logic clk,
    input logic rst,
    input logic start,
    input logic signed [WIDTH-1:0] a,
    input logic signed [WIDTH-1:0] b,
    output logic done,
    output logic signed [WIDTH-1:0] result
);


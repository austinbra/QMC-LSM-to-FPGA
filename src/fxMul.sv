module fxMul #(
    parameter WIDTH = 32, //data width
    parameter QFRAC = 16 //fractional bits
)(
    input logic                     clk,
    input  logic                    rst_n,  // active‐low reset
    input logic signed [WIDTH-1:0]  a,
    input logic signed [WIDTH-1:0]  b,
    output logic signed [WIDTH-1:0] result
);
    logic signed [2*WIDTH-1:0]  prod;

    wire [QFRAC-1:0]               _unused_low  = prod[QFRAC-1:0];
    wire [2*WIDTH-1 : QFRAC+WIDTH] _unused_high = prod[2*WIDTH-1 : QFRAC+WIDTH];


    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            prod   <= '0;
            result <= '0;
        end else begin
            prod   <= $signed(a) * $signed(b);
            // grab bits [QFRAC + WIDTH-1 : QFRAC]
            result <= prod[QFRAC +: WIDTH];
        end
    end



endmodule

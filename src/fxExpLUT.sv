module fxExpLUT #(
    parameter WIDTH = 32,
    parameter QINT = 16
    parameter QFRAC = WIDTH - QINT,
    parameter LUT_BITS = 10
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic signed [WIDTH-1:0] x,
    output logic signed [WIDTH-1:0] exp_result,
    output logic valid_out
);

    // ROM for exp LUT
    localparam LUT_SIZE = 1 << LUT_BITS;
    logic [WIDTH-1:0] exp_lut [0:LUT_SIZE-1];
    initial $readmemh("gen/exp_lut_1024_q16.mem", exp_lut);

    // Index calculation: take LUT_BITS MSBs of fractional part
    logic [LUT_BITS-1:0] lut_index;
    assign lut_index = x[QFRAC + LUT_BITS - 1 : QFRAC];

    // Output register
    logic [WIDTH-1:0] result_reg;
    logic             valid_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result_reg <= '0;
            valid_reg  <= 1'b0;
        end else begin
            if (valid_in) begin
                result_reg <= exp_lut[lut_index];
                valid_reg  <= 1'b1;
            end else begin
                valid_reg  <= 1'b0;
            end
        end
    end

    assign exp_result = result_reg;
    assign valid_out  = valid_reg;

endmodule

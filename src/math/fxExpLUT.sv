module fxExpLUT #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS = fpga_cfg_pkg::FP_LUT_BITS
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic signed [WIDTH-1:0] a,
    output logic signed [WIDTH-1:0] result,
    output logic valid_out
);

    // ROM for exp LUT
    localparam LUT_SIZE = 1 << LUT_BITS;
    logic [WIDTH-1:0] exp_lut [0:LUT_SIZE-1];
    initial $readmemh("../gen/exp_lut_1024.mem", exp_lut);

    // Index calculation: take LUT_BITS MSBs of fractional part
    logic [LUT_BITS-1:0] lut_index;
    assign lut_index = a[QFRAC + LUT_BITS - 1 : QFRAC];

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

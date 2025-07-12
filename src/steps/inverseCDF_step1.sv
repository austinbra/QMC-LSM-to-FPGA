// Convert sobol sequence number to x ∈ (0,0.5]
module inverseCDF_step1 #(
    parameter WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter QINT = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC
)(
    input logic clk,
    input logic rst_n,

    input logic valid_in,
    input  logic ready_in,//downstream ready

    input logic signed [WIDTH-1:0] u,   // sobol number in Q16.16

    output logic valid_out,
    output logic ready_out,//upstream ready

    output logic [WIDTH-1:0] x,         // Q16.16 value in (0, 0.5]
    output logic negate                 // If 1, final z-score should be negated
);

    localparam signed [WIDTH-1:0] HALF = 'sd32768; // 0.5

    logic [WIDTH-1:0] x_reg;
    logic negate_reg, valid_reg;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            x <= '0;
            negate_reg <= '0;
            valid_reg <= '0;
        end else begin
            if (valid_in && ready_out) begin
                if (u < HALF) begin
                    x_reg <= u;
                    negate_reg <= 1'b0;
                end else begin
                    x_reg <= (1'sd1 << QFRAC) - u;
                    negate_reg <= 1'b1;
                end
                valid_reg <= 1'b1;
            end else if (ready_in && valid_reg) begin
                valid_reg <= '0;
            end
        end
    end

    assign x            = x_reg;
    assign negate       = negate_reg;
    assign valid_out    = valid_reg;
    assign ready_out    = ~valid_reg;

endmodule
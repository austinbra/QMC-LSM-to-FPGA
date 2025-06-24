// Convert sobol sequence number to x ∈ (0,0.5]
module inverseCDF_step1 #(
    parameter WIDTH = 32,
    parameter QINT = 16,
    parameter int QFRAC = WIDTH - QINT
)(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic signed [WIDTH-1:0] u,   // sobol number in Q16.16

    output logic valid_out,
    output logic [WIDTH-1:0] x,         // Q16.16 value in (0, 0.5]
    output logic negate                 // If 1, final z-score should be negated
);

    // constant for 0.5 in Q16.16
    localparam signed [WIDTH-1:0] HALF = 32'sd32768; // 0.5 in Q16.16

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            x <= 0;
            negate <= 0;
            valid_out <= 0;
        end else begin
            valid_out <= valid_in;
            if (u < HALF) begin
                x <= u;
                negate <= 1;
            end else begin
                x <= HALF - (u - HALF); // Same as 1 - u
                negate <= 0;
            end
        end
    end

endmodule
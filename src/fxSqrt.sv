//-----------------------------------------------------------
// approximates square root using newton-raphson algorithm
//-----------------------------------------------------------
module fxSqrt #(
    parameter WIDTH = 32,
    parameter FRAC = 16,
    parameter ITERATIONS = 3
)(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [WIDTH-1:0] y,      // input Q16.16

    output logic valid_out,
    output logic [WIDTH-1:0] sqrt_out
);

    // internal state
    logic [WIDTH-1:0] x_curr, x_next;
    logic [WIDTH-1:0] div_result;
    logic [1:0] iter;
    logic busy;

    // instantiate division module
    fxDiv #(WIDTH, FRAC) div (
        .clk(clk), .rst_n(rst_n),
        .numerator(y),
        .denominator(x_curr),
        .result(div_result)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            x_curr <= 0;
            iter <= 0;
            busy <= 0;
            sqrt_out <= =0;
            valid_out <= 0;
        end else begin
            if (valid_in && !busy) begin
                // start new iteration
                x_curr <= y >> 1;       // initial guess: y / 2
                iter <= 0;
                busy <= 1;
                valid_out <= 0;
            end else if (busy) begin
                // Newton-Raphson iteration: x_next = 0.5 * (x + y/x)
                x_next <= (x_curr + div_result) >> 1;
                x_curr <= x_next;
                iter <= iter + 1;

                if (iter == ITERATIONS - 1) begin
                    sqrt_out <= x_next;
                    valid_out <= 1;
                    busy <= 0;
                end else begin
                    valid_out <= 0;
                end
            end else begin
                valid_out <= 0;
            end
        end
    end

endmodule
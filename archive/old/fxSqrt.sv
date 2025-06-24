// approximates square root using newton-raphson algorithm
module fxSqrt #(
    parameter WIDTH = 32,
    parameter QINT = 16,
    parameter FRAC = WIDTH - QINT,
    parameter LATENCY = 3
)(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [WIDTH-1:0] a,

    output logic valid_out,
    output logic [WIDTH-1:0] sqrt_out
);

    logic [WIDTH-1:0] x_curr;
    logic [WIDTH-1:0] div_result;
    logic [3:0] cycle_count;  
    logic [1:0] iteration;    // Track Newton-Raphson iterations
    logic busy;

    // instantiate division module
    fxDiv_always #(WIDTH, QINT) div (
        .clk(clk),
        .rst_n(rst_n),
        .num(y),
        .denom(x_curr),
        .result(div_result)
    );

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            x_curr <= 0;
            cycle_count <= 0;
            iteration <= 0;
            busy <= 0;
            sqrt_out <= 0;
            valid_out <= 0;
        end else begin
            if (valid_in && !busy) begin
                // start new computation
                x_curr <= y >> 1;       // initial guess: y / 2
                cycle_count <= 0;
                iteration <= 0;
                busy <= 1;
                valid_out <= 0;
            end else if (busy) begin
                cycle_count <= cycle_count + 1;
                
                // Wait for division pipeline (3 cycles) then update
                if (cycle_count >= 3) begin
                    // Newton-Raphson iteration: x_curr = 0.5 * (x + y/x)
                    x_curr <= (x_curr + div_result) >> 1;
                    
                    iteration <= iteration + 1;
                    cycle_count <= 0;  // Reset for next iteration
                    
                    // Do 2 iterations for better accuracy
                    if (iteration >= 1) begin
                        sqrt_out <= (x_curr + div_result) >> 1;
                        valid_out <= 1;
                        busy <= 0;
                    end
                end else begin
                    valid_out <= 0;
                end
            end else begin
                valid_out <= 0;
            end
        end
    end

endmodule
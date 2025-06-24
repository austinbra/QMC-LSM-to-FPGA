// approximates square root using newton-raphson algorithm
module fxSqrt #(
    parameter WIDTH = 32,
    parameter QINT = 16,
    parameter LATENCY = 4
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic [WIDTH-1:0] y,
    output logic valid_out,
    output logic [WIDTH-1:0] sqrt_out
);

    logic [WIDTH-1:0] pipe_x   [0:LATENCY];
    logic [WIDTH-1:0] pipe_div [0:LATENCY];
    logic vpipe [0:LATENCY];

    fxDiv_always #(WIDTH, QINT, QFRAC) div (
        .clk(clk),
        .rst_n(rst_n),
        .num(y),
        .denom(pipe_x[0]),
        .result(pipe_div[0])
    );

    // init x_curr guess on pipe_x[0]
    // shift both x and div through the pipeline
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i <= LATENCY; i++) begin
                pipe_x[i]   <= 0;
                pipe_div[i] <= 0;
                vpipe[i]    <= 0;
            end
        end else begin
            // stage 0 loads init guess when valid_in
            vpipe[0]  <= valid_in;
            pipe_x[0] <= valid_in ? (y >> 1) : pipe_x[0]; // initial guess

            // shift everything in pipeline
            for (int i = 1; i <= LATENCY; ++i) begin
                vpipe[i] <= vpipe[i-1];
                pipe_x[i] <= vpipe[i-1] ? ((pipe_x[i-1] + pipe_div[i-1]) >> 1) : pipe_x[i];
                pipe_div[i] <= pipe_div[i-1];
            end
        end
    end

    assign sqrt_out  = pipe_x[LATENCY];
    assign valid_out = vpipe[LATENCY];
endmodule

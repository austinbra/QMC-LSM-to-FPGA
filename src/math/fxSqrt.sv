// approximates square root using newton-raphson algorithm
module fxSqrt #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT = fpga_cfg_pkg::FP_QINT,
    parameter int LATENCY = 4
)(
    input  logic clk,
    input  logic rst_n,
    input  logic valid_in,
    input  logic [WIDTH-1:0] a,
    output logic valid_out,
    output logic [WIDTH-1:0] sqrt_out
);

    logic [WIDTH-1:0] pipe_x   [0:LATENCY];
    logic [WIDTH-1:0] pipe_div [0:LATENCY];
    logic vpipe [0:LATENCY];

    logic temp;
    fxDiv #(WIDTH, QINT, QFRAC) div (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .num(a),
        .denom(pipe_x[0]),
        .valid_out(temp),
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
            pipe_x[0] <= valid_in ? (a >> 1) : pipe_x[0]; // initial guess

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

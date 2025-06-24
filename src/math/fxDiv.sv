// fxDiv.sv
// Fixed-point divider with QINT.QFRAC format,
// pipelined for DIV_LATENCY cycles, valid_in/valid_out handshake.

module fxDiv #(
    parameter int WIDTH    = 32,                 
    parameter int QINT     = 16,                 
    parameter int QFRAC    = WIDTH - QINT,       
    parameter int LATENCY  = 3                   // pipeline depth
)(
    input  logic                  clk,
    input  logic                  rst_n,       
    input  logic                  valid_in,       
    input  logic signed [WIDTH-1:0] numerator,   
    input  logic signed [WIDTH-1:0] denominator,
    output logic signed [WIDTH-1:0] result,     
    output logic                  valid_out          // pulses true when result is valid
);

    localparam int FULLW = WIDTH + QFRAC;
    logic signed [FULLW-1:0] num_ext, den_ext;

    always_comb begin
        num_ext = {{QFRAC{numerator[WIDTH-1]}}, numerator};
        den_ext = {{QFRAC{denominator[WIDTH-1]}}, denominator};
    end

    logic signed [FULLW-1:0] raw_div;
    always_comb begin
        // scale up by QFRAC, then integer divide
        raw_div = (num_ext <<< QFRAC) / den_ext;
    end

    logic signed [FULLW-1:0] pipe_div [0:LATENCY];
    logic valid_pipe [0:LATENCY];

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i <= LATENCY; i = i + 1) begin
                pipe_div[i]  <= '0;
                valid_pipe[i]<= 1'b0;
            end
            result <= '0;
            valid_out   <= 1'b0;

        end else begin
            valid_pipe[0] <= valid_in;
            for (i = 1; i <= LATENCY; i = i + 1)
                valid_pipe[i] <= valid_pipe[i-1];

            if (valid_in)
                pipe_div[0] <= raw_div;
            else
                pipe_div[0] <= pipe_div[0];  // hold previous to keep simulation clean

            for (i = 1; i <= LATENCY; i = i + 1)
                pipe_div[i] <= pipe_div[i-1];

            valid_out <= valid_pipe[LATENCY];
            if (valid_pipe[LATENCY])
                result <= pipe_div[LATENCY][FULLW-1 -: WIDTH];
        end
    end

endmodule

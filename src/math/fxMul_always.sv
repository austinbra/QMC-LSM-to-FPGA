module fxMul_always #(
    parameter int WIDTH = 32,                
    parameter int QINT  = 16,                
    parameter int QFRAC = WIDTH - QINT,   
    parameter int LATENCY = 1                 
)(
    input  logic clk,
    input  logic rst_n,        
    input  logic valid_in,     
    input  logic signed [WIDTH-1:0] a,         
    input  logic signed [WIDTH-1:0] b,          
    output logic valid_out,
    output logic signed [WIDTH-1:0] result    
         
);

    // Double-width raw product
    localparam int RAWW = 2 * WIDTH;
    logic signed [RAWW-1:0] raw_mul;

    // guess multiply
    always_comb raw_mul = $signed(a) * $signed(b);

    logic signed [RAWW-1:0] pipe_mul  [0:LATENCY];
    logic valid_pipe[0:LATENCY];

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i <= LATENCY; ++i) begin
                pipe_mul[i]   <= '0;
                valid_pipe[i] <= 1'b0;
            end
            result    <= '0;
            valid_out <= 1'b0;

        end else begin
            valid_pipe[0] <= valid_in;
            for (i = 1; i <= LATENCY; ++i)
                valid_pipe[i] <= valid_pipe[i-1];

            if (valid_in)
                pipe_mul[0] <= raw_mul;

            for (i = 1; i <= LATENCY; ++i)
                pipe_mul[i] <= pipe_mul[i-1];

            valid_out <= valid_pipe[LATENCY];
            if (valid_pipe[LATENCY])
                result <= pipe_mul[LATENCY][QFRAC +: WIDTH];
        end
    end

endmodule

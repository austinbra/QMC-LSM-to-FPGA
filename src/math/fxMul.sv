// fxMul.sv
// Fixed-point multiplier with QINT.QFRAC format,
// pipelined for MUL_LATENCY cycles, valid_in/valid_out handshake.

module fxMul #(
    parameter int WIDTH    = 32,                 // total bits (signed)
    parameter int QINT     = 16,                 // integer bits
    parameter int QFRAC    = WIDTH - QINT,       // fractional bits
    parameter int LATENCY  = 2                   // pipeline depth
)(
    input  logic                  clk,
    input  logic                  rst_n,        // active-low reset
    input  logic                  valid_in,        // pulse to launch a multiply
    input  logic signed [WIDTH-1:0] a,           // Q-format operand A
    input  logic signed [WIDTH-1:0] b,           // Q-format operand B
    output logic signed [WIDTH-1:0] result,      // Q-format product
    output logic                  valid_out          // pulses true when result is valid
);

    // ------------------------------------------------------------
	// helper: return 1 if the upper bits are just sign-extension
	// ------------------------------------------------------------
	localparam int UBIT = WIDTH - QFRAC;
    function automatic bit fits_Q16_16
        (input logic signed [2*WIDTH-1:0] x);
        logic signed [UBIT-1:0] upper_bits;
        logic signed [UBIT-1:0] sign_bits;
        begin
            upper_bits = x[2*WIDTH-1 : WIDTH+QFRAC];
            sign_bits  = { UBIT{ x[WIDTH+QFRAC-1] } };
            fits_Q16_16 = (upper_bits == sign_bits);
        end
    endfunction

    localparam int RAWW = 2*WIDTH;
    logic signed [RAWW-1:0] raw_mul;

    always_comb begin
        raw_mul = $signed(a) * $signed(b);
        assert (fits_Q16_16(raw_mul))
    		else $error("fxMul overflow: a=%0d b=%0d at %0t", a, b, $time);
    end

    logic signed [RAWW-1:0] pipe_mul [0:LATENCY];
    logic valid_pipe [0:LATENCY];

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i <= LATENCY; i = i + 1) begin
                pipe_mul[i]  <= '0;
                valid_pipe[i]<= 1'b0;
            end
            result <= '0;
            valid_out   <= 1'b0;
        end else begin

            valid_pipe[0] <= valid_in;
            for (i = 1; i <= LATENCY; i = i + 1)
                valid_pipe[i] <= valid_pipe[i-1];

            // inject raw_mul on valid_in
            if (valid_in)
                pipe_mul[0] <= raw_mul;
            else
                pipe_mul[0] <= pipe_mul[0];

            // shift pipeline
            for (i = 1; i <= LATENCY; i = i + 1)
                pipe_mul[i] <= pipe_mul[i-1];

            valid_out <= valid_pipe[LATENCY];
            if (valid_pipe[LATENCY])
                result <= pipe_mul[LATENCY][QFRAC +: WIDTH];
        end
    end

endmodule

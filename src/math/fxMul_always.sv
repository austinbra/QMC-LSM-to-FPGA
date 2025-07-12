//Streaming / one-per-path work -> fxMul_always (handshake)

module fxMul_always #(
    parameter int WIDTH    = fpga_cfg_pkg::FP_WIDTH ,
    parameter int QINT     = fpga_cfg_pkg::FP_QINT  ,
    parameter int QFRAC    = fpga_cfg_pkg::FP_QFRAC ,
    parameter int LATENCY  = fpga_cfg_pkg::FP_MUL_ALWAYS_LATENCY
)(
    input  logic                       clk,
    input  logic                       rst_n,

    // streaming handshake --------------------------------------------------
    input  logic                       valid_in,   // sample on a,b is valid
    output logic                       ready_out,  // this block can accept it
    input  logic                       ready_in,   // downstream ready for result
    output logic                       valid_out,  // result is valid
    //-----------------------------------------------------------------------
    input  logic signed [WIDTH-1:0]    a,
    input  logic signed [WIDTH-1:0]    b,
    output logic signed [WIDTH-1:0]    result
);

    // ---------------------------------------------------------------------
    // 0.  Q-format overflow guard  (compile-time helper)
    // ---------------------------------------------------------------------
    localparam int UBIT = WIDTH - QFRAC;

    function automatic bit fits_Qfmt
        (input logic signed [2*WIDTH-1:0] x);
        logic signed [UBIT-1:0] upper_bits;
        logic signed [UBIT-1:0] sign_bits;
        begin
            upper_bits = x[2*WIDTH-1 : WIDTH+QFRAC];
            sign_bits  = { UBIT{ x[WIDTH+QFRAC-1] } };
            fits_Qfmt  = (upper_bits == sign_bits);
        end
    endfunction

    // ---------------------------------------------------------------------
    // 1.  Raw product & pipeline registers
    // ---------------------------------------------------------------------
    localparam int RAWW = 2*WIDTH;
    logic signed [RAWW-1:0] raw_mul;
    always_comb begin
        raw_mul = $signed(a) * $signed(b);
        assert (fits_Qfmt(raw_mul))
          else $error("fxMul_always overflow: a=%0d  b=%0d  @%0t", a, b, $time);
    end

    // Pipeline arrays
    logic signed [RAWW-1:0] pipe_mul  [0:LATENCY];
    logic                   valid_pipe[0:LATENCY];

    // Ready logic: pipeline is ready when its *tail* is empty OR downstream is ready
    wire tail_busy  =  valid_pipe[LATENCY];
    assign ready_out = ~tail_busy | ready_in;   // expose to upstream

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i <= LATENCY; i++) begin
                pipe_mul[i]   <= '0;
                valid_pipe[i] <= 1'b0;
            end
        end
        else if (ready_out) begin  // advance only if we can accept new data
            //----------------------------------------------------------------
            // stage 0  (load new sample if present)
            //----------------------------------------------------------------
            valid_pipe[0] <= valid_in;
            if (valid_in)  pipe_mul[0] <= raw_mul;

            //----------------------------------------------------------------
            // shift pipeline
            //----------------------------------------------------------------
            for (i = 1; i <= LATENCY; i++) begin
                valid_pipe[i] <= valid_pipe[i-1];
                pipe_mul [i]  <= pipe_mul [i-1];
            end
        end
        // else: stall – keep all registers unchanged
    end

    // ---------------------------------------------------------------------
    // 2.  Output slice & handshake
    // ---------------------------------------------------------------------
    assign valid_out = valid_pipe[LATENCY];

    always_ff @(posedge clk)
        if (valid_out && ready_in)  // downstream consumed
            valid_pipe[LATENCY] <= 1'b0; // auto-clear tail valid

    assign result = pipe_mul[LATENCY][QFRAC +: WIDTH];

endmodule
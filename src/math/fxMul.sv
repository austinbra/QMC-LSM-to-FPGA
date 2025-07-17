//Streaming / one-per-path work -> fxMul_always (handshake)
(* use_dsp = "yes" *) module fxMul_always #(
    parameter int WIDTH    = fpga_cfg_pkg::FP_WIDTH ,
    parameter int QINT     = fpga_cfg_pkg::FP_QINT  ,
    parameter int QFRAC    = fpga_cfg_pkg::FP_QFRAC ,
    parameter int LATENCY  = fpga_cfg_pkg::FP_MUL_LATENCY
)(
    input  logic                       clk,
    input  logic                       rst_n,

    input  logic                       valid_in,   // sample on a,b is valid
    output logic                       ready_out,  // this block can accept it
    input  logic                       ready_in,   // downstream ready for result
    output logic                       valid_out,  // result is valid

    input  logic signed [WIDTH-1:0]    a,
    input  logic signed [WIDTH-1:0]    b,
    output logic signed [WIDTH-1:0]    result
);
(* use_dsp = "yes" *) 



    // Sanity check
    initial begin
        assert (LATENCY >= 1)
            else $error("fxMul_always: LATENCY must be ≥1");
        assert (QFRAC > 0)
            else $error("fxMul_always: QFRAC must be >0");
    end


    // 1.  Raw product & pipeline registers
    logic [LATENCY-1:0] v_pipe;
    logic signed [WIDTH-1:0] d_pipe [LATENCY-1:0];

    //stall whole pipe if tail can't drain
    wire shift_en = ready_in | ~v_pipe[LATENCY-1];


    logic signed [2*WIDTH-1:0] raw_prod = a * b;  // Full-width product to avoid overflow
    logic signed [WIDTH-1:0] prod_scaled = (raw_prod + (1 << (QFRAC-1))) >>> QFRAC;  // Round and truncate to WIDTH
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v_pipe <= '0;
        end
        else if (shift_en) begin
            v_pipe <= {v_pipe[LATENCY-2:0], (valid_in && ready_out)};
            d_pipe[0] <= prod_scaled;
            if (LATENCY > 1) d_pipe[1] <= d_pipe[0];
            if (LATENCY > 2) d_pipe[2] <= d_pipe[1];
            if (LATENCY > 3) d_pipe[3] <= d_pipe[2];
            //extend if needed
        end
    end

    // Handshake outputs
    assign valid_out = v_pipe[LATENCY-1];
    assign p = d_pipe[LATENCY-1];

    assign ready_out = ~v_pipe[0] | shift_en;
    assign result = d_pipe[LATENCY-1];

    initial begin
    // Assertions – catch lost back-pressure during sim
        assert property (@(posedge clk) disable iff(!rst_n) valid_out & ~ready_in |-> ##1 ~ready_out)
            else $error("fxMul_always: back-pressure lost - pipeline overwrite");
    end

endmodule
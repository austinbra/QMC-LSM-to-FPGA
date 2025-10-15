timeunit 1ns; timeprecision 1ps;
//Streaming / one-per-path work -> fxMul (handshake)
module fxMul #(
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
            else $error("fxMul: LATENCY must be ≥1");
        assert (QFRAC > 0)
            else $error("fxMul: QFRAC must be >0");
    end


    // 1.  Raw product & pipeline registers
    logic [LATENCY-1:0] v_pipe;
    logic signed [WIDTH-1:0] d_pipe [LATENCY-1:0];

    //stall whole pipe if tail can't drain
    logic shift_en;
    assign shift_en = ready_in || !v_pipe[LATENCY-1];


    logic signed [2*WIDTH-1:0] raw_prod;
    assign raw_prod = a * b;  // Full-width product to avoid overflow

    logic signed [WIDTH-1:0] prod_scaled;
    assign prod_scaled = (raw_prod + (1 <<< (QFRAC-1))) >>> QFRAC;  // Round and truncate to WIDTH

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            v_pipe <= '0;
            d_pipe[0] <= '0;
        end else if (shift_en) begin
            `ifdef SYNTHESIS
                        // Synthesis-safe guard; tools constant-fold LATENCY
            `endif  
            if (LATENCY == 1) begin
                v_pipe[0] <= valid_in && ready_out;
            end else begin
                v_pipe <= {v_pipe[LATENCY-2:0], valid_in && ready_out};
            end
            d_pipe[0] <= prod_scaled;
        end
    end

    generate
        for (genvar i = 1; i < LATENCY; i++) begin
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) d_pipe[i] <= '0;
                else if (shift_en) d_pipe[i] <= d_pipe[i-1];
            end
        end
    endgenerate

    // Handshake outputs
    assign valid_out = v_pipe[LATENCY-1];

    assign ready_out = !v_pipe[0] || shift_en;
    assign result = d_pipe[LATENCY-1];

    logic bp_prev;
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            bp_prev <= 1'b0;
        end else begin
            // remember backpressure condition this cycle
            bp_prev <= (valid_out && !ready_in);

            // if we had backpressure last cycle, ready_out must be 0 now
            if (bp_prev)
            assert (!ready_out)
                else $error("fxMul: back-pressure lost - pipeline overwrite");
        end
    end

endmodule
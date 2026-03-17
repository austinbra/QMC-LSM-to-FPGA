timeunit 1ns; timeprecision 1ps;
// Synthesizable fixed-point square root using non-restoring digit-by-digit algorithm.
//
// Algorithm:
//   To compute sqrt(a) in Q16.16, we compute isqrt(a << QFRAC) which gives
//   the result directly in Q16.16. The extended input is (WIDTH + QFRAC) bits.
//   Each iteration processes 2 input bits and produces 1 result bit.
//   Total iterations = (WIDTH + QFRAC) / 2 = 24 for Q16.16.
//
// Latency: ITERS + 1 cycles (25 for Q16.16). No LUT, no DSP.
// Input a is unsigned Q16.16 (must be >= 0).
module fxSqrt #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS = 8,
    parameter int LATENCY = fpga_cfg_pkg::FP_SQRT_LATENCY,
    parameter string LUT_FILE = "src/gen/sqrt_lut_256.mem"
)(
    input  logic            clk,
    input  logic            rst_n,
    input  logic            valid_in,
    output logic            ready_out,
    output logic            valid_out,
    input  logic            ready_in,
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] result
);
    localparam int EXT_W = WIDTH + QFRAC;   // 48 bits for Q16.16
    localparam int ITERS = EXT_W / 2;       // 24 iterations
    localparam int REM_W = ITERS + 2;       // remainder width (26 bits)

    typedef enum logic [1:0] {S_IDLE, S_COMPUTE, S_DONE} state_t;
    state_t state;

    logic [EXT_W-1:0]   a_work;
    logic [REM_W-1:0]   rem;
    logic [ITERS-1:0]   root;
    logic [4:0]          cnt;

    // Combinational: trial subtraction
    logic [REM_W-1:0] rem_shifted;
    logic [REM_W-1:0] trial;
    logic              trial_ok;

    assign rem_shifted = {rem[REM_W-3:0], a_work[EXT_W-1:EXT_W-2]};
    assign trial       = {{(REM_W-ITERS-2){1'b0}}, root, 2'b01};
    assign trial_ok    = (rem_shifted >= trial);

    assign ready_out = (state == S_IDLE);
    assign valid_out = (state == S_DONE);
    assign result    = {{(WIDTH-ITERS){1'b0}}, root};

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state  <= S_IDLE;
            rem    <= '0;
            root   <= '0;
            a_work <= '0;
            cnt    <= '0;
        end else begin
            case (state)
                S_IDLE: begin
                    if (valid_in) begin
                        a_work <= {a, {QFRAC{1'b0}}};
                        rem    <= '0;
                        root   <= '0;
                        cnt    <= ITERS[4:0] - 5'd1;
                        state  <= S_COMPUTE;
                    end
                end

                S_COMPUTE: begin
                    a_work <= a_work << 2;
                    if (trial_ok) begin
                        rem  <= rem_shifted - trial;
                        root <= {root[ITERS-2:0], 1'b1};
                    end else begin
                        rem  <= rem_shifted;
                        root <= {root[ITERS-2:0], 1'b0};
                    end

                    if (cnt == 5'd0)
                        state <= S_DONE;
                    cnt <= cnt - 5'd1;
                end

                S_DONE: begin
                    if (ready_in)
                        state <= S_IDLE;
                end

                default: state <= S_IDLE;
            endcase
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(result))
        else $error("fxSqrt stall overwrite");
endmodule

module fxlnLUT #(
    parameter WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter QINT = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC = fpga_cfg_pkg::FP_QFRAC,
    parameter LUT_BITS = 12 
)(
    input logic clk,
    input logic rst_n,

    input  logic valid_in,
    output logic ready_out,
    output logic valid_out,
    input  logic ready_in,

    input logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] result
);
    
    //skid buffer
    logic v_reg;
    assign ready_out = ~v_reg | ready_in;

    //range 2^‑LUT_BITS to 2
    localparam [WIDTH-1:0] A_MIN = 1 << (QFRAC-LUT_BITS);
    localparam [WIDTH-1:0] A_MAX = 2 << QFRAC;

    logic [WIDTH-1:0] a_bound;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            a_bound <= '0;
        else if (valid_in && ready_out) begin
            if (a < A_MIN) 
                a_bound <= A_MIN;
            else if (a > A_MAX)
                a_bound <= A_MAX;
            else
                a_bound <= a;
        end
    end

    // BRAM lookup
    wire [LUT_BITS-1:0] lut_index = a_bound[QFRAC-1 -: LUT_BITS];

    (* rom_style="block" *)
    logic [WIDTH-1:0] lut [0:(1<<LUT_BITS)-1];
    initial $readmemh("../gen/ln_lut_4096.hex", lut);

    logic signed [WIDTH-1:0] result_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            result_reg <= '0;
        else if (valid_in && ready_out)
            result_reg <= (a_bound < (1 << QFRAC)) ? -lut[lut_index] : lut[lut_index];  // Negate for ln < 0
    end

    // Handshake
    wire shift_en = ready_in | ~v_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
            v_reg <= '0;
        else if (shift_en) 
            v_reg <= valid_in && ready_out;
    end

    assign valid_out = v_reg;
    assign result = result_reg;

endmodule

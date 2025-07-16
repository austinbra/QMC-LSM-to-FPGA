module fxExpLUT #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS  = 12
)(
    input  logic clk,
    input  logic rst_n,

    input  logic valid_in,
    output logic ready_out,
    output logic valid_out,
    input  logic ready_in,

    input  logic signed [WIDTH-1:0] a,
    output logic signed [WIDTH-1:0] result
);

    // skid buffer
    logic v_reg;
    assign ready_out = ~v_reg | ready_in;

    // range  (−8 <= x <= 8)
    localparam signed [WIDTH-1:0] A_MIN = -(8 << QFRAC);
    localparam signed [WIDTH-1:0] A_MAX = (8 << QFRAC) - 1;

    logic signed [WIDTH-1:0] a_bound;
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

    // lut_indexess into BRAM
    wire is_neg = (a_bound < 0);
    wire [LUT_BITS-1:0] lut_index = is_neg ? (-a_bound[QFRAC-1 -: LUT_BITS]) : a_bound[QFRAC-1 -: LUT_BITS];

    (* rom_style="block" *)
    logic signed [WIDTH-1:0] lut [0:(1<<LUT_BITS)-1];
    initial $readmemh("../gen/exp_lut_4096.hex", lut);

    // One‑cycle read
    logic signed [WIDTH-1:0] result_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            result_reg <= '0;
        else if (valid_in && ready_out)
            result_reg <= is_neg ? ((1 <<< QFRAC) / lut[lut_index]) : lut[lut_index];
    end

    // Output handshake
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

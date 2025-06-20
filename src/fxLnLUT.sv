//-----------------------------------------------------------
// LUT for ln(x), for 0.000015 <= x <= 0.5
//-----------------------------------------------------------

module fxlnLUT #(
    parameter WIDTH = 32,
    parameter FRAC = 16,
    parameter ADDR_WIDTH = 10   // 1024 entries in LUT
)(
    input logic clk,
    input logic rst_n,
    input logic valid_in,
    input logic [WIDTH-1:0] x,

    output logic valid_out,
    output logic [WIDTH-1:0] ln_out
);

    // LUT ROM
    logic [WIDTH-1:0] lut [0:(1<<ADDR_WIDTH)-1];
    initial $readmemh("ln_lut_q16.hex", lut);

    // normalize x to address index
    logic [ADDR_WIDTH-1:0] index;
    always_comb begin
        // scale x from [2^-16, 0.5] to [0, 1023]
        // x >> (Frac - ADDR_WIDTH) acts as downscale
        index = x[FRAC +: ADDR_WIDTH];      // extracts ADDR_WIDTH bits from the fractional part of x
    end

    logic [WIDTH-1:0] ln_val;
    always_ff @(posedge clk) begin
        if (!rst_n)
            ln_val <= 0;
        else if (valid_in)
            ln_val <= lut[index];
    end

    assign ln_out = ln_val;
    assign valid_out = valid_in;

endmodule
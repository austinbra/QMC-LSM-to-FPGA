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
    /* verilator lint_off UNUSED */
    input logic [WIDTH-1:0] x,
    /* verilator lint_on UNUSED */

    output logic valid_out,
    output logic [WIDTH-1:0] ln_out
);

initial begin
    $display("fxlnLUT initialized");
end

always_ff @(posedge clk) begin
    if (valid_in)
        $display("Accessing LUT[%0d] = %0d (0x%08X)", index, lut[index], lut[index]);
end

    // LUT ROM
    logic [WIDTH-1:0] lut [0:(1<<ADDR_WIDTH)-1];
    initial $readmemh("ln_lut_q16.hex", lut);

    // Extract upper 10 fractional bits as index (e.g., x[15:6])
    /* verilator lint_off UNUSED */
    logic [ADDR_WIDTH-1:0] index;
    /* verilator lint_on UNUSED */
        
    // Map x ∈ [x_min, x_max] to index ∈ [0, 1023]
    // x in Q16.16, x_min = 0.000015 * 65536 ≈ 1, x_max = 0.5 * 65536 = 32768
    localparam logic [WIDTH-1:0] X_MIN = 32'd1;
    localparam logic [WIDTH-1:0] X_MAX = 32'd32768;
    localparam logic [WIDTH-1:0] X_RANGE = X_MAX - X_MIN;
    /* verilator lint_off UNUSED */
    logic [WIDTH + ADDR_WIDTH - 1:0] scaled_index;
    /* verilator lint_on UNUSED */

    logic [WIDTH + ADDR_WIDTH - 1:0] x_ext, x_min_ext, x_range_ext;

    /* verilator lint_off WIDTH */
    assign x_ext       = x;
    assign x_min_ext   = X_MIN;
    assign x_range_ext = X_RANGE;
    /* verilator lint_on WIDTH */

    always_comb begin
        if (x <= X_MIN)
            index = 0;
        else if (x >= X_MAX)
            index = (1 << ADDR_WIDTH) - 1;
        else begin
            scaled_index = ((x_ext - x_min_ext) * ((1 << ADDR_WIDTH) - 1)) / x_range_ext;
            index = scaled_index[ADDR_WIDTH-1:0]; 
        end 
    end

    logic [WIDTH-1:0] ln_val;
    always_ff @(posedge clk) begin
        if (!rst_n)
            ln_val <= 0;
        else if (valid_in)
            ln_val <= lut[index];
    end

    assign ln_out = ln_val;
    // Delay valid signal by 1 cycle to match when ln_val is ready
    logic v1;
    always_ff @(posedge clk) begin
        if (!rst_n)
            v1 <= 1'b0;
        else
            v1 <= valid_in;
    end

    assign valid_out = v1;

endmodule

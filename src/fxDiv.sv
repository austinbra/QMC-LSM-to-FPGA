
module fxDiv #(
    parameter WIDTH   = 32,
    parameter QFRAC   = 16
)(
    input  logic                    clk,
    input  logic                    rst_n,  // active‐low reset
    input  logic signed [WIDTH-1:0] num,  
    input  logic signed [WIDTH-1:0] denom,
    output logic signed [WIDTH-1:0] result     
);
    
    
    localparam int FULLW = WIDTH + QFRAC;

    logic signed [FULLW-1:0] num_ext, denom_ext;
    logic signed [FULLW-1:0] shifted, div_full;

    wire [QFRAC-1:0] _unused_frac = div_full[QFRAC-1:0];


    always_comb begin
        num_ext   = {{QFRAC{num[WIDTH-1]}},   num};
        denom_ext = {{QFRAC{denom[WIDTH-1]}}, denom};
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            shifted  <= '0;
            div_full <= '0;
            result   <= '0;
        end else begin
            shifted  <= num_ext <<< QFRAC;
            div_full <= shifted / denom_ext;
            result   <= div_full[FULLW-1 -: WIDTH];
        end
    end


endmodule
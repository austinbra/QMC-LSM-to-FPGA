
module sobol_flex #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,   // 16, 32, 64...
    parameter int M = 50                       // time-steps "dimensions"
)(
    input  logic                         clk,
    input  logic                         rst_n,

    input  logic                         valid_in,
    input  logic [WIDTH-1:0]             idx_in,       // path index (row)
    input  logic [$clog2(M)-1:0]         dim_in,       // current time-step (col)
    output logic                         valid_out,
    output logic [WIDTH-1:0]             sobol_out
);

    // Direction-number memory :  M * WIDTH words
    (* ram_style = "block" *)
    logic [WIDTH-1:0]  direction [0:M*WIDTH-1];
    initial $readmemh("../gen/direction.mem", direction);


    logic [WIDTH-1:0] gray;
    always_comb gray = idx_in ^ (idx_in >> 1); 
    //one on/off shifts the new dot into the biggest available gap.
    //Because the recipe is deterministic, the generator never stores the earlier points.
    //You just feed in the row index i and the formula dictates the new coordinate


    logic [WIDTH-1:0] leaf [0:WIDTH-1];
    genvar k;
    generate
        for (k = 0; k < WIDTH; k = k + 1)
            assign leaf[k] = gray[k] ? direction[dim_in*WIDTH + k] : '0; //for each bit position check if high then save x and y value, else 0
    endgenerate

    // depth = ceil(log2(WIDTH))
    localparam int LEVELS = (WIDTH <= 1) ? 1 : $clog2(WIDTH);

    // Stages; example: stage[l][i] holds XOR result at level l, element i
    logic [WIDTH-1:0] stage [0:LEVELS] ;
    generate
        for (k = 0; k < WIDTH; k++)
            assign stage[0][k] = leaf[k];

        //xor everything together
        for (k = 0; k < LEVELS; k++) begin : GEN_LEVEL
            for (int j = 0; j < (WIDTH >> (k+1)); j = j + 1) begin : GEN_PAIR
                assign stage[k+1][j] = stage[k][2*j] ^ stage[k][2*j+1];
            end
        end
    endgenerate
    assign sobol_out = stage[LEVELS][0];  // one 32-bit fraction on the 0–1 line, it lands where the biggest gap would have been split in half.

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)        
            valid_out <= 1'b0;
        else               
            valid_out <= valid_in;

endmodule

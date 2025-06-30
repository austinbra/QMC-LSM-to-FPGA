//=============================================================================
// sobol_fast  – 1-cycle, 32-bit Sobol draw, ready/valid interface
//   *  Block-RAM holds M×32 direction numbers
//   *  Gray-coded index so only one bit changes per path
//   *  5-level balanced XOR tree (fastest combinational form)
//=============================================================================
module sobol_fast #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,     // direction word width (fixed at 32)
    parameter int M = 50                         // Sobol dimensions (time steps)
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // stream interface
    input  logic                     valid_in,
    input  logic [WIDTH-1:0]         N,       		// number of paths
    input  logic [$clog2(M)-1:0]     dim_in,       // 0 … M-1
    output logic                     valid_out,
    output logic [WIDTH-1:0]         sobol_out 
);

    //-------------------------------------------------------------------------
    // 1) synchronous BRAM for direction numbers (M×32 words)
    //-------------------------------------------------------------------------
    (* ram_style = "block" *)
    logic [WIDTH-1:0] direction [0:M*WIDTH-1];

    initial $readmemh("gen/direction.mem", direction);

    // registered address into BRAM  (dim*32 + bit)
    logic [$clog2(M*WIDTH)-1:0] dir_addr_r;
    always_ff @(posedge clk) dir_addr_r <= {dim_in, N[4:0]};

    // word selected by BRAM, valid next cycle
    logic [WIDTH-1:0] dir_word_r;
    always_ff @(posedge clk) dir_word_r <= direction[dir_addr_r];

    //-------------------------------------------------------------------------
    // 2) one-clock Gray code (combinational)
    //-------------------------------------------------------------------------
    logic [WIDTH-1:0] gray;
    always_comb gray = N ^ (N >> 1);

    //-------------------------------------------------------------------------
    // 3) 5-level balanced XOR tree
    //-------------------------------------------------------------------------
    // leaf 0‥31: take direction[dim*32+k] when gray[k]==1 else 0
    logic [WIDTH-1:0] leaf [0:31];
    genvar k;
    generate
        for (k = 0; k < 32; k = k + 1)
            assign leaf[k] = gray[k] ? direction[{dim_in, k[4:0]}] : '0;
    endgenerate

    // level-1: 16 XORs
    logic [WIDTH-1:0] l1 [0:15];
    generate
        for (k = 0; k < 16; k = k + 1)
            assign l1[k] = leaf[2*k] ^ leaf[2*k+1];
    endgenerate

    // level-2: 8 XORs
    logic [WIDTH-1:0] l2 [0:7];
    generate
        for (k = 0; k < 8; k = k + 1)
            assign l2[k] = l1[2*k] ^ l1[2*k+1];
    endgenerate

    // level-3: 4 XORs
    logic [WIDTH-1:0] l3 [0:3];
    generate
        for (k = 0; k < 4; k = k + 1)
            assign l3[k] = l2[2*k] ^ l2[2*k+1];
    endgenerate

    // level-4: 2 XORs
    logic [WIDTH-1:0] l4 [0:1];
    generate
        for (k = 0; k < 2; k = k + 1)
            assign l4[k] = l3[2*k] ^ l3[2*k+1];
    endgenerate

    // level-5: final XOR
    assign sobol_out = l4[0] ^ l4[1];

    //-------------------------------------------------------------------------
    // 4) stream handshake: one-cycle latency
    //-------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n)      valid_out <= 1'b0;
        else             valid_out <= valid_in;

endmodule

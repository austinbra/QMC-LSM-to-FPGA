// Unrolled, BRAM-backed Sobol generator (Q0.32 -> [0,1))

module sobol #(
    parameter M = 50  // Number of Sobol dimensions (time steps)
)(
    input  logic [31:0] N,         // Path index
    input  logic [$clog2(M)-1:0] dim,       // Dimension selector: 0…M-1
    output logic [31:0] sobol_out  // Q0.32 fixed-point Sobol draw
);
    // Flattened 2D direction numbers in block RAM (M*32*32 bits)
    (* ram_style = "block" *)
    logic [31:0] direction [0:M*32-1];

    initial begin
        $readmemh("gen/direction.mem", direction); // expects M*32 hex lines
    end

    // Gray-code of index: make sure only one bit flips per step
    wire [31:0] gray = N ^ (N >> 1);

    
    // Unrolled XOR reduction for max clock frequency
    logic [31:0] xors [0:31];

    genvar k;
    generate
        for (k = 0; k < 32; k = k + 1) begin : UNROLL_XOR
            // if gray[k]=1, include direction[dim*32+k], else 0
            assign xors[k] = gray[k] ? direction[dim*32 + k] : 32'd0;
        end
    endgenerate

    // Stage-1: 32 -> 16
    logic [31:0] sum16 [0:15];
    generate
        for (k = 0; k < 16; k = k + 1) begin : REDUCE16
            assign sum16[k] = xors[2*k] ^ xors[2*k + 1];
        end
    endgenerate

    // Stage-2: 16 -> 8
    logic [31:0] sum8 [0:7];
    generate
        for (k = 0; k < 8; k = k + 1) begin : REDUCE8
            assign sum8[k] = sum16[2*k] ^ sum16[2*k + 1];
        end
    endgenerate

    // Stage-3: 8 -> 4
    logic [31:0] sum4 [0:3];
    generate
        for (k = 0; k < 4; k = k + 1) begin : REDUCE4
            assign sum4[k] = sum8[2*k] ^ sum8[2*k + 1];
        end
    endgenerate

    // Stage-4: 4 -> 2
    logic [31:0] sum2 [0:1];
    generate
        for (k = 0; k < 2; k = k + 1) begin : REDUCE2
            assign sum2[k] = sum4[2*k] ^ sum4[2*k + 1];
        end
    endgenerate

    // Final: 2 -> 1
    assign sobol_out = sum2[0] ^ sum2[1];

endmodule

module sobol #(
    parameter M = 50  // Number of Sobol dimensions (time steps). Default is 50.
)(
    input  logic [31:0] N,  // Path index (used to compute the i-th Sobol number)
    input  logic [$clog2(M)-1:0] dim,  // Dimension selector: 0 to M-1
    output logic [31:0] sobol_out
);
    logic [31:0] direction [0:M*32-1]; //Flattened 2D array

    initial begin
        $readmemh("gen/direction.mem", direction); //expects M×32 hex lines
    end

    integer j;
    always_comb begin //similar to always @(*) but includes all inputs automatically instead of "always @(a or b or c)"
        sobol_out = 32'd0; //32 bits of the decimal (d) = 0
        for (j = 0; j < 32; j = j + 1) begin
            if (N[j]) begin //only compute the j'th bits of N that are 1
                sobol_out ^= direction[dim * 32 + j]; // direction[dim * 32 + j] = v_j
            end
        end
    end
endmodule

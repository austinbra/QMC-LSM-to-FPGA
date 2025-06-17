module tb_sobol;
    logic [31:0] N;

    localparam M = 50;
    logic [$clog2(M)-1:0] dim;

    logic [31:0] sobol_out;

    sobol #(.M(M)) uut (
        .N(N),
        .dim(dim),
        .sobol_out(sobol_out)
    );

    initial begin
        N = 10;
        //the Nth value for dimensions 0 to M
        for (dim = 0; dim < M; dim++) begin
            #1;
            $display("dim %0d, index %0d => sobol = 0x%08x", dim, N, sobol_out);
        end
        //the first N values for dimensions 0
        dim = 0;
        for (N = 0; N < 10; N++) begin
            #1;
            $display("dim %0d, index %0d => sobol = 0x%08x", dim, N, sobol_out);
        end
        $finish;
    end
endmodule

//iverilog -g2012 -o sobol_test sobol.v tb_sobol.sv
//vvp sobol_test

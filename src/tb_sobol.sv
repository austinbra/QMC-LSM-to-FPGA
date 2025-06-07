module tb_sobol;
    logic [31:0] N;

    localparam M = 12;
    logic [$clog2(M)-1:0] dim;

    logic [31:0] sobol_out;

    sobol #(.M(12)) uut (
        .N(N),
        .dim(dim),
        .sobol_out(sobol_out)
    );

    initial begin
        N = 10;
        for (dim = 0; dim < 12; dim++) begin
            #1;
            $display("dim %0d, index %0d => sobol = 0x%08x", dim, N, sobol_out);
        end
        $finish;
    end
endmodule

//iverilog -g2012 -o sobol_test sobol.v tb_sobol.sv
//vvp sobol_test

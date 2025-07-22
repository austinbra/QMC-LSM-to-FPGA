`timescale 1ns/1ps
module sobol #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,   // 16, 32, 64...
    parameter int M         = 50,                       // time-steps "dimensions"
    parameter int LANE_ID   = 0
)(
    input  logic                         clk,
    input  logic                         rst_n,

    input  logic                         valid_in,
    output logic                         ready_out,
    output logic                         valid_out, //to downstream
    input  logic                         ready_in, //from downstream

    input  logic [WIDTH-1:0]             idx_in,       // current path index (row)
    input  logic [$clog2(M)-1:0]         dim_in,       // current time-step (col)
    output logic [WIDTH-1:0]             sobol_out
);

    // Direction-number memory :  M * WIDTH words
    (* ram_style = "block" *)
    logic [WIDTH-1:0]  direction [0:M*WIDTH-1];
    initial $readmemh("direction.mem", direction);


    logic [WIDTH-1:0] gray;
    always_comb begin
        gray = idx_in ^ (idx_in >>> 1); 
    end
    //one on/off shifts the new dot into the biggest available gap.
    //Because the recipe is deterministic, the generator never stores the earlier points.
    //You just feed in the row index i and the formula dictates the new coordinate


    logic [WIDTH-1:0] leaf [0:WIDTH-1];
    
    generate
        for (genvar k = 0; k < WIDTH; k = k + 1) begin
            assign leaf[k] = gray[k] ? direction[dim_in*WIDTH + k] : '0; //for each bit position check if high then save x and y value, else 0
        end
    endgenerate// Procedural block for debugging

    always_comb begin
        for (int k = 0; k < WIDTH; k++) begin
            $display("Cycle %t: Gray code=%b, Leaf[%0d]=%h", $time, gray, k, leaf[k]);
        end
        $display("Cycle %t: sobol_out=%h", $time, sobol_out);
    end
    

    // depth = ceil(log2(WIDTH))
    localparam int LEVELS = $clog2(WIDTH);

    // Stages; example: stage[l][i] holds XOR result at level l, element i
    logic [WIDTH-1:0] stage [0:LEVELS][0:WIDTH-1];
    generate
        for (genvar k = 0; k < WIDTH; k++)begin
            assign stage[0][k] = leaf[k];
            
        end
        
        
        //xor everything together
        for (genvar lvl = 0; lvl < LEVELS; lvl++) begin : GEN_LEVEL
            for (genvar j = 0; j < (WIDTH >> (lvl+1)); j++) begin : GEN_PAIR
                assign stage[lvl+1][j] = stage[lvl][2*j] ^ stage[lvl][2*j+1];
            end
        end
    endgenerate
    
    logic [WIDTH-1:0] sobol_raw;
    assign sobol_raw = stage[LEVELS][0];


    // skid buffer for ready/valid handshaking
    logic skid_valid;
    logic [WIDTH-1:0] skid_sobol_reg;

    assign ready_out = !skid_valid || ready_in;

    assign valid_out = skid_valid;
    assign sobol_out = skid_sobol_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skid_valid <= 1'b0;
            skid_sobol_reg <= '0;
        end else begin
            if (valid_in && ready_out) begin
                skid_sobol_reg <= sobol_raw;
                skid_valid <= 1'b1;
            end
            else if (skid_valid && ready_in) begin
                skid_valid <= 1'b0;
            end
        end
        
    end

    // Assertions for verification (stall/backpressure invariants)
    initial begin
        assert (WIDTH > 0 && $clog2(WIDTH) == LEVELS) 
            else $error("Non-power-of-2 WIDTH in Sobol");

        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(sobol_out)) 
            else $error("Sobol: Stall overwrite - data loss");

        assert property (@(posedge clk) disable iff (!rst_n) valid_in && !ready_out |=> $stable(idx_in) && $stable(dim_in)) 
            else $error("Sobol: Input overwrite on backpressure");

        assert property (@(posedge clk) disable iff (!rst_n) (idx_in == 0) |-> (sobol_out == 0)) 
            else $error("Error: sobol_out should be 0 for idx=0");
    end

endmodule

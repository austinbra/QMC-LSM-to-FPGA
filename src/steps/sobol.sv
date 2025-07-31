`timescale 1ns/1ps
module sobol #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,   // 16, 32, 64...
    parameter int M         = 50,                       // total time-steps "dimensions"
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
    output logic [WIDTH-1:0]             sobol_out,

    // expose the entire LUT for TB / debugging
    output logic [WIDTH-1:0]         direction [0:M*WIDTH-1]
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
    //Because the reciprical is deterministic, the generator never stores the earlier points.
    //You just feed in the row index i and the formula dictates the new coordinate


    logic [WIDTH-1:0] leaf [0:WIDTH-1];
    
    generate
        for (genvar k = 0; k < WIDTH; k = k + 1) begin
            assign leaf[k] = gray[k] ? direction[dim_in*WIDTH + k] : '0; //for each bit position check if high then save x and y value, else 0
        end
    endgenerate// Procedural block for debugging    

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


    // Fixed Buffer logic
    logic buffer_valid;
    logic [WIDTH-1:0] buffer_data;

    assign ready_out = !buffer_valid || ready_in;
    assign valid_out = buffer_valid;
    assign sobol_out = buffer_data;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buffer_valid <= 1'b0;
            buffer_data <= '0;
        end else begin
            // Use case statement to handle all combinations explicitly
            case ({valid_in && ready_out, buffer_valid && ready_in})
                2'b00: begin
                    // No input, no output - no change
                end
                2'b01: begin
                    // No input, output consumed
                    buffer_valid <= 1'b0;
                end
                2'b10: begin
                    // Input accepted, no output
                    buffer_data <= sobol_raw;
                    buffer_valid <= 1'b1;
                end
                2'b11: begin
                    // Both input accepted and output consumed simultaneously
                    buffer_data <= sobol_raw;
                    // buffer_valid stays 1'b1
                end
            endcase
        end
    end

    // Assertions for verification
    initial begin
        assert (WIDTH > 0 && (1 << $clog2(WIDTH)) == WIDTH) 
            else $error("WIDTH must be a power of 2 in Sobol");

        assert property (@(posedge clk) disable iff (!rst_n) 
            valid_out && !ready_in |=> $stable(sobol_out)) 
            else $error("Sobol: Stall overwrite - data loss");

        assert property (@(posedge clk) disable iff (!rst_n) 
            valid_in && !ready_out |=> $stable(idx_in) && $stable(dim_in)) 
            else $error("Sobol: Input overwrite on backpressure");
    end

endmodule

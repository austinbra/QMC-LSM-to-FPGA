// UART Transmitter

module uart_tx #(
    parameter CLK_FREQ_HZ = 100000000,  // 100 MHz
    parameter BAUD_RATE = 115200
)(
    input logic clk,
    input logic rst_n,
    input logic [7:0] tx_data,      // need to get 32 bits to match width
    input logic tx_start,
    output logic tx,
    output logic tx_busy
);

    localparam int CLKS_PER_BIT = CLK_FREQ_HZ / BAUD_RATE;
    typedef enum logic [2:0] {
        IDLE,
        START_BIT,
        DATA_BITS,
        STOP_BIT,
        CLEANUP
    } state_t;
    
    state_t state;
    logic [15:0] clk_count;
    logic [2:0] bit_index;      // 8 bit UART
    logic [7:0] tx_data_reg;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            clk_count <= 0;
            bit_index <= 0;
            tx_data_reg <= 0;
            tx <= 1'b1;
            tx_busy <= 0;
        end else begin
            case (state)
                IDLE: begin
                    tx <= 1'b1;
                    clk_count <= 0;
                    bit_index <= 0;
                    tx_busy <= 0;
                    if (tx_start) begin
                        tx_data_reg <= tx_data;
                        state <= START_BIT;
                        tx_busy <= 1;
                    end
                end
                
                START_BIT: begin
                    tx <= 1'b0;
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
                        state <= DATA_BITS;
                    end else begin
                        clk_count <= clk_count + 1;
                    end    
                end

                DATA_BITS: begin
                    tx <= tx_data_reg[bit_index];
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
                        if (bit_index == 7)
                            state <= STOP_BIT;
                        else
                            bit_index <= bit_index + 1;
                    end else
                        clk_count <= clk_count + 1;
                end
                
                STOP_BIT: begin
                    tx <= 1'b1;
                    if (clk_count == CLKS_PER_BIT - 1) begin
                        clk_count <= 0;
                        state <= CLEANUP;
                    end else begin
                        clk_count <= clk_count + 1;
                    end
                end
                    
                CLEANUP: begin
                    tx_busy <= 0;
                    state <= IDLE;
                end
            endcase
        end    
    end
endmodule
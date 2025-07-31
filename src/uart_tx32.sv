// Wrapper to handle 32 bit Q16.16 format

module uart_tx32 #(
    parameter CLK_FREQ_HZ = 100_000_000,  // 100 MHz
    parameter BAUD_RATE = 115200
)(
    input logic clk,
    input logic rst_n,
    
    input logic valid_in,
    input logic [31:0] data_in,
    output logic ready_out,
    
    output logic tx,
    output logic tx_busy
    );
    
    typedef enum logic [2:0] {
        IDLE, BYTE0, BYTE1, BYTE2, BYTE3, DONE
    } state_t;
    
    logic [7:0] tx_data;
    logic tx_start;
    logic tx_busy_d;
    state_t state;
    logic [31:0] data_buf;
    
    uart_tx #(.CLK_FREQ_HZ(CLK_FREQ_HZ), .BAUD_RATE(BAUD_RATE)) tx_byte (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(tx_data),
        .tx_start(tx_start),
        .tx(tx),
        .tx_busy(tx_busy)
    );
    
    logic tx_done;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            tx_busy_d <= 0;
        else
            tx_busy_d <= tx_busy;
    end

    assign tx_done = (tx_busy_d == 1) && (tx_busy == 0);

    
    assign ready_out = (state == IDLE);
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            tx_start <= 0;
            tx_data <= 0;
            data_buf <= 0;
        end else begin
            tx_start <= 0;
            
            case (state)
                IDLE: begin
                    if (valid_in) begin
                        data_buf <= data_in;
                        state <= BYTE0;
                    end
                end
                
                BYTE0: begin
                    tx_data <= data_buf[7:0];
                    tx_start <= 1;
                    state <= BYTE1;
                end
                
                BYTE1: if (tx_done) begin
                    tx_data <= data_buf[15:8];
                    tx_start <= 1;
                    state <= BYTE2;
                end
                
                BYTE2: if (tx_done) begin
                    tx_data <= data_buf[23:16];
                    tx_start <= 1;
                    state <= BYTE3;
                end
                
                BYTE3: if (tx_done) begin
                    tx_data <= data_buf[31:24];
                    tx_start <= 1;
                    state <= DONE;
                end
                
                DONE: if (tx_done) begin
                    state <= IDLE;
                end
            endcase
        end
    end
endmodule

// Wrapper to handle 32 bit Q16.16 format

module uart_rx32 #(
    parameter CLK_FREQ_HZ = 100000000,  // 100 MHz
    parameter BAUD_RATE = 115200
)(
    input logic clk,
    input logic rst_n,
    
    input logic rx,
    output logic valid_out,
    output logic [31:0] data_out
);

    // One byte receiver
    logic [7:0] rx_data;
    logic rx_valid;
    
    uart_rx #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE)
    ) uart_rx_inst (
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .rx_data(rx_data),
        .rx_valid(rx_valid)
    );
    
    // FSM to receive 4 bytes
    typedef enum logic [2:0] {
        IDLE,
        BYTE0,
        BYTE1,
        BYTE2,
        BYTE3
    } state_t;
    
    state_t state;
    logic [31:0] buffer;
    
    // Output registers
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            buffer <= 32'd0;
            data_out <= 32'd0;
            valid_out <= 1'b0;
        end else begin
            valid_out <= 1'b0;
            
            if (rx_valid) begin
                case (state)
                    IDLE: begin
                        buffer[7:0] <= rx_data;
                        state <= BYTE1;
                    end
                    
                    BYTE1: begin
                        buffer[15:8] <= rx_data;
                        state <= BYTE2;
                    end
                    
                    BYTE2: begin
                        buffer[23:16] <= rx_data;
                        state <= BYTE3;
                    end
                    
                    BYTE3: begin
                        buffer[31:24] <= rx_data;
                        data_out <= {rx_data, buffer[23:0]};
                        valid_out <= 1'b1;
                        state <= IDLE;
                    end
                    
                    default: state <= IDLE;
                endcase
            end
        end
    end
endmodule

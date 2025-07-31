module uart_input_handler #(
    parameter CLK_FREQ_HZ = 100_000_000,
    parameter BAUD_RATE = 115200
)(
    input logic clk,
    input logic rst_n,
    
    input logic rx,         // serial rx line
    output logic tx,         // serial tx line
    
    output logic batch_valid,
    input logic batch_ready,
    
    output logic [31:0] paths,
    output logic [31:0] steps,
    output logic [31:0] S0,
    output logic [31:0] K,
    output logic [31:0] r,
    output logic [31:0] sigma,
    output logic [31:0] T
);

    // FSM states
    typedef enum logic [1:0] {
        S_RECEIVE,
        S_WAIT_READY
    } state_t;
    
    state_t state, next_state;
    
    logic [2:0] word_cnt;
    
    // UART rx signals
    logic [31:0] rx_data;
    logic rx_valid;
    
    // UART tx signals
    logic tx_ready;
    logic tx_valid;
    logic [31:0] tx_data;
    
    // Register storage
    logic [31:0] reg_array [0:6];
    
    logic rx_valid_d;
logic rx_valid_rising;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        rx_valid_d <= 1'b0;
    else
        rx_valid_d <= rx_valid;
end

assign rx_valid_rising = rx_valid && !rx_valid_d;
    
    // FSM sequential logic and storage
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_RECEIVE;
            word_cnt <= 0;
        end else begin
            state <= next_state;
            if (state == S_RECEIVE && rx_valid_rising && word_cnt <= 6) begin
            reg_array[word_cnt] <= rx_data;
            $display("Stored word %0d = 0x%08x", word_cnt, rx_data);
            word_cnt <= word_cnt + 1;
        end

        if (state == S_WAIT_READY && batch_ready)
            word_cnt <= 0;
        end
    end
    
    // FSM next state logic
    always_comb begin
    next_state = state;
    batch_valid = 0;

    case (state)
        S_RECEIVE: begin
            if (rx_valid_rising && word_cnt == 6)
                next_state = S_WAIT_READY;
        end

        S_WAIT_READY: begin
            batch_valid = 1;
            if (batch_ready)
                next_state = S_RECEIVE;
        end
    endcase
end
    
    // Assign outputs
    assign paths = reg_array[0];
    assign steps = reg_array[1];
    assign S0 = reg_array[2];
    assign K = reg_array[3];
    assign r = reg_array[4];
    assign sigma = reg_array[5];
    assign T = reg_array[6];
    
    // UART rx module
    uart_rx32 #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE)
    ) uart_rx_inst (
        .clk(clk),
        .rst_n (rst_n),
        .rx(rx),
        .valid_out(rx_valid),
        .data_out (rx_data)
    );
    
    // HERE
    
// ==============================
    // Optional UART TX (Echo-back after full batch)
    // ==============================
    uart_tx32 #(
        .CLK_FREQ_HZ(CLK_FREQ_HZ),
        .BAUD_RATE(BAUD_RATE)
    ) uart_tx_inst (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (tx_valid),
        .data_in   (tx_data),
        .ready_out (tx_ready),
        .tx        (tx),
        .tx_busy   ()
    );

    // OPTIONAL: Simple echo of each word during WAIT_READY
    logic [2:0] echo_cnt;
    logic       echoing;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            echo_cnt <= 0;
            echoing <= 0;
        end else if (state == S_WAIT_READY && batch_ready) begin
            echo_cnt <= 0;
            echoing <= 1;
        end else if (echoing && tx_ready) begin
            echo_cnt <= echo_cnt + 1;
            if (echo_cnt == 6)
                echoing <= 0;
        end
    end

    assign tx_valid = echoing;
    assign tx_data  = reg_array[echo_cnt];    
endmodule
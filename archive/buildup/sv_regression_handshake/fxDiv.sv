
module fxDiv #(
    parameter WIDTH   = 32,
    parameter LATENCY = 1,   // iterations or pipeline depth
    parameter Qint    = 16,
    parameter Qfrac   = WIDTH - Qint
)(
    input  logic                    clk,
    input  logic                    rst,
    input  logic                    start,      // pulse to start a divide
    input  logic signed [WIDTH-1:0] numerator,  // Q-format dividend
    input  logic signed [WIDTH-1:0] denominator,// Q-format divisor
    output logic signed [WIDTH-1:0] result,     // Q-format result
    output logic                    done        // asserted when quotient valid
);
    logic signed [WIDTH-1:0]  num_reg, den_reg;
    logic start_reg;

    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            num_reg <= 0;
            den_reg <= 0;
            start_reg <= 0;
        end else begin
            num_reg <= numerator;
            den_reg <= denominator;
            start_reg <= start;
        end
    end
    
    logic signed [WIDTH-1:0] div_pipe [0:LATENCY];

    integer i;
    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            for (i = 0; i <= LATENCY; i = i + 1)
                div_pipe[i] <= '0;
        end
        else begin
            //divide
            div_pipe[0] <= (num_reg <<< Qfrac) / den_reg;//will change later to optimize, look at fxmul and fxdiv phase 2 in drive
            // shift the previous values down the pipeline
            for (i = 1; i <= LATENCY; i = i + 1)
                div_pipe[i] <= div_pipe[i-1];
        end
    end


    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            result <= '0;
        end
        else begin
            result <= div_pipe[LATENCY];
        end
    end

    localparam int count_WIDTH = $clog2(LATENCY + 2);//minimize bit width
    logic [count_WIDTH-1:0] cycle_cnt;

    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            cycle_cnt <= '0;
            done      <= 1'b0;
        end else if (start_reg) begin
            cycle_cnt <= 1;        // start counting
            done      <= 1'b0;
        end else if (cycle_cnt != 0) begin
            cycle_cnt <= cycle_cnt + 1;
            done      <= (cycle_cnt == LATENCY + 1);
            if (done)
                cycle_cnt <= '0;     // reset after setting done high
        end else begin
            done <= 1'b0;
        end
    end


endmodule
module fxMul #(
    parameter WIDTH = 32, //data width
    parameter LATENCY = 1, //pipeline stages
    parameter Qint = 16,    //int bits for Q format
    parameter Qfrac = WIDTH - Qint //fractional bits
)(
    input logic         clk,
    input logic         rst,
    input logic         start,
    input logic signed [WIDTH-1:0]  a,
    input logic signed [WIDTH-1:0]  b,
    output logic signed [WIDTH-1:0] result,
    output logic        done

);

    // Internal pipeline registers
    // Stage 0: input registers
    logic signed [WIDTH-1:0]  a_reg, b_reg;
    logic start_reg;

    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            a_reg <= 0;
            b_reg <= 0;
            start_reg <= 0;
        end else begin
            a_reg <= a;
            b_reg <= b;
            start_reg <= start;
        end
    end

    // Stage 1 to LATENCY: shift-register pipeline width products
    //------------------------------------------------------
    logic signed [2*WIDTH-1:0] mul_pipe [0:LATENCY];

    integer i;
    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            for (i = 0; i <= LATENCY; i = i + 1)
                mul_pipe[i] <= '0;
        end
        else begin
            //stage 1 multiply and capture
            mul_pipe[0] <= a_reg * b_reg;//will change later to optimize, look at fxmul and fxdiv phase 2 in drive
            // stages 2 to LATENCY+1, shift the previous values down the pipeline
            for (i = 1; i <= LATENCY; i = i + 1)
                mul_pipe[i] <= mul_pipe[i-1];
        end
    end

    // get Qint.Qfrac result from the 2*WIDTH-bit product
    
    // the raw product has 2*Qfrac fractional bits  to align to Qfrac im shifting right by Qfrac
    always_ff @(posedge clk or negedge rst) begin
        if (!rst) begin
            result <= '0;
        end
        else begin
            // select bits [Qfrac + WIDTH–1 : Qfrac] from the 2*WIDTH–1 downto 0 vector
            result <= mul_pipe[LATENCY][Qfrac + WIDTH-1 : Qfrac];
        end
    end

    // Handshake: start -> done after LATENCY+1 cycles

    // Count cycles after start_reg so we can assert done
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

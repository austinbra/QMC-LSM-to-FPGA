// Accumulator for quadratic LSM regression (β0 + β1·S + β2·S²)
module accumulator #(
    parameter int WIDTH     = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT      = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC     = fpga_cfg_pkg::FP_QFRAC,
    parameter int N_SAMPLES = 10000
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // stream from GBM / decision
    input  logic                     valid_in,
    input  logic signed [WIDTH-1:0]  x_in,   // S_t
    input  logic signed [WIDTH-1:0]  y_in,   // discounted payoff

    // β’s once per exercise date
    output logic                     valid_out,
    output logic signed [WIDTH-1:0]  beta [0:2],

    // ready from 3×3 solver
    input  logic                     solver_ready
);

    logic v_x2, v_acc;

    logic signed [WIDTH-1:0] x2, xy, x2y, x3, x4;

    fxMul_always #() mul_x_x (
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in),
        .a(x_in), .b(x_in), .result(x2), .valid_out(v_x2));

    fxMul_always #() mul_x_y (
        .clk(clk), .rst_n(rst_n), .valid_in(valid_in),
        .a(x_in), .b(y_in), .result(xy), .valid_out(/*unused*/));



    fxMul_always #() mul_x2_y (
        .clk(clk), .rst_n(rst_n), .valid_in(v_x2),
        .a(x2), .b(y_in), .result(x2y), .valid_out(v_acc));

    // extra mults fed by x2 so they line-up with v_acc
    fxMul_always #() mul_x2_x (
        .clk(clk), .rst_n(rst_n), .valid_in(v_x2),
        .a(x2), .b(x_in), .result(x3), .valid_out(/*open*/));

    fxMul_always #() mul_x2_x2 (
        .clk(clk), .rst_n(rst_n), .valid_in(v_x2),
        .a(x2), .b(x2), .result(x4), .valid_out(/*open*/));

    // ------------------------------------------------------------
    // 2) 64-bit accumulators
    // ------------------------------------------------------------
    typedef logic signed [63:0] acc_t;

    function acc_t extended (input logic signed [WIDTH-1:0] v);
        extended = {{(64-WIDTH){v[WIDTH-1]}}, v};
    endfunction

    acc_t sum1, sumx, sumx2, sumx3, sumx4, sumy, sumxy, sumx2y;
    logic [$clog2(N_SAMPLES):0] count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sum1    <= '0; 
            sumx    <= '0; 
            sumx2   <= '0; 
            sumx3   <= '0; 
            sumx4   <= '0;
            sumy    <= '0; 
            sumxy   <= '0; 
            sumx2y  <= '0; 
            count   <= '0;
        end
        else if (v_acc) begin
            sum1    <= sum1     + 1;
            sumx    <= sumx     + extended(x_in);
            sumx2   <= sumx2    + extended(x2);
            sumx3   <= sumx3    + extended(x3);
            sumx4   <= sumx4    + extended(x4);
            sumy    <= sumy     + extended(y_in);
            sumxy   <= sumxy    + extended(xy);
            sumx2y  <= sumx2y   + extended(x2y);
            count   <= count    + 1;
        end
    end

    // ------------------------------------------------------------
    // 3) do solver when all sums complete
    // ------------------------------------------------------------
    localparam int IDLE = 0, SOLVE = 1, WAIT = 2;
    logic [1:0] state;
    logic start_solver, solver_done;
    logic signed [WIDTH-1:0] mat_flat [0:11];
    logic signed [WIDTH-1:0] beta_s [0:2];
    logic singular_err;

    regression solver (
        .clk(clk), 
        .rst_n(rst_n),
        .valid_in(start_solver),
        .mat_flat(mat_flat),
        .solver_ready(solver_ready),
        .valid_out(solver_done),
        .singular_err(singular_err),
        .beta(beta_s)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n || singular_err) begin
            state <= IDLE; start_solver<=0; valid_out<=0;
        end else case (state)
            IDLE:
                if (count == N_SAMPLES) begin
                    // Row 0
                    mat_flat[0]=sum1; //this is where the .py file comes in, if i dont need 64 bits then grab only the top bits for the integer part for 32 bits
                    mat_flat[1]=sumx;   
                    mat_flat[2]=sumx2;  
                    mat_flat[3]=sumy;
                    // Row 1
                    mat_flat[4]=sumx;  
                    mat_flat[5]=sumx2;  
                    mat_flat[6]=sumx3;  
                    mat_flat[7]=sumxy;
                    // Row 2
                    mat_flat[8]=sumx2; 
                    mat_flat[9]=sumx3;  
                    mat_flat[10]=sumx4; 
                    mat_flat[11]=sumx2y;
                    start_solver <= 1'b1;
                    state <= SOLVE;
                  end
            SOLVE:
                if (solver_ready) begin
                    start_solver <= 1'b0;
                    state <= WAIT;
                  end
            WAIT: 
                if (solver_done) begin
                    logic fallback = singular_err;

                    // fallback: beta[0] = mean payoff; beta[1] = beta[2] = 0
                    if (fallback) begin
                        // mean = sumy / sum1
                        logic signed [WIDTH-1:0] mean_payoff;
                        logic mean_done;

                        fxDiv #() div_mean (
                            .clk(clk),
                            .rst_n(rst_n),
                            .valid_in(1'b1),
                            .numerator(sumy <<< QFRAC),
                            .denominator(sum1[WIDTH-1:0]),
                            .result(mean_payoff),
                            .valid_out(mean_done));

                        if (mean_done) begin
                            beta[0] <= mean_payoff;
                            beta[1] <= '0;
                            beta[2] <= '0;
                            valid_out <= 1'b1;
                        end else
                            valid_out <= 1'b0;
                    end
                    // normal case: use solver output beta's
                    else begin
                        beta <= beta_s;
                        valid_out <= 1'b1;
                    end
                    // reset for next date
                    sum1 <= 0;
                    sumx <= 0;
                    sumx2 <= 0;
                    sumx3 <= 0;
                    sumx4 <= 0;
                    sumy <= 0;
                    sumxy <= 0;
                    sumx2y <= 0;
                    count <= 0;
                    state <= IDLE;
                end else
                    valid_out <= 1'b0;
        endcase
    end
endmodule

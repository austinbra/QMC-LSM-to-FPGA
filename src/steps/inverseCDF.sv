
module inverseCDF #(
    parameter int WIDTH              = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT               = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC              = fpga_cfg_pkg::FP_QFRAC,
    parameter int LANE_ID            = 0
)(
    input logic clk,
    input logic rst_n,

    input logic valid_in,
    output logic ready_out,

    input logic signed [WIDTH-1:0] u_in,        // input in [0,1) sobol sequence numbers

    output logic valid_out,
    input logic ready_in,

    output logic signed [WIDTH-1:0] z_out       //  output z-score
);

    localparam signed [WIDTH-1:0] NEG_TWO = -(2 << QFRAC);

    localparam int SQRT_LATENCY         = fpga_cfg_pkg::FP_SQRT_LATENCY
    localparam int MUL_LATENCY          = fpga_cfg_pkg::FP_MUL_LATENCY
    localparam int STEP1_LATENCY        = 1;               // inverseCDF_step1: Single register stage
    localparam int LN_LATENCY           = 2;               // fxlnLUT: LUT read + output reg

    localparam int NEG_DELAY = STEP1_LATENCY + LN_LATENCY + MUL_LATENCY + SQRT_LATENCY;

    //skid buffer
    logic buf_valid;
    logic signed [WIDTH-1:0] buf_u_in;  // Consistent naming
    logic shift_en;
    assign shift_en = ready_in && buf_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 0;
            buf_u_in <= 0;
        end else begin
            if (valid_in && ready_out) begin
                buf_u_in <= u_in;
                buf_valid <= 1;
            end else if (shift_en && barrier_ready) begin
                buf_valid <= 0;
            end
        end
    end


    logic step1_ready, loglut_ready, mul_neg2_ready, sqrt_unit_ready, rational_ready;
    logic barrier_ready;
    logic internal_ready;
    
    assign barrier_ready = step1_ready && loglut_ready && mul_neg2_ready && sqrt_unit_ready && rational_ready;
    assign ready_out = (!buf_valid || barrier_ready);
    assign internal_ready = barrier_ready && ready_in;



    // Step 1: Convert sobol sequence number to (0,0.5] saving 
    logic [WIDTH-1:0] x;
    logic negate;
    logic v1;

    inverseCDF_step1 #() step1 (    //save above or below .5 by whther to negate
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(valid_in),
        .valid_out(v1),
        .ready_in(loglut_ready),
        .ready_out(step1_ready),
        .u(buf_u_in),       //prob
        .x(x),
        .negate(negate)
    );

    // Step 2: find sqrt(y) = sqrt(-2 * ln(x))
    logic [WIDTH-1:0] ln_x;
    logic v2a;

    fxlnLUT #() loglut (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v1),
        .valid_out(v2a),
        .ready_in(mul_neg2_ready),
        .ready_out(loglut_ready),   // connect ready from next stage
        .x(x),
        .ln_out(ln_x)
    );

    logic [WIDTH-1:0] neg2_ln_x;
    logic v2b;

    fxMul #() mul_neg2(
        .clk(clk), 
        .rst_n(rst_n),
        .valid_in(v2a),  
        .valid_out(v2b),
        .ready_in(sqrt_unit_ready),
        .ready_out(mul_neg2_ready)
        .a(ln_x), 
        .b(NEG_TWO),
        .result(neg2_ln_x),
        );   

    logic [WIDTH-1:0] t;
    logic v3;

    fxSqrt #() sqrt_unit (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2b),
        .valid_out(v3),
        .ready_in(rational_ready),
        .ready_out(sqrt_unit_ready),
        .a(neg2_ln_x),
        .sqrt_out(t)
    );

    // Delay negate signal to align with t 
    logic [NEG_DELAY-1:0] negate_pipe;
    generate
        for (genvar i = 0; i < NEG_DELAY; i++) begin //negate delay
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    negate_pipe[i] <= '0;
                end else if (shift_en && ready_in) begin
                    if (i == 0) 
                        negate_pipe[i] <= negate;  // Input from step1
                    else 
                        negate_pipe[i] <= negate_pipe[i-1];  // Shift  
                end
            end
        end
    endgenerate

    // Step 3: Rational approximation (Zelen & Severo)

    fxInvCDF_ZS #(WIDTH, QINT) rational (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v3),
        .valid_out(valid_out),
        .ready_in(ready_in),
        .ready_out(rational_ready),
        .t(t),
        .negate(negate_pipe[NEG_DELAY-1]),
        .z(z_out));

    initial begin   
        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(z_out)) 
            else $error("InvCDF: Stall overwrite");
    end
endmodule

module GBM_step #(
    parameter int WIDTH       = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT        = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC       = fpga_cfg_pkg::FP_QFRAC,
    parameter int DIV_LATENCY = fpga_cfg_pkg::FP_DIV_LATENCY,
    parameter int LANE_ID = 0
)(
    input  logic                       clk,
    input  logic                       rst_n,

    input  logic                       valid_in,
    output logic                       ready_out,
    output logic                       valid_out,
    input  logic                       ready_in,

    input  logic signed [WIDTH-1:0]    z,
    input  logic signed [WIDTH-1:0]    S,
    input  logic signed [WIDTH-1:0]    r,
    input  logic signed [WIDTH-1:0]    sigma,
    input  logic signed [WIDTH-1:0]    dt,
    output logic signed [WIDTH-1:0]    S_next
);
    localparam signed [WIDTH-1:0] ONE = 1 << QFRAC;

    // ----------------------------------------------------------------------
    // 0. One-deep skid buffer to absorb upstream bursts
    // ----------------------------------------------------------------------
    typedef struct packed {
        logic signed [WIDTH-1:0] z;
        logic signed [WIDTH-1:0] S;
        logic signed [WIDTH-1:0] r;
        logic signed [WIDTH-1:0] sigma;
        logic signed [WIDTH-1:0] dt;
    } sample_t;

    sample_t in_buf;
    logic buf_valid;
    logic shift_en = ready_in && buf_valid && (drift_barrier && diffusion_barrier && exp_barrier && mul_price_ready);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            buf_valid <= 0;
            in_buf <= '{0, 0, 0, 0, 0};  // Explicit reset
        end else begin
            if (valid_in && ready_out) begin
                in_buf <= '{z, S, r, sigma, dt};
                buf_valid <= 1;
            end else if (shift_en) begin
                buf_valid <= 0;
            end
        end
    end

    logic mul_sigma2_ready, mul_drift_ready, sqrt_blk_ready, mul_sigma_sqrt_ready, mul_diffusion_ready, explut_ready, recip_ready, mul_price_ready;
    logic drift_barrier = mul_sigma2_ready && mul_drift_ready;
    logic diffusion_barrier = sqrt_blk_ready && mul_sigma_sqrt_ready && mul_diffusion_ready;
    logic exp_barrier = explut_ready && recip_ready;

    assign ready_out = (!buf_valid || (drift_barrier && diffusion_barrier && exp_barrier && mul_price_ready));
    // ----------------------------------------------------------------------
    // 1. DRIFT branch :  (r – 0.5 σ²) * dt
    // ----------------------------------------------------------------------
    logic drift_v_in = buf_valid && shift_en;
    logic drift_v_mid, drift_v_out;
    logic signed [WIDTH-1:0] sigma2, half_sigma2, drift;
    

    fxMul #(.LATENCY(2)) mul_sigma2 (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (drift_v_in),
        .ready_out (mul_sigma2_ready),
        .valid_out (drift_v_mid),
        .ready_in  (mul_drift_ready),  // Chain to next mul in branch
        .a         (in_buf.sigma),
        .b         (in_buf.sigma),
        .result    (sigma2)
    );

    assign half_sigma2 = sigma2 >>> 1;   // multiply by 0.5 via shift
    

    fxMul #(.LATENCY(2)) mul_drift (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (drift_v_mid), 
        .valid_out  (drift_v_out),
        .ready_in   (join_ready),
        .ready_out  (mul_drift_ready), 
        .a          (in_buf.r - half_sigma2), 
        .b          (in_buf.dt),
        .result     (drift)
    );

    // ----------------------------------------------------------------------
    // 2. DIFFUSION branch : σ √dt · z
    // ----------------------------------------------------------------------
    logic diff_v_in = buf_valid;
    logic diff_v_mid1, diff_v_mid2, diff_v_out;
    logic signed [WIDTH-1:0] sqrt_dt, sigma_sqrt_dt, diffusion;

    fxSqrt #() sqrt_blk (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (diff_v_in),  
        .valid_out  (diff_v_mid1), 
        .ready_in   (mul_sigma_sqrt_ready),
        .ready_out  (sqrt_blk_ready),
        .a          (in_buf.dt),
        .result   (sqrt_dt)
    );

    logic diff2_v, diff2_r;
    fxMul #(.LATENCY(2)) mul_sigma_sqrt (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (diff_v_mid1), 
        .valid_out  (diff_v_mid2),    
        .ready_in   (mul_diffusion_ready),
        .ready_out  (mul_sigma_sqrt_ready),
        .a          (sqrt_dt), 
        .b          (in_buf.sigma),
        .result     (sigma_sqrt_dt)
    );

    fxMul #(.LATENCY(2)) mul_diffusion (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (diff_v_mid2), 
        .valid_out  (diff_v_out), 
        .ready_in   (join_ready),
        .ready_out  (mul_diffusion_ready),
        .a          (sigma_sqrt_dt), 
        .b          (in_buf.z),
        .result     (diffusion)
    );

    // ----------------------------------------------------------------------
    // 3. Join drift + diffusion  (requires both branches ready)
    // ----------------------------------------------------------------------
    (* preserve = 1 *) logic join_valid = drift_v_out && diff_v_out; //preservatin for retiming
    logic join_ready;
    assign join_ready = drift_barrier && diffusion_barrier && mul_price_ready; //barrier ready

    logic signed [WIDTH-1:0] exp_arg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            exp_arg <= '0;
        else if (join_valid && join_ready)
            exp_arg <= (drift + diffusion > (1 <<< (WIDTH-1)-1)) ? (1 <<< (WIDTH-1)-1) : drift + diffusion;
            //basically just a catch but it means 
            //exp_arg <= drift + diffusion;
    end

    // ----------------------------------------------------------------------
    // 4.  e^(exp_arg)  (CORDIC-lite LUT) and reciprocal for negative arg
    // ----------------------------------------------------------------------
    logic signed [WIDTH-1:0] abs_arg;
    logic sign_bit;

    assign sign_bit = exp_arg[WIDTH-1];
    assign abs_arg  = sign_bit ? -exp_arg : exp_arg;

    logic exp_v, recip_v;
    logic signed [WIDTH-1:0] e_pos, e_neg;

    fxExpLUT #() explut (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (join_valid), 
        .valid_out  (exp_v),      
        .ready_in   (recip_ready),
        .ready_out  (explut_ready),
        .a          (abs_arg),
        .result     (e_pos)
    );

    fxDiv #() recip (
        .clk(clk), .rst_n(rst_n),
        .valid_in       (exp_v),   
        .valid_out      (recip_v), 
        .ready_in       (mul_price_ready),
        .ready_out      (recip_ready),
        .numerator      (ONE),  // 1.0 in Q format
        .denominator    (e_pos),
        .result         (e_neg)
    );

    logic signed [WIDTH-1:0] e_final = sign_bit ? e_neg : e_pos;

    // ----------------------------------------------------------------------
    // 5.  Final price  S_next = S · e^(drift+diff)
    // ----------------------------------------------------------------------
    fxMul #(.LATENCY(2)) mul_price (
        .clk(clk), .rst_n(rst_n),
        .valid_in   (recip_v),  
        .valid_out  (valid_out), 
        .ready_in   (ready_in),
        .ready_out  (mul_price_ready),
        .a          (e_final), 
        .b          (in_buf.S),
        .result     (S_next)
    );
    initial begin
        assert property (@(posedge clk) sigma2 >= 0) 
            else $error("Negative sigma2 in GBM");

        assert property (@(posedge clk) disable iff (!rst_n) valid_out && !ready_in |=> $stable(S_next)) 
            else $error("GBM: Backpressure violation");
        
        assert property (@(posedge clk) disable iff (!rst_n) (drift_v_out != diff_v_out) |-> ##1 !join_valid) 
            else $error("GBM: Lagging branch");
        
    end
endmodule

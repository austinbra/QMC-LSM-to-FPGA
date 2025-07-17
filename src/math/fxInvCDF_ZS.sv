//-----------------------------------------------------------
// Approximates Z score using Zelen & Severo rational polynomial
//-----------------------------------------------------------

module fxInvCDF_ZS #(
    parameter int WIDTH                 = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT                  = fpga_cfg_pkg::FP_QINT,
    parameter int QFRAC                 = fpga_cfg_pkg::FP_QFRAC,
    parameter int MUL_LATENCY           = fpga_cfg_pkg::FP_MUL_LATENCY,
    parameter int DIV_LATENCY           = fpga_cfg_pkg::FP_DIV_LATENCY
    )(
    input logic clk,
    input logic rst_n,

    input logic valid_in,
    output logic valid_out,
    input logic ready_in,
    output logic ready_out,

    input logic [WIDTH-1:0] t,          //  input from sqrt module
    input logic negate,                 // negate flag in step 1
    
    output logic signed [WIDTH-1:0] z   //  z-score
);

    // pre determined constants 
    // C0 ≈ 2.515517 = 2 + (0.515517 * 2^QFRAC)
    localparam signed [WIDTH-1:0] C0 = (2 <<< QFRAC) + ((515517 * (1 <<< QFRAC)) / 1000000);
    localparam signed [WIDTH-1:0] C1 = (802853 * (1 <<< QFRAC)) / 1000000; // C1 ≈ 0.802853 = 0 + (0.802853 * 2^QFRAC)
    localparam signed [WIDTH-1:0] C2 = (10328 * (1 <<< QFRAC)) / 1000000; // C2 ≈ 0.010328 = 0 + (0.010328 * 2^QFRAC)

    localparam signed [WIDTH-1:0] D1 = (1 <<< QFRAC) + ((432788 * (1 <<< QFRAC)) / 1000000); // D1 ≈ 1.432788 = 1 + (0.432788 * 2^QFRAC)
    localparam signed [WIDTH-1:0] D2 = (189269 * (1 <<< QFRAC)) / 1000000; // D2 ≈ 0.189269 = 0 + (0.189269 * 2^QFRAC)
    localparam signed [WIDTH-1:0] D3 = (1308 * (1 <<< QFRAC)) / 1000000; // D3 ≈ 0.001308 = 0 + (0.001308 * 2^QFRAC)

    localparam signed [WIDTH-1:0] ONE = 1 <<< QFRAC;


    logic [WIDTH-1:0] mul_t3_ready, mul_t2_ready, mul_c1t_ready, mul_c2t2_ready, mul_d1t_ready, mul_d2t2_ready, mul_d3t3_ready, div_nd_ready;
    wire barrier_ready = mul_t2_ready && mul_c1t_ready && mul_c2t2_ready && mul_d1t_ready && mul_d2t2_ready && mul_d3t3_ready && div_nd_ready;
    assign ready_out = barrier_ready && (ready_in || !skid_valid); 
    
//skid buffer
    logic v0;
    logic skid_valid, skid_negate;
    logic [WIDTH-1:0] skid_t;
    wire accept = valid_in && ready_out && !skid_valid;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            skid_valid <= 0;
        end else if (accept) begin
            skid_t <= t;
            skid_negate <= negate;
            skid_valid <= 1;
        end else if (ready_in && skid_valid) 
            skid_valid <= '0;  // Drain on ready
    end
    logic [WIDTH-1:0] t_eff = skid_valid ? skid_t : t;
    logic negate_eff = skid_valid ? skid_negate : negate;

    assign v0 = (skid_valid || valid_in) && barrier_ready;

// Multipliers
    logic v1a, v1b;       // valid_out of stage 1
    logic [WIDTH-1:0] t2, t3;
    

    fxMul #() mul_t_t (
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v0),
        .valid_out (v1a),
        .ready_in  (ready_in),
        .ready_out (mul_t2_ready),
        .a         (t_eff),
        .b         (t_eff),
        .result    (t2)
    );

    fxMul #() mul_t_t2(
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v1a),
        .valid_out (v1b),
        .ready_in  (barrier_ready),
        .ready_out (mul_t3_ready),
        .a         (t_eff),
        .b         (t2),
        .result    (t3)
    );  // t^3

// Numerator: C0 + C1 * t + C2 * t2
    logic v2a, v2b;
    logic [WIDTH-1:0] c1t, c2t2, num;

    fxMul #() mul_c1t(
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v0),
        .valid_out (v2a),
        .ready_in  (barrier_ready),
        .ready_out (mul_c1t_ready),
        .a         (C1),
        .b         (t_eff),
        .result    (c1t)
    );

    fxMul #() mul_c2t2(        
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v1a),
        .valid_out (v2b),
        .ready_in  (barrier_ready),
        .ready_out (mul_c2t2_ready),
        .a         (C2),
        .b         (t2),
        .result    (c2t2)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            num <= '0;
        end else if (v2b && barrier_ready && ready_in) begin
            num <= C0 + c1t + c2t2;
        end
    end
    
// Denominator: 1 + D1 * t + D2 * t2 + D3 * t3
    logic v3a, v3b, v3c;
    logic [WIDTH-1:0] d1t, d2t2, d3t3, den;

    fxMul #() mul_d1t(
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v0),
        .valid_out (v3a),
        .ready_in  (barrier_ready),
        .ready_out (mul_d1t_ready),
        .a         (D1),
        .b         (t_eff),
        .result    (d1t)
    );

    fxMul #() mul_d2t2(
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v1a),
        .valid_out (v3b),
        .ready_in  (barrier_ready),
        .ready_out (mul_d2t2_ready),
        .a         (D2),
        .b         (t2),
        .result    (d2t2)
    );

    fxMul #() mul_d3t3(
        .clk       (clk),
        .rst_n     (rst_n),
        .valid_in  (v1b),
        .valid_out (v3c),
        .ready_in  (barrier_ready),
        .ready_out (mul_d3t3_ready),
        .a         (D3),
        .b         (t3),
        .result    (d3t3)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            den <= '0;
        end else if (v3c && barrier_ready && ready_in) begin
            den <= ONE + d1t + d2t2 + d3t3;
        end
    end

// Divide numerator by denominator
    logic v4;
    logic [WIDTH-1:0] ratio;
    fxDiv #() div_nd (
        .clk        (clk),
        .rst_n      (rst_n),
        .valid_in   (v3c),
        .valid_out  (v4),
        .ready_in   (ready_in),
        .ready_out  (div_nd_ready),
        .numerator  (num),
        .denominator(den),
        .result     (ratio)
    );
    
// piplin the negate flag through 5 stages 
    localparam int INV_LATENCY = 3*MUL_LATENCY + DIV_LATENCY;
    logic [INV_LATENCY-1:0] negate_pipe;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            negate_pipe <= '0;
        else
            negate_pipe <= {negate_pipe[INV_LATENCY-2:0], v0 ? negate_eff : 1'd0};
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            z <= '0;
            valid_out <= '0;
        end else begin
            if (v4 && ready_in) begin
                valid_out <= 1;
                z <= negate_pipe[INV_LATENCY-1] ? -(t_eff - ratio) : (t_eff - ratio);
            end else 
                valid_out <= '0';
        end
    end

    initial begin
        assert property (@(posedge clk) disable iff (!rst_n) !ready_out |-> !valid_out) 
            else $error("Output valid while not ready");

        assert property (@(posedge clk) disable iff (!rst_n) v4 && barrier_ready |-> $stable(num) && $stable(den)) 
            else $error("Desync on partial stall");

        assert property (@(posedge clk) disable iff (!rst_n) v4 |-> $stable(negate_pipe)) 
            else $error("Negate pipe misaligned"); //if submodules have variable latency, misalignment could negate wrong

        assert property (@(posedge clk) disable iff (!rst_n) !ready_in |-> !barrier_ready) 
            else $error("Barrier not respecting downstream stall");
    end
endmodule
// Blocks:
//   Sobol  ->  inverseCDF  ->  GBM_step  ->  regression3x3 ->  lsm_decision  ->  uart_bridge

module top_mc_option_pricer #(
    parameter int WIDTH = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT  = fpga_cfg_pkg::FP_QINT
)(
    input  logic clk_100,     // on-board 100 MHz
    input  logic rst_btn_n,   // push-button reset
    input  logic uart_rxd,
    output logic uart_txd
);

    // clocking: assume PLL creates fast_clk = 200 MHz
    logic fast_clk;
    // TODO: Instantiate MMCM/PLL if you need faster clock

    // -------------- UART bridge ----------------
    uart_bridge #(.DEPTH(1024)) link (
        .fast_clk(fast_clk),
        .rst_n(rst_btn_n),
        .core_tx_valid(tx_valid), 
        .core_tx_data(tx_data), 
        .core_tx_ready(tx_ready),
        .core_rx_valid(rx_valid), 
        .core_rx_data(rx_data), 
        .core_rx_ready(rx_ready),
        .uart_clk(clk_100), 
        .uart_rxd(uart_rxd), 
        .uart_txd(uart_txd));

    // Decode incoming parameter words (r, sigma, strike, etc.)
    // Broadcast constants; drive seed into Sobol.
    // TODO: small control FSM / CSR block

    // -------------- Monte-Carlo datapath ----------------
    logic sob_valid, z_valid, gbm_valid, reg_valid, lsm_valid;

    // Sobol
    sobol #(.M(M)) sobol_i (
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(sob_valid),
		.N(N),
		.dim_in(dim_in),
		.valid_out(z_valid),
		.sobol_out(sobol_out)
    );

    // inverse CDF
    inverseCDF #() invcdf_i (
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(z_valid),
		.u_in(sobol_out),
		.valid_out(gbm_valid),
		.z_out(z)
    );

    // GBM step
    GBM_step #() gbm_i (
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(gbm_valid),
		.z(z),
		.S_0(S_0),
		.r(r),
		.sigma(sigma),
		.t(t),
		.valid_out(reg_valid),
		.S_t(S_t)
    );

    // Regression accumulator + solver (one per exercise date)
    accumulator #() regress_i (
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(reg_valid),
		.x_in(S_t),
		.y_in(y_in),
		.valid_out(lsm_valid),
		.beta(beta),
		.solver_ready(solver_ready)
    );

    // Longstaff-Schwartz decision
    lsm_decision #() lsm_i (
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(lsm_valid),
		.S_t(S_t),
		.beta(beta),
		.strike(strike),
		.disc(disc),
		.valid_out(mean_ready),
		.PV(PV)
    );

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PV <= '0; 
        end
        else if (mean_ready) begin
            PV <= PV + extended(x_in);
        end
    end
    logic done;
    logic [WIDTH-1:0] cash_flow;
    fxDiv #() div (
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2),
        .numerator(PV),
        .denominator(N),
        .result(cash_flow),
        .valid_out(done));

    // e.g. send cash_flow words to PC
    assign tx_valid = lsm_valid;
    assign tx_data  = cash_flow;

endmodule


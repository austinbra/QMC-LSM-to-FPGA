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
    uart_bridge #(.DEPTH(1024)) link (										//get inputs for all others
        .fast_clk(fast_clk),												//choose if i want complie time or to input all values from UART
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
    sobol #(.M(M)) sobol_i (									//fully understand
        .clk(clk),
		.rst_n(rst_n),
		.valid_in(sob_valid),
		.idx_in(idx_in),
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
		.y_in(y_in), 															//what is
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
		.disc(disc),															//calculate before inputting = exp( r * t_i * delta_t)
		.valid_out(mean_ready),
		.PV(PV)
    );
	
	logic [WIDTH-1:0] count;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PV <= '0; 
			count <= '0;
        end
        else if (mean_ready) begin
            PV <= PV + extended(x_in);
			count <= count + 1;
        end
    end
    logic done;
    logic [WIDTH-1:0] cash_flow;
    fxDiv #() div (													//only run once count == number of time steps
        .clk(clk),
        .rst_n(rst_n),
        .valid_in(v2),
        .numerator(PV),
        .denominator(N),
        .result(cash_flow),
        .valid_out(done));


	always_ff @(posedge clk or negedge rst_n) begin 							//implement
        if (!rst_n) begin
            state <= IDLE; start_solver<=0; valid_out<=0;
        end else case (state)
            IDLE:
                if (count == N_SAMPLES) begin
                    // Row 0
                    mat_flat[0]=sum1; 
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
                
            WAIT: 
                
        endcase
    end




    // e.g. send cash_flow words to PC
    assign tx_valid = lsm_valid;
    assign tx_data  = cash_flow;

endmodule


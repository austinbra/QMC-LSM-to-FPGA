// 3×3 regression via Gaussian elimination, pipelined & fixed-point-aware

module regression3x3 #(
    parameter WIDTH         = 32,
    parameter MUL_LATENCY   = 1,
    parameter DIV_LATENCY   = 1
)(
    // Clock, reset, start
    input  logic                    clk,
    input  logic                    rst_n, //active low reset
    input  logic                    start,

    // Input matrices
    input  logic signed [WIDTH-1:0] A_flat [0:8],
    input  logic signed [WIDTH-1:0] B_flat [0:2],

    // Outputs
    output logic                    done,   // signals when regression is complete
    output logic signed [WIDTH-1:0] beta [0:2] // solution vector
);

    localparam int Qint  = 16;
    localparam int Qfrac = WIDTH - Qint;


    // FSM state definitions
    typedef enum logic [3:0]{
        S_IDLE,
        S_LOAD,
        S_PIVOT0,
        S_NORMALIZE0,
        S_ELIM0,
        S_PIVOT1,
        S_NORMALIZE1,
        S_ELIM1,
        S_BACKSUB,
        S_DONE
    } state_t;

    // Internal state & next_state
    state_t current_state, next_state;
    
    // Augmented matrix storage (Q16.16 format)
    logic signed [WIDTH-1:0] augmented [0:2][0:3];


    //-----------------------------------------------------------
    // combinationaly pick the row where |augmented[row][0]| is biggest
    //-----------------------------------------------------------
    logic [1:0]                 pivot0_row;
    logic signed [WIDTH-1:0]    tmp;

    always_comb begin
    pivot0_row = 0;
    if ( (augmented[1][0][WIDTH-1] ? -augmented[1][0] : augmented[1][0])
        > (augmented[pivot0_row][0][WIDTH-1] ? -augmented[pivot0_row][0] : augmented[pivot0_row][0]) )
        pivot0_row = 1;
    if ( (augmented[2][0][WIDTH-1] ? -augmented[2][0] : augmented[2][0])
        > (augmented[pivot0_row][0][WIDTH-1] ? -augmented[pivot0_row][0] : augmented[pivot0_row][0]) )
        pivot0_row = 2;
    end

    //-----------------------------------------------------------
    // Normalize Row 0
    //-----------------------------------------------------------
    logic [1:0]                 norm0_col_idx;
    logic                       norm0_active;
    logic signed [WIDTH-1:0]    div0_numer, div0_denom, norm0_result;
    logic                       div0_start, div0_done;

    // compute numerator & denominator before driving fxDiv
    always_comb begin
      div0_numer = augmented[0][norm0_col_idx];
      div0_denom = augmented[0][0];
    end

    fxDiv #(.WIDTH(WIDTH), .LATENCY(DIV_LATENCY)) normalize0_div (
      .clk        (clk),
      .rst        (rst_n),
      .start      (div0_start),
      .numerator  (div0_numer),
      .denominator(div0_denom),
      .result     (norm0_result),
      .done       (div0_done)
    );

    //-----------------------------------------------------------
    // Eliminate Column 0 (row 1 & 2)
    //-----------------------------------------------------------
    logic [1:0]                 elim0_row, elim0_col_idx;
    logic                       elim0_active;
    logic signed [WIDTH-1:0]    mul0_a, mul0_b, elim0_result;
    logic                       mul0_start, mul0_done;

    assign mul0_a = augmented[elim0_row][0];
    assign mul0_b = augmented[0][elim0_col_idx];

    fxMul #(.WIDTH(WIDTH), .LATENCY(MUL_LATENCY)) elim0_mul (
      .clk    (clk),
      .rst    (rst_n),
      .start  (mul0_start),
      .a      (mul0_a),
      .b      (mul0_b),
      .result (elim0_result),
      .done   (mul0_done)
    );

    //-----------------------------------------------------------
    // Normalize Row 1
    //-----------------------------------------------------------
    logic [1:0]              norm1_col_idx;
    logic                    norm1_active;
    logic signed [WIDTH-1:0] div1_numer, div1_denom, norm1_result;
    logic                    div1_start, div1_done;

    always_comb begin
      div1_numer = augmented[1][norm1_col_idx];
      div1_denom = augmented[1][1];
    end

    fxDiv #(.WIDTH(WIDTH), .LATENCY(DIV_LATENCY)) normalize1_div (
      .clk        (clk),
      .rst        (rst_n),
      .start      (div1_start),
      .numerator  (div1_numer),
      .denominator(div1_denom),
      .result     (norm1_result),
      .done       (div1_done)
    );

    //-----------------------------------------------------------
    // Eliminate Column 1 (row 2)
    //-----------------------------------------------------------
    logic [1:0]                 elim1_col_idx;
    logic                       elim1_active;
    logic signed [WIDTH-1:0]    mul1_a, mul1_b, elim1_result;
    logic                       mul1_start, mul1_done;

    assign mul1_a = augmented[2][1];
    assign mul1_b = augmented[1][elim1_col_idx];

    fxMul #(.WIDTH(WIDTH), .LATENCY(MUL_LATENCY)) elim1_mul (
      .clk    (clk),
      .rst    (rst_n),
      .start  (mul1_start),
      .a      (mul1_a),
      .b      (mul1_b),
      .result (elim1_result),
      .done   (mul1_done)
    );

    
    //-----------------------------------------------------------
    // Back-substitution signals
    //-----------------------------------------------------------
    logic signed [WIDTH-1:0]    bs_a, bs_b;
    logic [1:0]                 bs_step;

    // separate active & start flags for div (step 0) vs mul (steps 1/2)
    logic                        bs_active;
    logic                        bs_start;
    wire                         bs_done;
    wire signed [WIDTH-1:0]      bs_result;


    fxMul #(.WIDTH(WIDTH), .LATENCY(MUL_LATENCY)) backsub_mul (
      .clk    (clk),
      .rst    (rst_n),
      .start  (bs_start),
      .a      (bs_a),
      .b      (bs_b),
      .result (bs_result),
      .done   (bs_done)
    );

    //-----------------------------------------------------------
    // FSM: combinational next_state
    //-----------------------------------------------------------
    always_comb begin
        next_state = S_IDLE;
        unique case (current_state)
            S_IDLE:         next_state = start ? S_LOAD : S_IDLE;
            S_LOAD:         next_state = S_PIVOT0;
            S_PIVOT0:       next_state = S_NORMALIZE0;
            S_NORMALIZE0:   next_state = norm0_active  ? S_NORMALIZE0 : S_ELIM0;
            S_ELIM0:        next_state = S_PIVOT1;
            S_PIVOT1:       next_state = S_NORMALIZE1;
            S_NORMALIZE1:   next_state = norm1_active ? S_NORMALIZE1 : S_ELIM1;
            S_ELIM1:        next_state = S_BACKSUB;
            S_BACKSUB:      next_state = bs_step == 3 ? S_DONE : S_BACKSUB;
            S_DONE:         next_state = S_IDLE;
            default:        ; //catch all

        endcase
    end

    //-----------------------------------------------------------
    // FSM state
    //-----------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
        current_state <= S_IDLE;
      end else begin
        current_state <= next_state;
      end
    end


    //-----------------------------------------------------------
    // FSM main behavior block
    //-----------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            //rst all control signals
            done <= 1'b0;

            //normalize row 0
            norm0_active <= 1'b0;
            norm0_col_idx <= 2'b0;
            div0_start <= 1'b0;

            //elim col 0
            elim0_active <= 1'b0;
            elim0_row <= 2'b0;
            elim0_col_idx <= 2'b0;
            mul0_start <= 1'b0;

            //normalize row 1
            norm1_active <= 1'b0;
            norm1_col_idx <= 2'b0;
            div1_start <= 1'b0;

            //elim col 1
            elim1_active    <= 1'b0;
            elim1_col_idx   <= 2'd1;
            mul1_start      <= 1'b0;

            // back substitution
            bs_active <= 1'b0;
            bs_step    <= 2'd0;
            bs_start  <= 1'b0;
        end else begin
            //default, deassert all the starts and dones
            done <= 0;
            div0_start <= 1'b0;
            mul0_start <= 1'b0;
            div1_start <= 1'b0;
            mul1_start <= 1'b0;
            bs_start <= 1'b0;

            unique case(current_state)
                S_LOAD: begin
                    // load A_flat & B_flat into the augmented matrix
                    for (int i = 0; i < 3; ++i) begin
                        for (int j = 0; j < 3; ++j) begin
                            augmented[i][j] <= A_flat[i*3 + j];
                        end
                        augmented[i][3] <= B_flat[i];
                    end
                    done <= 0;
                end


                S_PIVOT0: begin
                    if (pivot0_row != 0) begin
                    // switch row 0 with pivot0_row
                    for (int c = 0; c < 4; c++) begin
                        tmp <= augmented[0][c];
                        augmented[0][c] <= augmented[pivot0_row][c];
                        augmented[pivot0_row][c] <= tmp;
                    end
                    end
                end


                S_NORMALIZE0: begin
                    if(!norm0_active) begin
                        norm0_active <= 1;
                        norm0_col_idx <= 0;
                        div0_start <= 1;
                    end else if (div0_done) begin
                        //get result and start the next one
                        augmented[0][norm0_col_idx] <= norm0_result;
                        if (norm0_col_idx == 3) ///can omit the begin and end since its only one line
                            norm0_active <= 0;
                        else begin 
                            norm0_col_idx <= (norm0_col_idx + 1'b1) & 2'b11;//weird system verilog syntaxing
                            div0_start <= 1;
                        end
                    end
                end

                S_ELIM0: begin
                    if(!elim0_active) begin
                        elim0_active <= 1;
                        elim0_row <= 1;
                        elim0_col_idx <= 1;
                        mul0_start <= 1;
                    end else if (mul0_done) begin
                        //augmented[r][c] <- augmented[r][c] – (augmented[r][pivot_col] * augmented[pivot_row][c])
                        augmented[elim0_row][elim0_col_idx] <= augmented[elim0_row][elim0_col_idx] - elim0_result;
                        if (elim0_col_idx == 3) begin
                            if (elim0_row == 2)
                                elim0_active <= 0;
                            else begin 
                                elim0_row <= elim0_row + 1;
                                elim0_col_idx <= 0;
                                mul0_start <= 1;
                            end
                        end else begin
                            elim0_col_idx <= (elim0_col_idx + 1'b1) & 2'b11;
                            mul0_start <= 1;
                        end
                    end
                end


                S_NORMALIZE1: begin
                    if(!norm1_active) begin
                        norm1_active <= 1;
                        norm1_col_idx <= 1;
                        div1_start <= 1;
                    end else if (div1_done) begin
                        augmented[1][norm1_col_idx] <= norm1_result;
                        if (norm1_col_idx == 3)
                            norm1_active <= 0;
                        else begin 
                            norm1_col_idx <= (norm1_col_idx + 1'b1) & 2'b11;
                            div1_start <= 1;
                        end
                    end
                end

                S_ELIM1: begin
                    if(!elim1_active) begin
                        elim1_active <= 1;
                        //elim1_row is only 1 row this time so uneeded
                        elim1_col_idx <= 1;
                        mul1_start <= 1;
                    end else if (mul1_done) begin
                        augmented[2][elim1_col_idx] <= augmented[2][elim1_col_idx] - elim1_result;
                        if (elim1_col_idx == 3)
                            elim1_active <= 0;
                        else begin
                            elim1_col_idx <= (elim1_col_idx + 1'b1) & 2'b11;
                            mul1_start <= 1;
                        end
                    end
                end

                S_BACKSUB: begin
                    case (bs_step)
                        0: begin
                            // inline Q16.16 divide: (aug[2][3] / (aug[2][2]>>>Qfrac)) produces beta 2
                            beta[2]  <= augmented[2][3] / (augmented[2][2] >>> Qfrac);
                            bs_step  <= 1;
                        end

                        1: begin
                            // compute (aug[1][3] - aug[1][2]*beta2) by multiply then subtract
                            if (!bs_active) begin
                                bs_active <= 1;
                                bs_start  <= 1;
                                bs_a       <= augmented[1][2];
                                bs_b       <= beta[2];
                            end
                            else if (bs_done) begin
                                bs_active <= 0;
                                beta[1]    <= augmented[1][3] - bs_result;
                                bs_step    <= 2;
                            end
                        end

                        2: begin
                            // compute (aug[0][3] - aug[0][1]*beta1)
                            if (!bs_active) begin
                                bs_active <= 1;
                                bs_start  <= 1;
                                bs_a       <= augmented[0][1];
                                bs_b       <= beta[1];
                            end
                            else if (bs_done) begin
                                bs_active <= 0;
                                beta[0]    <= augmented[0][3] - bs_result;
                                bs_step    <= 3;
                            end
                        end
                        default: ;
                    endcase
                    end


                S_DONE: begin
                    done <= 1;
                end

                default:     ;//no operatons
            endcase
        end                
    end

    
    // sim display
    always @(posedge clk) begin
        if (done) begin
            $display("Regression Done.");
            $display("beta[0] = %0d", beta[0]);
            $display("beta[1] = %0d", beta[1]);
            $display("beta[2] = %0d", beta[2]);
        end
    end

    always @(posedge clk) begin
        $display("FSM state: %0d", current_state);
    end

endmodule

//cd ~/verilator_regression or mkdir
//cp /mnt/c/Users/atxbr/Documents/GitHub/QMC-LSM-to-FPGA/src/regression3x3.sv .
//verilator -Wall --cc regression3x3.sv fxMul.sv fxDiv.sv --exe regression3x3_tb.cpp
//make -C obj_dir -j -f Vregression3x3.mk Vregression3x3
// obj_dir/Vregression3x3
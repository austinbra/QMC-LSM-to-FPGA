// 3×3 regression via Gaussian elimination, pipelined & fixed-point-aware

module solveRegression3x3 #(
    parameter WIDTH         = 32,
    parameter MUL_LATENCY   = 2,
    parameter DIV_LATENCY   = 3
)(
    // Clock, reset, start
    input  logic                         clk,
    input  logic                         rst,
    input  logic                         start,

    // Input matrices
    input  logic signed [WIDTH-1:0]      A_flat [0:8],
    input  logic signed [WIDTH-1:0]      B_flat [0:2],

    // Outputs
    output logic                         done,   // signals when regression is complete
    output logic signed [WIDTH-1:0]      beta [0:2] // solution vector
);

    // FSM state definitions
    //-----------------------------------------------------------
    localparam IDLE               = 4'd0;
    localparam LOAD               = 4'd1;
    localparam PIVOT_ROW_0        = 4'd2;
    localparam NORMALIZE_ROW_0    = 4'd3;
    localparam ELIMINATE_COLUMN_0 = 4'd4;
    localparam PIVOT_ROW_1        = 4'd5;
    localparam NORMALIZE_ROW_1    = 4'd6;
    localparam ELIMINATE_COLUMN_1 = 4'd7;
    localparam BACK_SUB           = 4'd8;
    localparam DONE               = 4'd9;

    // Internal state & next_state
    //-----------------------------------------------------------
    logic [3:0] state, next_state;

    // Augmented matrix storage (Q16.16 format)
    //-----------------------------------------------------------
    logic signed [WIDTH-1:0] augmented [0:2][0:3];

    // Normalization signals (scaling a pivot row to 1)
    //-----------------------------------------------------------
    // renamed from norm_col to make it clear this is an index
    logic          [1:0]                   normalize_col_idx;
    logic                                  normalize_active;
    wire signed   [WIDTH-1:0]              norm_result;         // from fxDiv (divides two Q16.16s → Q16.16)

    // intermediate values for divider
    logic signed  [WIDTH-1:0]              numerator;
    logic signed  [WIDTH-1:0]              denominator;
    logic          [1:0]                   current_row;
    logic          [1:0]                   pivot_col;

    logic                                  div_start;
    logic          [1:0]                   div_counter;
    logic                                  div_done;

    // compute numerator & denominator before driving fxDiv
    always_comb begin
        numerator   = augmented[current_row][normalize_col_idx];
        denominator = augmented[current_row][pivot_col];
    end

    fxDiv #(WIDTH, 31) div0 (
        .numerator   (numerator),
        .denominator (denominator),
        .result      (norm_result)
    );

    // First elimination (row-0 subtract) signals
    //-----------------------------------------------------------
    logic          [1:0]                   mul_counter;
    logic                                  mul_start;
    logic                                  mul_done;

    logic          [1:0]                   elim_row;
    logic          [1:0]                   elim_col;
    logic                                  elimination_active;

    wire signed   [WIDTH-1:0]              elim_mul_result;     // from fxMul

    fxMul #(WIDTH) mul0 (
        .a      (augmented[elim_row][0]),
        .b      (augmented[0][elim_col]),
        .result (elim_mul_result)
    );

    // Second elimination (row-1 → row-2)
    //-----------------------------------------------------------
    wire signed [WIDTH-1:0]                elim2_factor = augmented[2][1];
    wire signed [WIDTH-1:0]                elim2_product;      // from fxMul

    fxMul #(WIDTH) mul_col1 (
        .a      (elim2_factor),
        .b      (augmented[1][elim_col]),
        .result (elim2_product)
    );

    
    // Back-substitution signals
    //-----------------------------------------------------------
    logic signed [WIDTH-1:0]                bs_mul_a;
    logic signed [WIDTH-1:0]                bs_mul_b;
    wire signed  [WIDTH-1:0]                bs_mul_result;      // from fxMul

    logic signed [WIDTH-1:0]                acc;                 // partial RHS during back-sub
    // renamed from bs_step to make clear this tracks back-sub stages
    logic          [1:0]                   backsub_stage;

    fxMul #(WIDTH) bs_mul (
        .a      (bs_mul_a),                // assigned below
        .b      (bs_mul_b),                // assigned below
        .result (bs_mul_result)
    );

    
    // FSM: combinational next_state
    //-----------------------------------------------------------
    always_comb begin
        case (state)
            IDLE:               next_state = start ? LOAD : IDLE;
            LOAD:               next_state = PIVOT_ROW_0;
            PIVOT_ROW_0:        next_state = NORMALIZE_ROW_0;
            NORMALIZE_ROW_0:    next_state = (normalize_active && normalize_col_idx < 4)
                                         ? NORMALIZE_ROW_0
                                         : ELIMINATE_COLUMN_0;
            ELIMINATE_COLUMN_0: next_state = PIVOT_ROW_1;
            PIVOT_ROW_1:        next_state = NORMALIZE_ROW_1;
            NORMALIZE_ROW_1:    next_state = (normalize_active && normalize_col_idx < 4)
                                         ? NORMALIZE_ROW_1
                                         : ELIMINATE_COLUMN_1;
            ELIMINATE_COLUMN_1: next_state = BACK_SUB;
            BACK_SUB:           next_state = DONE;
            DONE:               next_state = IDLE;
            default:            next_state = IDLE;
        endcase
    end

    
    // FSM: sequential state + handshake counters
    //-----------------------------------------------------------
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state       <= IDLE;
            div_counter <=  0; div_done <= 1'b0; div_start <= 1'b0;
            mul_counter <=  0; mul_done <= 1'b0; mul_start <= 1'b0;
        end else begin
            state <= next_state;

            // divider timing FSM
            if (div_start) begin
                div_counter <= 1;  div_done <= 1'b0;  div_start <= 1'b0;
            end else if (div_counter != 0) begin
                div_counter <= div_counter + 1;
                if (div_counter == DIV_LATENCY)
                    div_done <= 1'b1;
            end else begin
                div_done <= 1'b0;
            end

            // multiplier timing FSM
            if (mul_start) begin
                mul_counter <= 1;  mul_done <= 1'b0;  mul_start <= 1'b0;
            end else if (mul_counter != 0) begin
                mul_counter <= mul_counter + 1;
                if (mul_counter == MUL_LATENCY)
                    mul_done <= 1'b1;
            end else begin
                mul_done <= 1'b0;
            end
        end
    end

    
    // Loop variables & issued_div flag
    //-----------------------------------------------------------
    integer                                i, j, row, column;
    logic          [1:0]                   best_row;
    logic signed   [WIDTH-1:0]             best_val, curr_val;
    logic                                  issued_div;

    
    // FSM: main behavior block
    //-----------------------------------------------------------
    always_ff @(posedge clk) begin
        case (state)
            IDLE: begin
                done               <= 1'b0;
                normalize_col_idx  <= 0;
                normalize_active   <= 1'b0;
                elim_row           <= 1;
                elim_col           <= 0;
                elimination_active <= 1'b0;
                backsub_stage      <= 0;
                issued_div         <= 1'b0;
            end

            LOAD: begin
                done <= 1'b0;
                for (i = 0; i < 3; i++) begin
                    for (j = 0; j < 3; j++)
                        augmented[i][j] <= A_flat[i*3 + j];
                    augmented[i][3] <= B_flat[i];  // attach B as last column
                end
            end

            PIVOT_ROW_0: begin
                done      <= 1'b0;
                best_row  <= 0;
                best_val  <= (augmented[0][0] < 0)
                             ? -augmented[0][0]
                             :  augmented[0][0];
                for (row = 1; row < 3; row++) begin
                    curr_val = (augmented[row][0] < 0)
                               ? -augmented[row][0]
                               :  augmented[row][0];
                    if (curr_val > best_val) begin
                        best_val <= curr_val;
                        best_row <= row;
                    end
                end

                if (best_row != 0) begin
                    for (column = 0; column < 4; column++) begin
                        logic signed [WIDTH-1:0] temp;  // temporary swap register
                        temp                       = augmented[0][column];
                        augmented[0][column]      <= augmented[best_row][column];
                        augmented[best_row][column]<= temp;
                    end
                end
            end

            NORMALIZE_ROW_0: begin
                done            <= 1'b0;
                current_row     <= 0;
                pivot_col       <= 0;
                if (!normalize_active) begin
                    normalize_col_idx <= 0;
                    normalize_active  <= 1'b1;
                    issued_div        <= 1'b0;
                    div_start         <= 1'b1;
                end else if (!div_done) begin
                    // wait for division to finish
                end else if (div_done && !issued_div) begin
                    // one extra cycle for timing
                    issued_div <= 1'b1;
                end else if (div_done && issued_div && normalize_col_idx < 4) begin
                    augmented[0][normalize_col_idx] <= norm_result;
                    normalize_col_idx              <= normalize_col_idx + 1;
                    div_start                      <= 1'b1;
                    issued_div                     <= 1'b0;
                end else if (normalize_col_idx >= 4) begin
                    normalize_active <= 1'b0;
                    issued_div       <= 1'b0;
                end
            end

            ELIMINATE_COLUMN_0: begin
                done <= 1'b0;
                if (!elimination_active) begin
                    elim_row           <= 1;
                    elim_col           <= 0;
                    elimination_active <= 1'b1;
                end else if (elim_row <= 2 && elim_col < 4) begin
                    augmented[elim_row][elim_col] <=
                        augmented[elim_row][elim_col] - elim_mul_result;
                    elim_col <= elim_col + 1;
                end else if (elim_col == 4) begin
                    elim_row <= elim_row + 1;
                    elim_col <= 0;
                end else begin
                    elimination_active <= 1'b0;
                end
            end

            PIVOT_ROW_1: begin
                done      <= 1'b0;
                best_row  <= 1;
                best_val  <= (augmented[1][1] < 0)
                             ? -augmented[1][1]
                             :  augmented[1][1];
                curr_val  <= (augmented[2][1] < 0)
                             ? -augmented[2][1]
                             :  augmented[2][1];
                if (curr_val > best_val) begin
                    best_val <= curr_val;
                    best_row <= 2;
                end

                if (best_row != 1) begin
                    for (column = 1; column < 4; column++) begin
                        logic signed [WIDTH-1:0] temp;
                        temp                        = augmented[1][column];
                        augmented[1][column]       <= augmented[best_row][column];
                        augmented[best_row][column]<= temp;
                    end
                end
            end

            NORMALIZE_ROW_1: begin
                done            <= 1'b0;
                current_row     <= 1;
                pivot_col       <= 1;
                if (!normalize_active) begin
                    normalize_col_idx <= 1;
                    normalize_active  <= 1'b1;
                    issued_div        <= 1'b0;
                    div_start         <= 1'b1;
                end else if (!div_done) begin
                    // wait for division
                end else if (div_done && !issued_div) begin
                    issued_div <= 1'b1;
                end else if (div_done && issued_div) begin
                    augmented[1][normalize_col_idx] <= norm_result;
                    if (normalize_col_idx == 3) begin
                        normalize_active <= 1'b0;
                    end else begin
                        normalize_col_idx <= normalize_col_idx + 1;
                        div_start         <= 1'b1;
                        issued_div        <= 1'b0;
                    end
                end
            end

            ELIMINATE_COLUMN_1: begin
                done            <= 1'b0;
                if (!elimination_active) begin
                    elim_col           <= 1;
                    elimination_active <= 1'b1;
                end else if (elim_col < 4) begin
                    augmented[2][elim_col] <=
                        augmented[2][elim_col] - elim2_product;
                    elim_col <= elim_col + 1;
                end else begin
                    elimination_active <= 1'b0;
                end
            end

            BACK_SUB: begin
                done <= 1'b0;
                case (backsub_stage)
                    0: begin
                        beta[2]        <= augmented[2][3];
                        backsub_stage  <= 1;
                        mul_done       <= 1'b0;
                        mul_counter    <= 0;
                    end

                    1: if (!mul_done && mul_counter == 0) begin
                        bs_mul_a  <= augmented[1][2];
                        bs_mul_b  <= beta[2];
                        mul_start <= 1'b1;
                    end else if (mul_done) begin
                        acc      <= augmented[1][3] - bs_mul_result;
                        beta[1]  <= acc;
                        backsub_stage <= 2;
                        mul_counter <= 0;
                    end

                    2: if (!mul_done && mul_counter == 0) begin
                        bs_mul_a  <= augmented[0][1];
                        bs_mul_b  <= beta[1];
                        mul_start <= 1'b1;
                    end else if (mul_done) begin
                        acc      <= augmented[0][3] - bs_mul_result;
                        beta[0]  <= acc;
                        backsub_stage <= 3;
                        mul_counter <= 0;
                    end

                    default: backsub_stage <= 0;
                endcase
            end

            DONE: done <= 1'b1;
        endcase
    end

    
    // Simulation-only display
    
    always @(posedge clk) begin
        if (done) begin
            $display("Regression Done.");
            $display("beta[0] = %0d", beta[0]);
            $display("beta[1] = %0d", beta[1]);
            $display("beta[2] = %0d", beta[2]);
        end
    end

    always_ff @(posedge clk) begin
        $display("FSM state: %0d", state);
    end

endmodule
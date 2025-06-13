module solveRegression3x3 #(
    parameter WIDTH = 32,
    parameter MUL_LATENCY = 2,
    parameter DIV_LATENCY = 3
)(
    // sequential inputs should be logic
    input  logic                       clk,
    input  logic                       rst,
    input  logic                       start,

    // flattened arrays as logic
    input  logic signed [WIDTH-1:0]    A_flat [0:8],
    input  logic signed [WIDTH-1:0]    B_flat [0:2],

    // outputs driven in always_ff → logic
    output logic                       done,                             
    output logic signed [WIDTH-1:0]    beta [0:2]      
);

    // FSM states
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

    // state registers
    logic [3:0] state, next_state;

    // augmented matrix
    logic signed [WIDTH-1:0] augmented [0:2][0:3];

    // normalization controls
    logic [1:0] norm_col;
    logic       normalize_active;

    // result of divider is driven by the divider instance → keep as wire
    wire signed [WIDTH-1:0] norm_result; // wire: output of fxDiv

    // divider handshake
    logic signed [WIDTH-1:0] numerator, denominator;
    logic [1:0]              current_row, pivot_col;
    logic                    div_start;
    logic [1:0]              div_counter;
    logic                    div_done;

    always_comb begin
        numerator   = augmented[current_row][norm_col];
        denominator = augmented[current_row][pivot_col];
    end

    fxDiv #(WIDTH, 31) div0 (
        .numerator  (numerator),
        .denominator(denominator),
        .result     (norm_result)
    );

    // multiplication handshake for first elimination
    logic [1:0]              mul_counter;
    logic                    mul_start;
    logic                    mul_done;
    logic [1:0]              elim_row, elim_col;
    logic                    elimination_active;

    // fxMul output → net driven by instance → wire
    wire signed [WIDTH-1:0] elim_mul_result; // wire: output of fxMul

    fxMul #(WIDTH) mul0 (
        .a      (augmented[elim_row][0]),
        .b      (augmented[0][elim_col]),
        .result (elim_mul_result)
    );

    // elimination row 2 factor
    // continuous assignment from augmented → wire
    wire signed [WIDTH-1:0] elim2_factor  = augmented[2][1];            // wire: tied to array element
    wire signed [WIDTH-1:0] elim2_product;                              // wire: fxMul output

    fxMul #(WIDTH) mul_col1 (
        .a      (elim2_factor),
        .b      (augmented[1][elim_col]),
        .result (elim2_product)
    );

    // back-substitution signals
    logic signed [WIDTH-1:0] bs_mul_a, bs_mul_b;
    // fxMul output → wire
    wire signed [WIDTH-1:0] bs_mul_result; // wire: output of fxMul

    logic signed [WIDTH-1:0] acc;
    logic [1:0]              bs_step;

    fxMul #(WIDTH) bs_mul (
        .a      (bs_mul_a),
        .b      (bs_mul_b),
        .result (bs_mul_result)
    );

    // state transition combinational
    always_comb begin
        case (state)
            IDLE:               next_state = start ? LOAD : IDLE;
            LOAD:               next_state = PIVOT_ROW_0;
            PIVOT_ROW_0:        next_state = NORMALIZE_ROW_0;
            NORMALIZE_ROW_0:    next_state = (normalize_active && norm_col < 4) ? NORMALIZE_ROW_0 : ELIMINATE_COLUMN_0;
            ELIMINATE_COLUMN_0: next_state = PIVOT_ROW_1;
            PIVOT_ROW_1:        next_state = NORMALIZE_ROW_1;
            NORMALIZE_ROW_1:    next_state = (normalize_active && norm_col < 4) ? NORMALIZE_ROW_1 : ELIMINATE_COLUMN_1;
            ELIMINATE_COLUMN_1: next_state = BACK_SUB;
            BACK_SUB:           next_state = DONE;
            DONE:               next_state = IDLE;
            default:            next_state = IDLE;
        endcase
    end

    // state register + handshake counters
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state       <= IDLE;
            div_counter <= 0; div_done <= 0; div_start <= 0;
            mul_counter <= 0; mul_done <= 0; mul_start <= 0;
        end else begin
            state <= next_state;

            // divider timing
            if (div_start) begin
                div_counter <= 1; div_done <= 0; div_start <= 0;
            end else if (div_counter > 0) begin
                div_counter <= div_counter + 1;
                div_done    <= (div_counter == DIV_LATENCY);
            end else begin
                div_done <= 0;
            end

            // multiplier timing
            if (mul_start) begin
                mul_counter <= 1; mul_done <= 0; mul_start <= 0;
            end else if (mul_counter > 0) begin
                mul_counter <= mul_counter + 1;
                mul_done    <= (mul_counter == MUL_LATENCY);
            end else begin
                mul_done <= 0;
            end
        end
    end

    // loop vars (simulation-only)
    integer i, j, row, column;
    logic [1:0]              best_row;
    logic signed [WIDTH-1:0] best_val, curr_val;
    logic                    issued_div;

    // main FSM
    always_ff @(posedge clk) begin
        case (state)
            IDLE: begin
                done              <= 0;
                norm_col          <= 0;
                normalize_active  <= 0;
                elim_row          <= 1;
                elim_col          <= 0;
                elimination_active<= 0;
                bs_step           <= 0;
                issued_div        <= 0;
            end

            LOAD: begin
                done <= 0;
                for (i = 0; i < 3; i++) begin
                    for (j = 0; j < 3; j++)
                        augmented[i][j] <= A_flat[i*3 + j];
                    augmented[i][3] <= B_flat[i];
                end
            end

            PIVOT_ROW_0: begin
                done     <= 0;
                best_row <= 0;
                best_val <= (augmented[0][0] < 0) ? -augmented[0][0] : augmented[0][0];
                for (row = 1; row < 3; row++) begin
                    curr_val = (augmented[row][0] < 0) ? -augmented[row][0] : augmented[row][0];
                    if (curr_val > best_val) begin
                        best_val  = curr_val;
                        best_row  = row;
                    end
                end
                if (best_row != 0) begin
                    for (column = 0; column < 4; column++) begin
                        logic signed [WIDTH-1:0] temp;  // reg→logic
                        temp = augmented[0][column];
                        augmented[0][column] <= augmented[best_row][column];
                        augmented[best_row][column] <= temp;
                    end
                end
            end

            NORMALIZE_ROW_0: begin
                done         <= 0;
                current_row  <= 0;
                pivot_col    <= 0;
                if (!normalize_active) begin
                    norm_col         <= 0;
                    normalize_active <= 1;
                    issued_div       <= 0;
                    div_start        <= 1;
                end else if (div_done && issued_div && norm_col < 4) begin
                    augmented[0][norm_col] <= norm_result;
                    norm_col    <= norm_col + 1;
                    div_start   <= 1;
                    issued_div  <= 0;
                end else if (div_done && !issued_div) begin
                    issued_div <= 1;
                end else if (norm_col >= 4) begin
                    normalize_active <= 0;
                    issued_div       <= 0;
                end
            end

            ELIMINATE_COLUMN_0: begin
                done <= 0;
                if (!elimination_active) begin
                    elim_row          <= 1;
                    elim_col          <= 0;
                    elimination_active<= 1;
                end else if (elim_row <= 2 && elim_col < 4) begin
                    augmented[elim_row][elim_col] <= augmented[elim_row][elim_col] - elim_mul_result;
                    elim_col <= elim_col + 1;
                end else if (elim_row <= 2 && elim_col == 4) begin
                    elim_row <= elim_row + 1;
                    elim_col <= 0;
                end else begin
                    elimination_active <= 0;
                end
            end

            PIVOT_ROW_1: begin
                done     <= 0;
                best_row <= 1;
                best_val <= (augmented[1][1] < 0) ? -augmented[1][1] : augmented[1][1];
                curr_val = (augmented[2][1] < 0) ? -augmented[2][1] : augmented[2][1];
                if (curr_val > best_val) begin
                    best_val = curr_val;
                    best_row = 2;
                end
                if (best_row != 1) begin
                    for (column = 1; column < 4; column++) begin
                        logic signed [WIDTH-1:0] temp;  // reg→logic
                        temp = augmented[1][column];
                        augmented[1][column] <= augmented[best_row][column];
                        augmented[best_row][column] <= temp;
                    end
                end
            end

            NORMALIZE_ROW_1: begin
                done         <= 0;
                current_row  <= 1;
                pivot_col    <= 1;
                if (!normalize_active) begin
                    norm_col         <= 1;
                    normalize_active <= 1;
                    issued_div       <= 0;
                    div_start        <= 1;
                end else if (div_done && issued_div) begin
                    augmented[1][norm_col] <= norm_result;
                    if (norm_col == 3) begin
                        normalize_active <= 0;
                        issued_div       <= 0;
                    end else begin
                        norm_col   <= norm_col + 1;
                        div_start  <= 1;
                        issued_div <= 0;
                    end
                end else if (div_done && !issued_div) begin
                    issued_div <= 1;
                end
            end

            ELIMINATE_COLUMN_1: begin
                done <= 0;
                if (!elimination_active) begin
                    elim_col          <= 1;
                    elimination_active<= 1;
                end else if (elim_col < 4) begin
                    augmented[2][elim_col] <= augmented[2][elim_col] - elim2_product;
                    elim_col <= elim_col + 1;
                end else begin
                    elimination_active <= 0;
                end
            end

            BACK_SUB: begin
                done <= 0;
                case (bs_step)
                    0: begin
                        beta[2]     <= augmented[2][3];
                        bs_step     <= 1;
                        mul_done    <= 0;
                        mul_counter <= 0;
                    end
                    1: if (!mul_done && mul_counter == 0) begin
                        bs_mul_a <= augmented[1][2];
                        bs_mul_b <= beta[2];
                        mul_start<= 1;
                    end else if (mul_done) begin
                        acc     <= augmented[1][3] - bs_mul_result;
                        beta[1] <= acc;
                        bs_step <= 2;
                        mul_counter <= 0;
                    end
                    2: if (!mul_done && mul_counter == 0) begin
                        bs_mul_a <= augmented[0][1];
                        bs_mul_b <= beta[1];
                        mul_start<= 1;
                    end else if (mul_done) begin
                        acc     <= augmented[0][3] - bs_mul_result;
                        beta[0] <= acc;
                        bs_step <= 3;
                        mul_counter <= 0;
                    end
                    default: bs_step <= 0;
                endcase
            end

            DONE: done <= 1;
        endcase
    end

    // simulation-only display
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

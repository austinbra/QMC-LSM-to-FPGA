module solveRegression3x3 #(
    parameter WIDTH = 32,
    parameter MUL_LATENCY = 2,
    parameter DIV_LATENCY = 3
)(
    input wire clk,
    input wire rst,
    input wire start,

    // input matricies: 3x3 matrix A and 3x1 vector B
    // flattened so that A[3][3] maps to A_flat[0...8]
    input wire signed [WIDTH-1:0] A_flat [0:8],
    input wire signed [WIDTH-1:0] B_flat [0:2],

    output reg done,                             // signals when regression is complete
    output reg signed [WIDTH-1:0] beta [0:2]     // solution vector
);

    // define FSM states using localparam
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

    logic [3:0] state, next_state;      // current and next states

    // create augmented matrix from 
    reg signed [WIDTH-1:0] augmented [0:2][0:3];

    // wires for row 0 normalization
    reg [1:0] norm_col;
    reg normalize_active;
    wire signed [WIDTH-1:0] norm_result;

    // intermediate registers to avoid passing 2D array into fxDiv
    reg signed [WIDTH-1:0] numerator;
    reg signed [WIDTH-1:0] denominator;
    reg [1:0] current_row;
    reg [1:0] pivot_col;

    // fxDiv flags
    reg div_start;
    reg [1:0] div_counter;
    reg div_done;

    always_comb begin
        numerator = augmented[current_row][norm_col];
        denominator = augmented[current_row][pivot_col];
    end

    fxDiv #(WIDTH, 31) div0 (
        .numerator(numerator),
        .denominator(denominator),
        .result(norm_result)
    );

    // elimination0 registers
    reg [1:0] mul_counter;
    reg mul_start;
    reg mul_done;

    reg [1:0] elim_row;
    reg [1:0] elim_col;
    reg elimination_active;

    wire signed [WIDTH-1:0] elim_mul_result;

    fxMul #(WIDTH) mul0 (
        .a(augmented[elim_row][0]),
        .b(augmented[0][elim_col]),
        .result(elim_mul_result)
    );

    // elimination 1 signals

    wire signed [WIDTH-1:0] elim2_factor = augmented[2][1];
    wire signed [WIDTH-1:0] elim2_product;

    fxMul #(WIDTH) mul_col1 (
        .a(elim2_factor),
        .b(augmented[1][elim_col]),
        .result(elim2_product)
    );

    // back sub signals
    logic signed [WIDTH-1:0] bs_mul_a;
    logic signed [WIDTH-1:0] bs_mul_b;
    wire signed [WIDTH-1:0] bs_mul_result;
    reg signed [WIDTH-1:0] acc;                 // partial rhs during back sub
    reg [1:0] bs_step;                          // step tracker from beta2=0 to beta0=2

    fxMul #(WIDTH) bs_mul ( 
        .a(bs_mul_a),                       // assigned below
        .b(bs_mul_b),                       // assigned below
        .result(bs_mul_result)
    );

    // state transition logic
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

    // state register
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state <= IDLE;
            div_counter <= 0;
            div_done <= 0;
            div_start <= 0;
            mul_counter <= 0;
            mul_done <= 0;
            mul_start <= 0;
        end else begin
            state <= next_state;
            if (div_start) begin
                div_counter <= 1;
                div_done <= 0;
                div_start <= 0;
            end else if (div_counter > 0) begin
                div_counter <= div_counter + 1;
                if (div_counter == DIV_LATENCY) 
                    div_done <= 1;
            end else begin
                    div_done <= 0;
            end
            if (mul_start) begin
                mul_counter <= 1;
                mul_done <= 0;
                mul_start <= 0;
            end else if (mul_counter > 0) begin
                mul_counter <= mul_counter + 1;
                if (mul_counter == MUL_LATENCY)
                    mul_done <= 1;
            end else begin
                    mul_done <= 0;
            end
        end
    end

    // define loop counters
    integer i, j;
    integer row, column;
    reg [1:0] best_row;
    reg signed [WIDTH-1:0] best_val;
    reg signed [WIDTH-1:0] curr_val;

    // flag for division
    reg issued_div;

    // logic for each state
    always_ff @(posedge clk) begin
        case (state)
            IDLE: begin
                done <= 0;
                norm_col <= 0;
                normalize_active <= 0;
                elim_row <= 1;
                elim_col <= 0;
                elimination_active <= 0;
                bs_step <= 0;
                issued_div <= 0;
            end

            LOAD: begin
                done <= 0;
                for (i = 0; i < 3; i++) begin
                    for (j = 0; j < 3; j++) begin
                        augmented[i][j] <= A_flat[i * 3 + j];
                    end
                    augmented[i][3] <= B_flat[i];            // attach B as last column
                end
            end

            PIVOT_ROW_0: begin
                done <= 0;

                // step 1: initialize row 0 as pivot row
                best_row = 0;
                best_val = (augmented[0][0] < 0) ? -augmented[0][0] : augmented[0][0];      // get value with greatest magnitude

                // step 2: scan rows 1 and 2 for better candidate
                for (row = 1; row < 3; row++) begin
                    curr_val = (augmented[row][0] < 0) ? -augmented[row][0] : augmented[row][0];

                    // update best_row if current row has a larger absolute value
                    if (curr_val > best_val) begin
                        best_val = curr_val;
                        best_row = row;
                    end
                end

                // step 3: swap best row and row 0
                if (best_row != 0) begin
                    for (column = 0; column < 4; column++) begin
                        // swap each element
                        reg signed [WIDTH-1:0] temp;
                        temp = augmented[0][column];
                        augmented[0][column] <= augmented[best_row][column];
                        augmented[best_row][column] <= temp;
                    end
                end

            end
            
            NORMALIZE_ROW_0: begin
                done <= 0;
                current_row <= 0;
                pivot_col <= 0;

                if (!normalize_active) begin
                    norm_col <= 0;
                    normalize_active <= 1;
                    issued_div <= 0;
                    div_start <= 1;
                end else if (!div_done) begin
                    // wait for division to complete
                end else if (div_done && !issued_div) begin
                    // wait 1 cycle before triggering next div
                    issued_div <= 1;
                end else if (div_done && issued_div && norm_col < 4) begin
                    augmented[0][norm_col] <= norm_result;
                    norm_col <= norm_col + 1;
                    div_start <= 1;
                    issued_div <= 0;  // allow next division to issue
                end else if (norm_col >= 4) begin
                    normalize_active <= 0;
                    issued_div <= 0;
                end
            end

            ELIMINATE_COLUMN_0: begin
                done <= 0;

                // set elimination_active high if first entry
                if (!elimination_active) begin
                    elim_row <= 1;
                    elim_col <= 0;
                    elimination_active <= 1;
                end

                else if (elim_row <= 2 && elim_col < 4) begin
                    augmented[elim_row][elim_col] <= augmented[elim_row][elim_col] - elim_mul_result;
                    elim_col <= elim_col + 1;
                end

                else if (elim_row <= 2 && elim_col == 4) begin
                    // go to next row if end col reached
                    elim_row <= elim_row + 1;
                    elim_col <= 0;
                end

                else begin
                    elimination_active <= 0;        // finished elimination
                end
            end

            PIVOT_ROW_1: begin
                done <= 0;

                // assume row 1 is best to start
                best_row = 1;

                // best val is the one with greatest magnitude
                best_val = (augmented[1][1] < 0) ? -augmented[1][1] : augmented[1][1];

                // compare to row 2
                curr_val = (augmented[2][1] < 0) ? -augmented[2][1] : augmented[2][1];
                if (curr_val > best_val) begin
                    best_val = curr_val;
                    best_row = 2;
                end

                // swap best row if needed
                if (best_row != 1) begin
                    for (column = 1; column < 4; column++) begin
                        // loop to swap element in each column
                        reg signed [WIDTH-1:0] temp;
                        temp = augmented[1][column];
                        augmented[1][column] <= augmented[2][column];
                        augmented[2][column] <= temp;
                    end
                end
            end

            NORMALIZE_ROW_1: begin
                done <= 0;
                current_row <= 1;
                pivot_col <= 1;
            
                if (!normalize_active) begin
                    norm_col <= 1;
                    normalize_active <= 1;
                    issued_div <= 0;
                    div_start <= 1;
                end 
                else if (!div_done) begin
                    // Wait for division to complete
                end 
                else if (div_done && !issued_div) begin
                    issued_div <= 1;
                end 
                else if (div_done && issued_div) begin
                    augmented[1][norm_col] <= norm_result;
                    if (norm_col == 3) begin
                        normalize_active <= 0;
                        issued_div <= 0;
                    end else begin
                        norm_col <= norm_col + 1;
                        div_start <= 1;
                        issued_div <= 0;
                    end
                end
            end

            ELIMINATE_COLUMN_1: begin
                done <= 0;
                
                if (!elimination_active) begin
                    elim_col <= 1;
                    elimination_active <= 1;
                end
                else if (elim_col < 4) begin
                    augmented[2][elim_col] <= augmented[2][elim_col] - elim2_product;
                    elim_col <= elim_col + 1;
                end
                else begin
                    elimination_active <= 0;
                end
            end

            BACK_SUB: begin
                done <= 0;

                case (bs_step) 
                    0: begin
                        beta[2] <= augmented[2][3];
                        bs_step <= 1;
                        mul_done <= 0;
                        mul_counter <= 0;
                    end

                    1: begin
                        if (!mul_done && mul_counter == 0) begin
                            bs_mul_a <= augmented[1][2];
                            bs_mul_b <= beta[2];
                            mul_start <= 1;
                        end else if (mul_done) begin
                            acc <= augmented[1][3] - bs_mul_result;
                            beta[1] <= acc;
                            bs_step <= 2;
                            mul_counter <= 0;
                        end
                    end

                    2: begin
                        if (!mul_done && mul_counter == 0) begin
                            bs_mul_a <= augmented[0][1];
                            bs_mul_b <= beta[1];
                            mul_start <= 1;
                        end else if (mul_done) begin
                            acc <= augmented[0][3] - bs_mul_result;
                            beta[0] <= acc;
                            bs_step <= 3;
                            mul_counter <= 0;
                        end
                    end

                    default: begin
                        bs_step <= 0;
                    end
                endcase
            end


            DONE: begin
                done <= 1;
            end
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
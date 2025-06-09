module solveRegression3x3 #(
    parameter WIDTH = 32        // for 32 bit fixed point
)(
    input wire clk,
    input wire rst,
    input wire start,

    // input matricies: 3x3 matrix A and 3x1 vector B
    // flattened so that A[3][3] maps to A_flat[0...8]
    input wire signed [WIDTH-1:0] A_flat [0:8],
    input wire signed [WIDTH-1:0] B_flat [3],

    output reg done,                             // signals when regression is complete
    output reg signed [WIDTH-1:0] beta [0:2]     // solution vector
);

    // define FSM states
    typedef enum logic [2:0] {
        IDLE,
        LOAD,
        PIVOT_ROW_0,
        NORMALIZE_ROW_0,
        ELIMINATE_COLUMN_0,
        DONE
    } state_t;
    state_t state, next_state;      // current and next states

    // create augmented matrix from 
    reg signed [WIDTH-1:0] augmented [0:2][0:3];

    // wires for row 0 normalization
    reg [1:0] norm_col;
    reg normalize_active;
    wire signed [WIDTH-1:0] norm_result;

    // intermediate registers to avoid passing 2D array into fxDiv
    reg signed [WIDTH-1:0] numerator;
    reg signed [WIDTH-1:0] demoninator;
    numerator <= augmented[0][norm_col];
    denominator <= augmented[0][0];

    fxDiv #(WIDTH, 31) div0 (
        .numerator(numerator),
        .denominator(denominator),
        .result(norm_result)
    );

    // elimination registers
    reg [1:0] elim_row;
    reg [1:0] elim_col;
    reg elimination_active;

    wire signed [WIDTH-1:0] elim_mul_result;

    fxMul #(WIDTH) mul0 (
        .a(augmented[elim_row][0]),
        .b(augmented[0][elim_col]),
        .result(elim_mul_result)
    );

    // state transition logic
    always_comb begin
        case (state)
            IDLE:               next_state = start ? LOAD : IDLE;
            LOAD:               next_state = PIVOT_ROW_0;
            PIVOT_ROW_0:        next_state = NORMALIZE_ROW_0;
            NORMALIZE_ROW_0:    next_state = (normalize_active && norm_col < 4) ? NORMALIZE_ROW_0 : ELIMINATE_COLUMN_0;
            ELIMINATE_COLUMN_0: next_state = DONE;
            DONE:               next_state = IDLE;
            default:            next_state = IDLE;
        endcase
    end

    // state register
    always_ff @(posedge clk or posedge rst) begin
        if (rst) 
            state <= IDLE;
        else
            state <= next_state;
    end

    // define loop counters
    integer i, j;

    // logic for each state
    always_ff @(posedge clk) begin
        case (state)
            IDLE: begin
                done <= 0;
                norm_col <= 0;
                normalize_active <= 0;
            end

            LOAD: begin
                for (i = 0; i < 3; i++) begin
                    for (j = 0; j < 3; j++) begin
                        augmented[i][j] <= A_flat[i * 3 + j];
                    end
                    augmented[i][3] <= B_flat[i];            // attach B as last column
                end
            end

            PIVOT_ROW_0: begin
                
                // define loop counters
                integer row, column;

                reg [1:0] best_row;                         // keeps track of best row found
                reg signed [WIDTH-1:0] best_val;            // keeps track of best value found
                reg signed [WIDTH-1:0] curr_val;            // holds current value to be compared

                // step 1: initialize row 0 as pivot row
                best_row = 0;
                best_val = (augmented[0][0] < 0) ? -augmented[0][0] : augmented[0][0];      // get value with greatest magnitude

                // step 2: scan rows 1 and 2 for better candidate
                for (row = 1; row < 3; row++) begin
                    curr_val = (augmented[row][0] < 0) ? -augmented[row][0] : augmented[row][0];

                    // update best_row if current row has a larger absolute value
                    if (curr_val > best_val) begin
                        best_val = cur_val;
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

                // set normalization_active high to start
                if (!normalization_active) begin
                    norm_col = 0;
                    normalization_active <= 1;
                end
                else if (norm_col < 4) begin
                    augmented[0][norm_col] <= norm_result;
                    norm_col <= norm_col + 1;
                end
                else begin
                    normalize_active <= 0; 
                end
            end

            ELIMINATE_COLUMN_0: 
                done <= 0;

                // set elimination_active high if first entry
                if (!elimination_active) begin
                    elim_row <= 1;
                    elim_col <= 0;
                    elimination_active <= 1;
                end

                else if (elim_row <= 3 && elim_col < 4) begin
                    augmented[elim_row][elim_col] <= augmented[elim_row][elim_col]

            DONE: begin
                done <= 1;
            end
        endcase
    end
endmodule

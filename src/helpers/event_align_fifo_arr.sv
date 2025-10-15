timeunit 1ns; timeprecision 1ps;
// Small ring FIFO to align an array payload between “launch” and later
// “result-valid” events. Robust for any DEPTH >= 1 (wrap-around safe).
module event_align_fifo_arr #(
    parameter int N      = 1,  // number of array elements
    parameter int DW     = 32, // element width
    parameter int DEPTH  = 4   // queue depth (>=1)
)(
    input  logic                 clk,
    input  logic                 rst_n,

    // push on launch event
    input  logic                 push_en,
    input  logic [DW-1:0]        push_data [0:N-1],

    // pop on corresponding result-valid event
    input  logic                 pop_en,
    output logic [DW-1:0]        pop_data [0:N-1],

    output logic                 full,
    output logic                 empty
);
    localparam int AW = (DEPTH <= 1) ? 1 : $clog2(DEPTH);

    // Storage
    logic [DW-1:0] mem [0:DEPTH-1][0:N-1];

    // Pointers and count
    logic [AW-1:0] wptr;
    logic [AW-1:0] rptr;
    logic [AW:0]   count;

    // Next-pointer wrap-around helpers
    function automatic logic [AW-1:0] inc_ptr(input logic [AW-1:0] p);
        if (p == DEPTH-1) return '0;
        else              return p + 1'b1;
    endfunction

    // Flags
    assign full  = (count == DEPTH[AW:0]);
    assign empty = (count == '0);

    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wptr  <= '0;
            rptr  <= '0;
            count <= '0;
            for (i = 0; i < N; ++i) pop_data[i] <= '0;
        end else begin
            unique case ({push_en, pop_en})
                2'b10: begin
                    for (i = 0; i < N; ++i) mem[wptr][i] <= push_data[i];
                    wptr  <= inc_ptr(wptr);
                    count <= count + 1'b1;
                end
                2'b01: begin
                    for (i = 0; i < N; ++i) pop_data[i] <= mem[rptr][i];
                    rptr  <= inc_ptr(rptr);
                    count <= count - 1'b1;
                end
                2'b11: begin
                    // concurrent push & pop: present current rptr, write next at wptr
                    for (i = 0; i < N; ++i) begin
                        pop_data[i]  <= mem[rptr][i];
                        mem[wptr][i] <= push_data[i];
                    end
                    rptr <= inc_ptr(rptr);
                    wptr <= inc_ptr(wptr);
                    // count unchanged
                end
                default: ;
            endcase
        end
    end

endmodule
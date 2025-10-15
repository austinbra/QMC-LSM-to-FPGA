timeunit 1ns; timeprecision 1ps;
module fxExpLUT #(
    parameter int WIDTH    = fpga_cfg_pkg::FP_WIDTH,
    parameter int QINT     = fpga_cfg_pkg::FP_QINT,   // kept for symmetry
    parameter int QFRAC    = fpga_cfg_pkg::FP_QFRAC,
    parameter int LUT_BITS = 12                       // 2^LUT_BITS entries
)(
    input  logic                      clk,
    input  logic                      rst_n,

    // upstream handshake
    input  logic                      valid_in,
    output logic                      ready_out,

    // downstream handshake
    output logic                      valid_out,
    input  logic                      ready_in,

    // NOTE: This block expects a ≥ 0 (non-negative). For negative inputs,
    //       pass |a| here and handle reciprocal outside (e.g., via fxDiv).
    input  logic signed [WIDTH-1:0]   a,      // Qm.n fixed-point
    output logic signed [WIDTH-1:0]   result  // Qm.n fixed-point
);
    // Domain: exp(x) for x ∈ [0, 8). Clamp outside range.
    localparam signed [WIDTH-1:0] A_MIN = '0;                    // 0.0
    localparam signed [WIDTH-1:0] A_MAX = (8 <<< QFRAC) - 1;     // 8.0 - ε

    // Index mapping: idx = floor(a * 2^LUT_BITS / 8)
    // With a in QFRAC, that is idx = a >> (QFRAC + 3 - LUT_BITS)
    localparam int SHIFT = (QFRAC + 3) - LUT_BITS;

    // Synthesis-time guard
    initial begin
        if (SHIFT < 0) begin
            $fatal(1, "fxExpLUT: invalid SHIFT; QFRAC+3=%0d, LUT_BITS=%0d, SHIFT=%0d", QFRAC+3, LUT_BITS, SHIFT);
        end
    end

    // -------------------------------------------------------------------------
    // One-deep elastic output (stall-safe) with a one-cycle BRAM read
    // Control:
    //  - When (valid_in && ready_out), clamp 'a', form LUT index, latch addr_reg,
    //    and arm addr_pending.
    //  - Next cycle, read lut[addr_reg] into result_reg, assert v_reg.
    //  - Hold result_reg while valid_out && !ready_in.
    //  - Accept new input only if no pending ROM read and output can drain.
    // -------------------------------------------------------------------------
    logic                    addr_pending;          // awaiting ROM read
    logic [LUT_BITS-1:0]     addr_reg;              // registered LUT address
    logic                    v_reg;                 // output valid register
    logic signed [WIDTH-1:0] result_reg;            // registered output
    logic signed [WIDTH-1:0] a_clamped;            // clamped input

    assign valid_out = v_reg;
    assign result    = result_reg;

    // Ready when: no pending ROM read, and output is available (or draining)
    assign ready_out = (!addr_pending) && (!v_reg || ready_in);

    // -------------------------------------------------------------------------
    // LUT ROM: exp(x) for x ∈ [0, 8)
    // Each entry is a WIDTH-bit Q-format value of exp(x_i)
    // -------------------------------------------------------------------------
    (* rom_style = "block" *)
    logic [WIDTH-1:0] lut [0:(1<<LUT_BITS)-1];

    string lut_fname;
    initial begin
        lut_fname = $sformatf("exp_lut_%0d.mem", (1 << LUT_BITS));
        if (!$readmemh(lut_fname, lut)) begin
            $fatal(1, "fxExpLUT: failed to read %s", lut_fname);
        end
    end

    // -------------------------------------------------------------------------
    // Sequential control and datapath
    // -------------------------------------------------------------------------
    logic [WIDTH-1:0]       a_u;        // unsigned view of clamped input
    logic [WIDTH-1:0]       a_shifted;  // shifted for address formation
    logic [LUT_BITS-1:0]    idx_next;   // next index (combinational register)

    // Precompute index components (kept sequential for Vivado friendliness)
    // Note: These registers are written only when we accept a new input.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            addr_pending <= 1'b0;
            addr_reg     <= a_shifted[LUT_BITS-1:0];
            v_reg        <= 1'b0;
            result_reg   <= '0;
            a_clamped    <= '0;
            a_u          <= '0;
            a_shifted    <= '0;
            idx_next     <= '0;
        end
        else begin
            // Accept new sample?
            if (valid_in && ready_out) begin
                // Clamp input to [0, 8)
                if (a <= A_MIN)       a_clamped <= A_MIN;
                else if (a >= A_MAX)  a_clamped <= A_MAX;
                else                  a_clamped <= a;

                // Form unsigned value, compute index bits
                // idx = (unsigned)a_clamped >> SHIFT
                a_u       <= $unsigned(a);  // safe; will use clamped for addr
                a_shifted <= ($unsigned(a <= A_MIN ? A_MIN :
                                         (a >= A_MAX ? A_MAX : a)) >> SHIFT);
                idx_next  <= a_shifted[LUT_BITS-1:0];

                // Latch address; arm pending
                addr_reg     <= a_shifted[LUT_BITS-1:0];
                addr_pending <= 1'b1;
            end
            // Complete the pending read (one cycle after accepting)
            else if (addr_pending) begin
                result_reg   <= lut[addr_reg];
                v_reg        <= 1'b1;
                addr_pending <= 1'b0;
            end
            // Downstream consumed the output
            else if (v_reg && ready_in) begin
                v_reg <= 1'b0;
            end
            // Else: hold (stall-safe)
        end
    end

    // -------------------------------------------------------------------------
    // Assertions (simulation only)
    // -------------------------------------------------------------------------
    // Output must remain stable while backpressured
    property p_stall_stable;
        @(posedge clk) disable iff (!rst_n)
            valid_out && !ready_in |=> $stable(result);
    endproperty
    assert property (p_stall_stable)
        else $error("fxExpLUT: Result changed while backpressured.");

    // Do not overwrite input while not ready
    property p_input_not_overwritten;
        @(posedge clk) disable iff (!rst_n)
            (valid_in && !ready_out) |-> $stable(a);
    endproperty
    assert property (p_input_not_overwritten)
        else $error("fxExpLUT: Input overwritten while !ready_out.");

endmodule
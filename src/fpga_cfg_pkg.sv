package fpga_cfg_pkg;
    timeunit 1ns;
    timeprecision 1ps;

    parameter int FP_WIDTH              = 32;
    parameter int FP_QINT               = 16;
    parameter int FP_QFRAC              = FP_WIDTH - FP_QINT;
    parameter int FP_MUL_LATENCY        = 1;
    parameter int FP_DIV_LATENCY        = 16; // 16 is safe for fMAX roughly 200 MHz on spartan 7
    parameter int FP_SQRT_LATENCY       = 9; // *** do not change ***

    // Common fixed-point constants (synthesis-safe, derived from FP_QFRAC).
    // Use 32'sd1 (not 1'sd1) to prevent sign-extension bugs.
    localparam signed [FP_WIDTH-1:0] FP_ONE     = 32'sd1 <<< FP_QFRAC;
    localparam signed [FP_WIDTH-1:0] FP_HALF    = 32'sd1 <<< (FP_QFRAC - 1);
    localparam signed [FP_WIDTH-1:0] FP_NEG_ONE = -FP_ONE;
    localparam signed [FP_WIDTH-1:0] FP_NEG_TWO = -(32'sd2 <<< FP_QFRAC);

    // synthesis translate_off
    function automatic signed [FP_WIDTH-1:0] fp_from_real(input real val);
        return signed'($rtoi(val * $itor(1 << FP_QFRAC)));
    endfunction
    // synthesis translate_on

endpackage

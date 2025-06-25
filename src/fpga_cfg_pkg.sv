package fpga_cfg_pkg;
    parameter int FP_WIDTH              = 32;
    parameter int FP_QINT               = 16;
    parameter int FP_QFRAC              = FP_WIDTH - FP_QINT;
    parameter int FP_MUL_LATENCY        = 2;
    parameter int FP_MUL_ALWAYS_LATENCY = 1;
    parameter int FP_DIV_LATENCY        = 3;
    parameter int FP_SQRT_LATENCY       = 4;
    parameter int FP_LUT_BITS           = 10;
endpackage

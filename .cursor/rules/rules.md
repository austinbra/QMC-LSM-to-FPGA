---
description: Permanent project identity, architecture, design rules, and file map for QMC-LSM-to-FPGA.
globs: ["**/*.sv", "**/*.py", "**/*.ps1", "**/*.tcl", "**/*.md"]
alwaysApply: true
---

# QMC-LSM-to-FPGA: Project Rules

## Identity

Production-grade, fully pipelined FPGA engine for American option pricing
using Longstaff-Schwartz Monte Carlo (LSMC) with Quasi-Monte Carlo (Sobol)
sequences. Target: Xilinx Spartan-7 (XC7S50), Vivado flow, SystemVerilog.

## Pipeline Architecture

Streaming datapath with ready/valid handshaking and skid buffers at every
stage boundary. Two-pass LSMC: training (accumulate sufficient stats) then
decision (exercise vs continue). O(1) memory via online accumulation.

```
Sobol → InverseCDF → GBM → Accumulator → Regression → LSM Decision → UART
         (~15 cyc)   (~5 cyc)
```

Pass 1 (Training): sobol → invCDF → GBM → accumulator (8 running 64-bit sums)
Pass 2 (Decision): sobol → invCDF → GBM → lsm_decision (compare & accumulate PV)

Sobol is deterministic — same (idx, dim) produces same output. Paths regenerated
exactly in pass 2. 2x compute, but O(1) BRAM instead of O(N*M).

Antithetic variates: even path_idx = normal z, odd = -z (same Sobol index).
Doubles effective N with near-zero overhead.

## Fixed-Point Format: Q16.16

- 32-bit signed: 16 integer bits, 16 fractional bits
- Range: [-32768.0, +32767.9999]
- Precision: 1/65536 ~ 0.0000153
- All constants from fpga_cfg_pkg.sv: FP_ONE, FP_HALF, FP_NEG_ONE, FP_NEG_TWO
- Changing format: update fpga_cfg_pkg only

## File Map

```
src/
  fpga_cfg_pkg.sv                     Global Q16.16 params + FP constants
  helpers/rv_skid_arr_gate.sv         Skid buffer (array, gated accept)
  helpers/event_align_fifo_arr.sv     Event-aligned ring FIFO (combinational read)
  math/fxMul.sv                       Fixed-point multiplier (DSP-mapped)
  math/fxDiv.sv                       Fixed-point divider (div_gen wrapper)
  math/fxExpLUT.sv                    Exponential LUT (BRAM, signed mode)
  math/fxLnLUT.sv                     Natural log (3-stage pipeline + interpolation)
  math/fxSqrt.sv                      Square root (non-restoring, 25 cycles)
  math/fxInvCDF_ZS.sv                 Zelen-Severo rational approximation
  steps/sobol.sv                      Sobol QMC generator (Gray-coded XOR)
  steps/inverseCDF_fold.sv            Fold U(0,1) to (0,0.5] + negate flag
  steps/inverseCDF.sv                 Full inverse CDF pipeline
  steps/GBM.sv                        GBM step (streaming: MUL→EXP→MUL)
  steps/accumulator.sv                Quadratic LSM accumulator (64-bit sums)
  steps/regression.sv                 3x4 Gaussian elimination solver
  steps/lsm_decision.sv               Exercise/continue decision
  io/uart/*.sv                        UART rx/tx (8-bit and 32-bit)
  io/handlers/uart_input_handler.sv   Batch handler + 5-word result packet
  top/top_option_pricer.sv            Top-level two-pass LSMC FSM
  sim/fxDiv_core_stub.sv              Simulation stub for div_gen IP
  gen/*.mem                           LUT memory files (exp, ln, sqrt, sobol)
  uart_host.py                        Host-side Python (benchmark/live/sweep)

tb/                                   Testbenches (unit + integration + top UART)
scripts/                              Build scripts (PS1, TCL, Python validation)
baseline/cpp_fixed/                   C++ fixed-point baseline (Q16.16)
```

## Design Principles (MANDATORY)

1. STREAMING PIPELINE: Fire next sample as soon as pipeline accepts. Never
   wait for end-to-end completion. Skid buffers decouple all stages.

2. READY/VALID HANDSHAKE: Every stage. valid_out holds stable when !ready_in.
   Assertions enforce stall stability. No glitches or races.

3. EVENT-ALIGNMENT FIFOs: Side-channel data (negate flags, S values) synced
   with main-path data across variable-latency stages.

4. PARAMETERIZATION: No magic numbers. Widths, QINT, QFRAC, latencies, LUT
   sizes from fpga_cfg_pkg. Use fpga_cfg_pkg::FP_ONE (not 1<<<QFRAC).

5. DECLARATIONS FIRST: Never declare a variable after it is used. All
   declarations at top of block before procedural statements.

6. RESET: posedge clk or negedge rst_n with '0 initialization. No latches.

7. SATURATION: Always clamp fixed-point math where overflow could occur.
   Moneyness normalization (S/K) for regression inputs.

8. CORRECTNESS FIRST: Everything must compile, synthesize, and be stall-correct.

## SystemVerilog Shift Operators

- `>>>` : Arithmetic right shift (sign-extends). USE THIS for signed shifts.
- `<<<` : Arithmetic left shift (preserves signedness). USE THIS for Q16.16.
- `>>` / `<<` : Logical shifts. Only for unsigned operands.
- Always `$signed(...)` where sign matters. Never rely on implicit casting.

## Workflow Rules

- Do not run all compiles at the same time. Break up and run individually.
- Compile check: `./scripts/run_xvlog_src.ps1`
- Elaborate check: `./scripts/run_xelab_smoke.ps1`
- Full TB run: `./scripts/run_tb_top_uart_safe.ps1 [-ComputeMode|-Multibatch]`
- Numerical validation: `python scripts/validate_numerical.py`

## Resource Budget (Spartan-7 XC7S50)

- 120 DSP48E1: ~33 used (~28%)
- 75 BRAM36: ~10-12 used (~16%)
- ~32K LUTs: pipeline + control logic

## Fixed Design Decisions

1. Q16.16 fixed-point (change fpga_cfg_pkg only to switch)
2. Quadratic regression basis [1, S, S^2] (3 coefficients)
3. PUT/CALL via runtime flag (UART word 7 bit 0)
4. Single exercise date (step M-1). Full backward induction is future work.
5. Sobol MAX_STEPS=50 dimensions. Keep M <= 20 for quality.
6. Single clock domain (clk_100, target 100-170 MHz)

## Host Running Modes (src/uart_host.py)

- BENCHMARK: `--mode benchmark --target cpu|fpga|both` (price delta, speedup)
- LIVE: `--mode live` (Yahoo Finance data, logs snapshot)
- SWEEP: `--mode sweep` (convergence at increasing N)

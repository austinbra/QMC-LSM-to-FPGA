# Validation Log

This file records the main verification steps run during repository cleanup and benchmark workflow integration.

## Scope

- Source-tree reorganization (`src/io`, `src/top`, baseline promotion).
- `src/` compile and elaboration health.
- C++ fixed-point baseline build/run checks.
- Host benchmark/live runner checks.

## Toolchain Checks

### Vivado SystemVerilog compile

- Command:
  - `./run_xvlog_src.ps1`
- Result:
  - Pass
- Notes:
  - Re-run multiple times after each major RTL update (including file moves, `inverseCDF_fold` rename, UART packet updates, top-level benchmark hooks).

### Vivado elaboration smoke

- Command:
  - `./run_xelab_smoke.ps1`
- Result:
  - Pass
- Covered module snapshots:
  - `top_mc_option_pricer`
  - `uart_input_handler`
  - `sobol`
  - `inverseCDF_fold`
  - `inverseCDF`
  - `GBM`
  - `accumulator`
  - `regression`
  - `lsm_decision`
- Notes:
  - Uses simulation stub `src/sim/fxDiv_core_stub.sv` to unblock elaboration without generated `fxDiv_core` IP in sim context.

## C++ Baseline Validation

### Baseline compile and run (promoted location)

- Location:
  - `baseline/cpp_fixed/`
- Commands used:
  - `g++ -std=c++17 main.cpp pricing.cpp linalg.cpp sobol_wrapper.cpp utils.cpp -o fixed_baseline`
  - `./fixed_baseline --paths 256 --steps 12 --S0 100 --K 100 --r 0.05 --sigma 0.2 --T 1.0`
  - `./run_baseline.ps1 -InputFile params_example.txt`
- Result:
  - Pass
- Representative output observed:
  - `Estimated Option Price (double): 5.31464`
  - runtime printed successfully

### CPU sanity behavior check

- Method:
  - Compared runs with different `S0` values under same other params.
- Result:
  - Higher `S0` produced higher option value (expected monotonic call-like behavior).

## Python Host Runner Validation

### Syntax and CPU benchmark path

- Command:
  - `python -m py_compile src/uart_host.py`
- Result:
  - Pass

- Command:
  - `python src/uart_host.py --mode benchmark --target cpu --param-file baseline/cpp_fixed/params_example.txt --build-cpu`
- Result:
  - Pass
- Notes:
  - Prints parameters, CPU output, parsed CPU price/runtime.

### CPU baseline monotonic sweep (quick regression)

- Location:
  - `baseline/cpp_fixed/`
- Commands:
  - Build: `g++ -std=c++17 main.cpp pricing.cpp linalg.cpp sobol_wrapper.cpp utils.cpp -o fixed_baseline`
  - Runs (paths=2048, steps=12, r=0.05, sigma=0.2, T=1.0):
    - `S0=80, K=100`  -> `price=1.09646`
    - `S0=100, K=100` -> `price=5.46686`
    - `S0=120, K=100` -> `price=21.1872`
    - `S0=100, K=90`  -> `price=11.3954`
    - `S0=100, K=110` -> `price=3.09445`
- Result:
  - Pass
- Why this indicates correctness:
  - Call option value rises as `S0` rises (holding other params fixed).
  - Call option value falls as strike `K` rises (holding other params fixed).
  - These monotonic properties are required for financially sane pricing behavior.

## Functional Protocol Validation

### UART result packet protocol

- Implemented packet words (after parameter echo phase):
  - `0xABCD0001` marker
  - `price_raw`
  - `cycles_lo`
  - `cycles_hi`
- Host decode support:
  - `src/uart_host.py` decodes marker/price/cycles and can compute `compute_time_s` with `--fpga-fclk-hz`.

### Top UART integration testbench (`tb_top_option_pricer_uart.sv`)

- Added hardened host-side UART tasks with bounded waits:
  - `wait_for_tx_ready`
  - `wait_for_rx_byte_valid`
  - `wait_for_tx_busy`
  - `recv_byte` / `recv_word`
- Added explicit global watchdog in TB to prevent infinite simulation runs.
- Test modes:
  - `tb_top_option_pricer_uart` (timeout-expected): **Pass**
  - `tb_top_option_pricer_uart_compute` (real compute-expected): **Pass**
- Notes:
  - `tb_top_option_pricer_uart` now uses a deliberately short timeout budget in timeout mode (`CORE_MAX_CYCLES=32`) to keep timeout-path coverage deterministic.
  - `tb_top_option_pricer_uart_compute` uses a long budget and now observes non-timeout completion.
  - Top-level start logic now keys off accepted batch handshake (`batch_valid && batch_ready` edge), not raw `batch_valid` edge.

### Stability and resource-safety guards

- Added bounded/guarded runner scripts:
  - `run_xvlog_src.ps1`
  - `run_xelab_smoke.ps1`
  - `run_tb_top_uart_safe.ps1`
- Guard behavior:
  - Hard wall-clock timeout per tool invocation with forced process-tree kill on timeout.
  - `-nolog` enabled for `xvlog/xelab/xsim` in safe scripts to avoid unbounded log growth.
  - `--mt off` for `xelab` in safe scripts to reduce peak memory pressure.

### Multi-batch UART regression (diagnostic)

- Added wrapper:
  - `tb_top_option_pricer_uart_multibatch` (`NUM_BATCHES=2`)
- Current result:
  - **Fail** (diagnostic, reproducible)
- Observed behavior:
  - Batch 0 passes echo/result.
  - Batch 1 returns X in result price.
  - Assertion fires in `fxInvCDF_ZS` path: "Output valid while not ready".
- Interpretation:
  - There is still a back-to-back transaction robustness issue in the inverse-CDF handshake path under repeated sessions.
  - Single-batch timeout/compute flows remain healthy and are still passing.

## P0 Bug Fix Audit (2026-03-01)

A full-codebase correctness review identified and fixed 13 blocking bugs across the math, pipeline, and baseline modules. All fixes pass `xvlog` + `xelab` smoke.

### Math module LUT timing bugs (off-by-one pipeline races)

Three BRAM-backed LUT modules had the same systemic defect: a registered address/input and the LUT read occurred on the same clock edge, causing the LUT output to correspond to the *previous* sample.

| Module | Bug | Fix |
|--------|-----|-----|
| `fxLnLUT` | `lut_index` derived from registered `a_bound`; `result_reg` captures stale lookup | Rewrote as 2-stage pipeline: stage 1 registers `a_bound`, stage 2 reads `lut[lut_index]` from the registered value |
| `fxExpLUT` | `addr_reg` captures stale `a_shifted` | Same 2-stage pipeline: clamp+register in stage 1, LUT read in stage 2 |
| `fxSqrt` | LUT index from stale `a_norm_reg`; final `v4_result` from stale `tmp` | LUT index now computed from combinational `a_norm`; output is combinational from `mul4_result` (stable under stall by fxMul guarantee) |

### GBM pipeline bugs

| Bug | Fix |
|-----|-----|
| Diffusion branch fires on `buf_valid` alone (double-fire under stall) | Gated: `diff_v_in = buf_valid && shift_en` |
| `sign_bit` derived combinationally from `exp_arg` but used after ExpLUT+Div latency | Added `exp_launch` one-cycle-delayed pulse; `exp_arg` is now registered before ExpLUT fires, so `sign_bit` is stable throughout |
| `exp_arg` saturation `(1<<<(WIDTH-1)-1)` has wrong operator precedence; no negative clamp | Replaced with `MAX_POS`/`MIN_NEG` localparam constants with correct full-range signed saturation |

### Inverse CDF pipeline bugs

| Bug | Fix |
|-----|-----|
| `fxInvCDF_ZS`: `t_eff` and `negate_pipe` are stale at output (divider latency mismatch) | Complete rewrite: `in_flight` flag prevents double-acceptance; `t_cap` and `negate_cap` captured at input and held stable through entire computation |
| `inverseCDF`: `negate_pipe` shift register drifts under stalls | Replaced fixed shift register with `event_align_fifo_arr` FIFO: push on fold output, pop on sqrt output |
| `inverseCDF_fold`: negate polarity is inverted | Swapped: `u < 0.5 -> negate=1` (left tail), `u >= 0.5 -> negate=0` (right tail) |

### Accumulator / decision / baseline alignment bugs

| Bug | Fix |
|-----|-----|
| `accumulator`: `sum1 <= sum1 + acc_t'(1)` adds integer 1, not 1.0 in Q16.16 | Changed to `sum1 + (acc_t'(1) <<< QFRAC)` |
| `lsm_decision`: computes PUT payoff `max(K-S, 0)` while C++ computes CALL `max(S-K, 0)` | Changed to `diff = S_t - strike` and `payoff = (S_t > strike) ? diff : 0` |
| C++ baseline `types.h`: `FRAC_BITS=21` (Q11.21) while FPGA uses Q16.16 | Changed to `FRAC_BITS=16` |
| `tb_regression`, `tb_accumulator`: connect to non-existent `.solver_ready` port | Removed the port connection |

### lsm_decision interface change

- Replaced `disc` input with `cont_value` input.
- The "continue" branch now uses the actual discounted future cashflow (`cont_value`) instead of `regression_estimate * disc`.
- Why: in proper LSMC, the regression estimate is only used for the exercise *decision*; the actual cashflow must be the real discounted future value.

### Verification status after P0 fixes

- `run_xvlog_src.ps1`: **Pass** (all 22 source files)
- `run_xelab_smoke.ps1`: **Pass** (all 9 module snapshots)

## Top-Level Integration (2026-03-01)

### Architecture: two-pass QMC-LSMC pipeline

Rewrote `top_option_pricer.sv` from a single-sample stub into a complete two-pass LSMC engine with an 11-state FSM.

**Pass 1 (Training):** For each of N paths, run M sequential GBM steps via `sobol -> inverseCDF -> GBM`, feeding `(S_exercise, disc * terminal_payoff)` into the accumulator. After N paths, accumulator triggers regression and outputs `beta[0:2]`.

**Pass 2 (Decision):** Regenerate the same N paths (Sobol is deterministic from `idx_in`). For each path, `lsm_decision` compares immediate exercise payoff against the regression-estimated continuation, then selects the actual cashflow. The PV is discounted to t=0 via `disc_total` and accumulated. Final price = `sum_pv / N`.

**Exercise date:** Step M-1 (one step before maturity). Single exercise date for this version.

**Init phase:** Computes `dt = T / M`, `disc = exp(-r * dt)`, `disc_total = disc^(M-1)` using dedicated utility fxDiv/fxMul/fxExpLUT instances (time-shared, not on the critical path).

**Timeout guard:** `CORE_MAX_CYCLES` checked in every long-running FSM state. Timeout returns marker `0xDEAD0001`.

### Verification status after integration

- `run_xvlog_src.ps1`: **Pass**
- `run_xelab_smoke.ps1`: **Pass** (all 9 module snapshots including top)

## Accumulator Runtime Sample Count (2026-03-01)

- Added `n_samples_cfg` runtime input port to `accumulator.sv`.
- When non-zero, overrides the `N_SAMPLES` parameter. When zero, uses parameter default.
- Why: the top-level FSM sends `lat_N` paths (from UART params), which varies per batch. The hardcoded `N_SAMPLES=10000` parameter would cause the accumulator to wait forever for paths that never arrive.
- `top_option_pricer.sv`: wires `.n_samples_cfg(lat_N[$clog2(10001)-1:0])`.
- `tb_accumulator.sv`: wires `.n_samples_cfg('0)` (uses parameter default).

### Verification status

- `run_xvlog_src.ps1`: **Pass** (all sources + both TBs)
- `run_xelab_smoke.ps1`: **Pass** (all 9 module snapshots including top, accumulator)

## Top UART Testbench Update (2026-03-01)

- Removed stale `ENABLE_PLACEHOLDER_RESULT` parameter (no longer exists in new top).
- Updated debug probes to match new signal names (`sobol_vout`, `inv_vout`, `gbm_vout`, `lsm_vout`, `core_active`, `result_valid`, `u_inv.*`).
- Added Q16.16 price sanity check in compute mode: logs price in human-readable form and flags out-of-range values.
- `CORE_MAX_CYCLES` in compute mode set to 2M (sufficient for N=64, M=12 two-pass LSMC).

## Known Gaps / Pending Validation

- Numerical/financial quality validation of produced price against C++ baseline with matching Q16.16 parameters is not yet done.
- Multi-exercise-date expansion: current architecture checks exercise at step M-1 only; full backward induction with M-1 regression passes is future work.
- Multi-batch UART regression (`tb_top_option_pricer_uart_multibatch`) was failing before due to `fxInvCDF_ZS` handshake issues -- the rewrite of that module should resolve it but has not been re-tested yet.

## Baseline/Archive Policy Validation

- Non-fixed-point archive baseline removed from active tree and superseded by promoted baseline path:
  - Active: `baseline/cpp_fixed/`
  - Archive marker retained: `archive/buildup/Cpp_outline_32/README.md`
- Archive legacy RTL kept for reference in `archive/old` and `archive/buildup/sv_regression_handshake`.

## Re-run Quick Checklist

1. `./run_xvlog_src.ps1`
2. `./run_xelab_smoke.ps1`
3. `python -m py_compile src/uart_host.py`
4. `cd baseline/cpp_fixed`
5. `./run_baseline.ps1 -InputFile params_example.txt`
6. `python src/uart_host.py --mode benchmark --target cpu --param-file baseline/cpp_fixed/params_example.txt --build-cpu`

## Task Completion Log (rolling)

- 2026-03-01: Safe run wrappers validated (`run_xvlog_src.ps1`, `run_xelab_smoke.ps1`, `run_tb_top_uart_safe.ps1`).
  - Status: working.
  - Why: each script completed with bounded execution and no uncontrolled log growth (`-nolog`, timeout kill path available).
- 2026-03-01: top UART timeout and compute wrappers both pass.
  - Status: working.
  - Why: full 7-word param RX, echo packet, and result packet checks complete under bounded TB watchdogs.
- 2026-03-01: workspace artifact cleanup executed (`cleanup_artifacts.ps1 -IncludeSimDirs`).
  - Status: working.
  - Why: generated simulator directory/log context removed after task completion.
- 2026-03-01: top-level batch accept/start handshake tightened in `top_option_pricer`.
  - Status: working.
  - Why: `core_start` now triggers only on accepted batch handshake edge, avoiding raw `batch_valid` edge races.
- 2026-03-01: multi-batch UART diagnostic added (`tb_top_option_pricer_uart_multibatch`).
  - Status: reproduces known issue.
  - Why: reliably exposes second-batch inverse-CDF handshake/data-valid instability for focused fixing.
- 2026-03-01: single-batch timeout/compute regressions re-verified after top/inverseCDF iterations.
  - Status: working.
  - Why: both wrappers (`tb_top_option_pricer_uart`, `tb_top_option_pricer_uart_compute`) report PASS with bounded waits and clean packet checks.
- 2026-03-01: Full P0 correctness audit: 13 bugs fixed across fxLnLUT, fxExpLUT, fxSqrt, GBM, fxInvCDF_ZS, inverseCDF, inverseCDF_fold, accumulator, lsm_decision, C++ baseline, testbenches.
  - Status: all fixes compile and elaborate clean.
  - Why: systemic LUT timing races, pipeline misalignment, negate polarity inversion, Q-format mismatch, and payoff direction mismatch all caused silent numerical errors or data corruption.
- 2026-03-01: lsm_decision interface changed: `disc` input replaced with `cont_value` for proper LSMC cashflow semantics.
  - Status: compile/elab clean; tb_lsm_decision updated.
  - Why: regression estimate should only drive the exercise decision, not the actual continuation cashflow.
- 2026-03-01: top_option_pricer.sv rewritten with 11-state two-pass LSMC FSM integrating sobol -> inverseCDF -> GBM -> accumulator -> regression -> lsm_decision.
  - Status: compile/elab clean.
  - Why: previous top was a single-sample stub with hardwired beta=[0,0,0] and no accumulator/regression.
- 2026-03-01: regression.sv debug $display traces gated behind `ifdef REG_DEBUG`.
  - Status: working.
  - Why: unconditional traces flood simulation logs during integration runs.
- 2026-03-01: C++ baseline Q-format aligned to Q16.16 (`FRAC_BITS=16`).
  - Status: working.
  - Why: was Q11.21, making cross-validation against FPGA unreliable.
- 2026-03-01: .gitignore updated to cover `dfx_runtime.txt`, `xvlog.pb`, `xelab.pb`.
  - Status: working.
- 2026-03-01: accumulator.sv: added `n_samples_cfg` runtime port (overrides N_SAMPLES parameter when non-zero).
  - Status: compile/elab clean.
  - Why: top-level sends lat_N paths per batch; hardcoded N_SAMPLES=10000 would deadlock for smaller batches.
- 2026-03-01: tb_top_option_pricer_uart.sv: removed ENABLE_PLACEHOLDER_RESULT, updated debug probes, added price sanity check.
  - Status: compile clean.
  - Why: aligned to new two-pass top-level (old params/signal names no longer exist).


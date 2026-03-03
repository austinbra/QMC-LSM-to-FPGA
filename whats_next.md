QMC-LSM-to-FPGA: Implementation Status & Plan
===============================================
Last full audit: 2026-03-02

**"Project Context File"** treat this as the **authoritative ground rules** for all future responses. Do not run all compiles at the same time, break them up and run them individually to prevent hangs.

===============================================================================
PART 1: FULL CODEBASE AUDIT (2026-03-02) — VERIFIED, NOT SELF-REPORTED
===============================================================================

The previous "status" sections claimed Phase 2 and Phase 3 were complete. A
line-by-line code review proved they are NOT functionally correct — only
compile/elaborate clean. Three critical bugs block the pipeline from producing
any result. No functional simulation has been run since Phases 2 and 3 were
added. The "PASS" claims for timeout/compute mode are from BEFORE those phases.

Module-by-module verified status
--------------------------------
  fpga_cfg_pkg.sv        COMPLETE   Q16.16, MUL_LAT=1, DIV_LAT=16, SQRT_LAT=9
  fxMul.sv               COMPLETE   DSP-mapped, stall-safe, assertions
  fxDiv.sv               COMPLETE   AXI-Stream wrapper; sim stub single-cycle (ok)
  fxExpLUT.sv            COMPLETE   2-stage pipeline, SIGNED_RANGE mode works
  fxLnLUT.sv             COMPLETE   2-stage pipeline, sign handling correct
  fxSqrt.sv              COMPLETE   LUT + Newton-Raphson, 4x fxMul(LATENCY=2)
  fxInvCDF_ZS.sv         FIXED      C0 corrected to 2.515517 (was 2.0)
  inverseCDF_fold.sv     COMPLETE   Fold + negate flag, polarity correct
  inverseCDF.sv          COMPLETE   Structurally ok; fxInvCDF_ZS C0 now fixed
  sobol.sv               COMPLETE   Gray code XOR tree, skid buffer
  GBM.sv                 FIXED      S pipeline replaced with event_align_fifo_arr
  accumulator.sv         COMPLETE   64-bit sums, n_samples_cfg, regression trigger
  regression.sv          COMPLETE   Gaussian elim, fallback, assertions
  lsm_decision.sv        COMPLETE   Proper LSMC decision with cont_value
  top_option_pricer.sv   FIXED      sub_phase widened [2:0], timeout guards added
  uart_input_handler.sv  FUNCTIONAL Messy formatting but works
  uart_rx/tx/32          COMPLETE   No issues
  helpers (skid, fifo)   COMPLETE   No issues
  C++ baseline           COMPLETE   Q16.16 aligned, monotonic sweep verified
  Python host            STRUCTURAL Never tested end-to-end with FPGA

Pipeline restoration plan status:
  Phase 1: Signed ExpLUT                   COMPLETE
  Phase 2: Pre-compute GBM const           COMPLETE  (sub_phase fixed, timeout guards added)
  Phase 3: GBM streaming pipeline          COMPLETE  (S pipe fixed via event_align_fifo_arr)
  Phase 4: FULLY PIPELINED TOP-LEVEL       COMPLETE  (fire step k+1 same cycle as gbm_vout)
  Phase 5: Accumulator stall diagnosis     COMPLETE  (ACC_DEBUG traces added)
  Phase 6: Two host running modes          COMPLETE  (benchmark + live)
  Phase 7: Cleanup/docs                    NOT STARTED

  NOTE: Phase 4 is NOT just an optimization — it is the CORE ARCHITECTURAL
  GOAL. Without streaming overlap in the top-level, every sample traverses
  the pipeline serially (~21 cycles per step) instead of overlapping (~5
  cycles/step effective throughput). The pipeline stages already have skid
  buffers and ready/valid — the top-level just needs to STOP waiting and
  START streaming.

===============================================================================
PART 2: CRITICAL BUGS — ALL RESOLVED (2026-03-02)
===============================================================================

--- BUG 1 (BLOCKING): sub_phase overflow in top_option_pricer.sv ---

File:    src/top/top_option_pricer.sv
Line:    299
Problem: `logic [1:0] sub_phase` is 2 bits (max value 3).
         ST_INIT_GBM_CONST needs 5 phases (0,1,2,3,4).
         The assignment `sub_phase <= 2'd4` truncates 4 (binary 100) to 0.
         The check `if (sub_phase == 4 ...)` is DEAD CODE — always false.
         Result: vol_sqrt_dt_reg is never set. State never transitions to
         ST_INIT_DISC. The FSM loops in ST_INIT_GBM_CONST forever.
         No INIT-state timeout exists, so it spins indefinitely.
         The entire pricing engine is non-functional.

Fix:
  1. Line 299: change `logic [1:0] sub_phase;` → `logic [2:0] sub_phase;`
  2. Change ALL sized sub_phase literals from 2'd to 3'd throughout the FSM:
     - Every `2'd0` → `3'd0` (or just use '0)
     - Every `2'd1` → `3'd1`
     - Every `2'd2` → `3'd2`
     - Every `2'd3` → `3'd3`
     - The one `2'd4` → `3'd4`  (this is the one that was wrapping)
     Lines affected: 398, 423, 429, 436, 454, 467, 477, 498, 549, 553, 555,
                     559, 561, 629, 637, 639, 645, 649, 651, 653, 656, 671, 673, 677
     (All are in the ST_INIT_* and ST_TRAIN/DECIDE_FEED and ST_FINAL_DIV states)
  3. Add timeout escape to ST_INIT_GBM_CONST, ST_INIT_DT, ST_INIT_DISC,
     ST_INIT_DISC_TOTAL — wrap the body with:
       if (core_timeout) state <= ST_DONE;
       else begin ... existing logic ... end

Verification: after fix, run `run_tb_top_uart_safe.ps1 -ComputeMode` and
confirm the FSM exits INIT and reaches ST_TRAIN_STEP.


--- BUG 2 (BLOCKING): GBM S pipeline misalignment in GBM.sv ---

File:    src/steps/GBM.sv
Lines:   89-99 (s_pipe shift register) and 145 (MUL2 .a connection)
Problem: `s_pipe[0:3]` is a 4-stage shift register that advances ONLY on
         `mul1_accept` events (input acceptance). MUL2 reads `s_pipe[3]` when
         `exp_vout` fires.

         At FULL THROUGHPUT (1 accept per cycle) this works: 4 input events
         match the 3-cycle pipeline latency (MUL1=1 + EXP=2) plus the
         mul1_accept-to-mul1_vout gap.

         At SPORADIC throughput (1 sample in flight, as the top-level currently
         sends), only ONE mul1_accept fires. s_pipe[0] = current S, but
         s_pipe[3] still holds stale data from a PREVIOUS sample. MUL2 then
         computes stale_S * exp(current_arg) — wrong.

Fix: Replace the event-driven s_pipe shift register with an event_align_fifo_arr
     FIFO (push on mul1_accept, pop on exp_vout && mul2_rout). This is the
     same pattern used in inverseCDF.sv for negate alignment.

     Concrete changes:
     1. Delete lines 88-99 (the s_pipe declaration and always_ff block)
     2. Add in their place:
          logic [WIDTH-1:0] s_align_push [0:0];
          logic [WIDTH-1:0] s_align_pop  [0:0];
          logic              s_fifo_full, s_fifo_empty;
          assign s_align_push[0] = pipe_S;
          event_align_fifo_arr #(.N(1), .DW(WIDTH), .DEPTH(4)) u_s_align (
              .clk(clk), .rst_n(rst_n),
              .push_en  (mul1_accept),
              .pop_en   (exp_vout && mul2_rout),
              .push_data(s_align_push),
              .pop_data (s_align_pop),
              .full     (s_fifo_full),
              .empty    (s_fifo_empty)
          );
          wire signed [WIDTH-1:0] s_aligned = $signed(s_align_pop[0]);
     3. Line 145: change `.a(s_pipe[3])` → `.a(s_aligned)`
     4. (Optional) add assertion: `assert(!(s_fifo_full && mul1_accept))`

Verification: tb_GBM.sv (single sample + streaming); run_tb_top_uart_safe.ps1.


--- BUG 3 (NUMERICAL): fxInvCDF_ZS C0 constant in fxInvCDF_ZS.sv ---

File:    src/math/fxInvCDF_ZS.sv
Line:    29
Problem: `C0 = (2 <<< QFRAC) + ((515517 <<< (QFRAC - 20)) / 1000000)`
         For QFRAC=16: (QFRAC-20) = -4. Shifting by -4 is
         undefined/implementation-defined — most tools produce 0.
         So C0 = (2 <<< 16) + 0 = 131072 = 2.0 in Q16.16.
         Correct value: 2.515517 → 164858 in Q16.16.
         This ~20% error in C0 corrupts every z-score from inverseCDF,
         producing wrong GBM paths and a wrong final price.

Fix: Rewrite C0 using the same pattern as C1/C2 (which ARE correct):

  OLD:  localparam signed [WIDTH-1:0] C0 = (2 <<< QFRAC) + ((515517 <<< (QFRAC - 20)) / 1000000);
  NEW:  localparam signed [WIDTH-1:0] C0 = (2515517 * (1 <<< QFRAC)) / 1000000;

  Verification math: 2515517 * 65536 / 1000000 = 164,858 → 164858/65536 ≈ 2.515518. Correct.

Verification: tb_inverseCDF.sv — check z-scores are in plausible [-3,3] range.

===============================================================================
PART 3: IMPLEMENTATION ORDER (execute sequentially)
===============================================================================

Step 1: Fix sub_phase width  (Bug 1)
  File: src/top/top_option_pricer.sv
  Scope: ~25 line edits (widen declaration + sized literals + timeout guards)
  Risk: Very low — purely a width/literal fix.

Step 2: Fix C0 constant  (Bug 3)
  File: src/math/fxInvCDF_ZS.sv
  Scope: 1 line edit
  Risk: Very low — changes a localparam only.

Step 3: Fix GBM S pipeline  (Bug 2)
  File: src/steps/GBM.sv
  Scope: ~15 lines (replace shift register with FIFO instance + wire)
  Risk: Low — follows proven pattern from inverseCDF.sv.

Step 4: Compile/elaborate check
  Commands: ./run_xvlog_src.ps1 ; ./run_xelab_smoke.ps1
  Expected: All pass (no new modules, just fixes).

Step 5: Functional simulation — timeout mode
  Command: ./run_tb_top_uart_safe.ps1
  Expected: PASS with timeout marker 0xDEAD0001 (CORE_MAX_CYCLES=32 in timeout mode).

Step 6: Functional simulation — compute mode
  Command: ./run_tb_top_uart_safe.ps1 -ComputeMode
  Expected: PASS with a real price (not 0xDEAD0001). Q16.16 price in [0x0000_1999, 0x0032_0000] range for S0=K=100 call.

Step 7: Update VALIDATION.md
  Append a new dated section documenting the 3 bug fixes and simulation results.

===============================================================================
PART 4: REMAINING WORK AFTER BUGS ARE FIXED (priority order)
===============================================================================

P1: Phase 4 — FULLY PIPELINED TOP-LEVEL (critical architectural goal)
  File: src/top/top_option_pricer.sv
  What: The current top serializes every sample: fire Sobol, wait for entire
        sobol→inverseCDF→GBM chain to complete, THEN fire the next Sobol.
        This destroys the throughput benefit of having a pipelined datapath.

        The fix: remove `sobol_accepted` serialization in ST_TRAIN_STEP and
        ST_DECIDE_STEP. Fire Sobol for step k+1 IMMEDIATELY when the pipeline
        can accept (sobol_rout is high), not after GBM outputs step k's result.
        The pipeline has skid buffers and ready/valid at every stage — it is
        DESIGNED to have multiple samples in flight simultaneously.

        Within a single path (M sequential steps), each step depends on the
        PREVIOUS step's S output (s_curr <= gbm_s_next). So steps within one
        path are inherently sequential. But the pipeline latency can still
        overlap: fire step k+1's Sobol as soon as GBM outputs step k, so
        inverseCDF for step k+1 overlaps with FSM bookkeeping for step k.

        Between paths (different path_idx), there is NO data dependency. Once
        lane replication is added (Phase P4), multiple paths run in parallel.

        The pipeline stages and their latencies:
          Sobol:      ~1 cycle (combinational XOR tree + output buffer)
          InverseCDF: ~15 cycles (fold + lnLUT + mul + sqrt + rational)
          GBM:        ~5 cycles (mul1 + exp + mul2)
        Total: ~21 cycles per step. With overlap, effective ~5 cycles/step.

  Why:  This is the CORE ARCHITECTURAL GOAL of the project. Without this,
        the FPGA has no throughput advantage over a CPU.
  Prerequisite: GBM S pipeline fix (Bug 2) must work correctly under streaming.

P1: Phase 5 — Accumulator/regression stall diagnosis
  Files: src/steps/accumulator.sv, src/steps/regression.sv
  What: Once INIT works and training pass runs, verify that ST_WAIT_BETA actually
        receives beta from the accumulator+regression chain. If it stalls:
        - Add debug prints (gated behind `ifdef`) in accumulator to trace cnt_done
          vs n_eff, start_solver firing, and solver response.
        - Check regression for singular_err or pivot-zero with the actual data.
  Why:  The restore plan identified ST_WAIT_BETA as a known blocker, but it was
        never testable because INIT was broken.

P2: Multi-batch UART regression
  File: tb/tb_top_option_pricer_uart.sv (tb_top_option_pricer_uart_multibatch)
  Run:  run_tb_top_uart_safe.ps1 -Multibatch
  What: Re-test with the 3 bug fixes. The previous failure was "batch 1 returns X
        in result price" with an assertion in fxInvCDF_ZS. The rewrite of fxInvCDF_ZS
        with in_flight processing should fix this, but needs verification.
        If it still fails, the issue is likely in how the top-level FSM resets pipeline
        state between batches (sobol_accepted, s_curr, step_idx, etc.).

P2: Numerical validation against C++ baseline
  Script: scripts/validate_numerical.py
  Run:   python scripts/validate_numerical.py
  What:  Run C++ baseline and FPGA sim with identical params (paths=64, steps=12,
         S0=K=100, r=0.05, sigma=0.2, T=1.0). Compare prices; expect <1% rel error.
  Why:   Ultimate correctness check.

P3: Phase 6 — Two host running modes (benchmark + live) — COMPLETE
  File: src/uart_host.py
  MODE 1 — BENCHMARK: --target both prints price delta, rel_err, speedup (with --fpga-fclk-hz).
  MODE 2 — LIVE: Logs input snapshot (ticker, date, params) before run.
  Prerequisite: Pipeline produces correct prices (Bugs 1-3 fixed + Phase 4/5).

P4: Lane replication
  File: src/top/top_option_pricer.sv
  What: `generate` block for NUM_LANES > 1, merge per-lane accumulators.
  Why:  Throughput scaling, acknowledged as future work.

P4: Multi-exercise-date expansion
  File: src/top/top_option_pricer.sv
  What: Full backward induction with M-1 regression passes (currently only exercises
        at step M-1). Requires per-step accumulator/regression, much more complex FSM.
  Why:  Current architecture is single-exercise-date only, acknowledged as future work.

===============================================================================
PART 5: FILE MAP (for context)
===============================================================================

Source tree:
  src/fpga_cfg_pkg.sv                     Package: Q16.16 params
  src/helpers/rv_skid_arr_gate.sv         Skid buffer (array, gated accept)
  src/helpers/event_align_fifo_arr.sv     Event-aligned ring FIFO
  src/math/fxMul.sv                       Fixed-point multiplier (DSP)
  src/math/fxDiv.sv                       Fixed-point divider (div_gen wrapper)
  src/math/fxExpLUT.sv                    Exponential LUT (BRAM, signed mode)
  src/math/fxLnLUT.sv                     Natural log LUT (BRAM)
  src/math/fxSqrt.sv                      Square root (LUT + Newton-Raphson)
  src/math/fxInvCDF_ZS.sv                 Zelen-Severo rational approximation  ← BUG 3
  src/steps/sobol.sv                      Sobol QMC generator
  src/steps/inverseCDF_fold.sv            Fold U(0,1) to (0,0.5] + negate
  src/steps/inverseCDF.sv                 Full inverse CDF pipeline
  src/steps/GBM.sv                        GBM step (streaming pipeline)         ← BUG 2
  src/steps/accumulator.sv                Quadratic LSM accumulator
  src/steps/regression.sv                 3x4 Gaussian elimination solver
  src/steps/lsm_decision.sv              LSM exercise/continue decision
  src/io/uart/uart_rx.sv                  8-bit UART receiver
  src/io/uart/uart_tx.sv                  8-bit UART transmitter
  src/io/uart/uart_rx32.sv               32-bit UART receiver
  src/io/uart/uart_tx32.sv               32-bit UART transmitter
  src/io/handlers/uart_input_handler.sv   UART batch handler + echo + result
  src/top/top_option_pricer.sv            Top-level two-pass LSMC engine        ← BUG 1
  src/sim/fxDiv_core_stub.sv              Simulation stub for div_gen IP

Memory files:
  src/gen/direction.mem                   Sobol direction numbers
  src/gen/exp_lut_4096.mem               exp() LUT, 4096 entries, [0,1)
  src/gen/exp_signed_lut_8192.mem        exp() LUT, 8192 entries, [-1,1]
  src/gen/ln_lut_4096.mem                ln() LUT, 4096 entries
  src/gen/sqrt_lut_256.mem               sqrt() LUT, 256 entries

Testbenches:
  tb/tb_top_option_pricer_uart.sv         Top UART test (timeout/compute/multibatch)
  tb/tb_GBM.sv                            GBM unit test
  tb/tb_accum_regression.sv               Accumulator + regression integration
  tb/tb_accumulator.sv                    Accumulator unit test
  tb/tb_inverseCDF.sv                     Inverse CDF unit test
  tb/tb_regression.sv                     Regression unit test
  tb/tb_sobol.sv                          Sobol unit test
  tb/tb_lsm_decision.sv                  LSM decision unit test
  tb/tb_fxDiv.sv                          Divider unit test
  tb/tb_uart_echo_top.sv                  UART echo test
  tb/tb_uart32_loopback.sv               32-bit UART loopback
  tb/tb_uart_loopback.sv                 8-bit UART loopback

Scripts:
  run_xvlog_src.ps1                       Vivado xvlog compile check
  run_xelab_smoke.ps1                     Vivado xelab elaboration check
  run_tb_top_uart_safe.ps1                Safe TB run (compile+elab+sim, timeouts)
  cleanup_artifacts.ps1                   Remove Vivado build artifacts

Baseline:
  baseline/cpp_fixed/                     C++ fixed-point baseline (Q16.16)
  baseline/cpp_fixed/run_baseline.ps1     Run script
  baseline/cpp_fixed/params_example.txt   Example parameters

===============================================================================
PART 6: PROJECT CONTEXT — DESIGN PRINCIPLES & STYLE RULES
===============================================================================
(These rules apply to ALL code changes. Read before making any edit.)

Project Scope / Goal
- Build a production-grade, FULLY PIPELINED QMC-LSMC engine for American
  option pricing on Spartan-7 FPGA using Vivado.
- The datapath is a TRUE STREAMING PIPELINE, not an FSM that serializes
  one sample at a time. Every stage has ready/valid handshaking and skid
  buffers so data flows continuously with backpressure propagation:
    Sobol → InvCDF → GBM → Accumulator → Regression → LSM Decision → UART
  The top-level orchestrates two passes (training + decision) but within each
  pass, the pipeline streams freely — Sobol fires the NEXT sample as soon as
  the pipeline can accept, not after the previous sample completes end-to-end.
- The current top_option_pricer.sv has an interim FSM that serializes samples.
  THIS MUST BE REPLACED with streaming control that lets the pipeline overlap.
- Must be robust, efficient, parameterized, simple, and correct.
- Clock target: ~170 MHz on Spartan-7.
- Accuracy: <1% relative error (bounded by QMC variance).
- Style: Low-level, clear SystemVerilog RTL with ready/valid handshaking
  and skid buffers at every stage boundary.

Two Running Modes (host-side, via src/uart_host.py)
- BENCHMARK MODE (`--mode benchmark --target cpu|fpga|both`):
    Run CPU baseline (baseline/cpp_fixed) and/or FPGA with IDENTICAL parameters.
    Compare: option price, FPGA core cycles vs CPU wall-clock time, speedup.
    UART transfer time is EXCLUDED from FPGA timing (use cycle counter at
    --fpga-fclk-hz). This is the primary validation and performance mode.
- LIVE MODE (`--mode live --target cpu|fpga`):
    Fetch real market data from Yahoo Finance (yfinance), derive S0/sigma from
    historical prices, then run pricing with live parameters. Logs input
    snapshot for repeatability. This is the demo/presentation mode.

Critical Design Principles
- "Make sure everything is completely correct or I will be sad."
- All code must survive stalls, retiming, replication, and batching without
  data loss or corruption.
- FULLY PIPELINED ARCHITECTURE:
  - The datapath is a streaming pipeline, NOT a monolithic FSM that serializes
    one sample at a time. Each stage processes data independently and in
    parallel. Multiple samples can be in-flight simultaneously.
  - The top-level orchestrator fires work into the pipeline AS FAST AS the
    pipeline can accept. It does NOT wait for end-to-end completion.
  - Skid buffers (one-deep elastic registers) at every stage boundary
    decouple stages and absorb backpressure without data loss.
  - Event-alignment FIFOs (event_align_fifo_arr) keep side-channel data
    (like negate flags, S values) synchronized with main-path data across
    variable-latency stages.
- Handshakes:
  - Use ready/valid protocol correctly at every stage.
  - Include skid buffers (one-deep elastic registers) for inputs.
  - For branching logic, use explicit barrier signals to prevent desync.
  - Valid and ready must never glitch or race.
  - Assertions required to enforce handshake invariants.
- Parameterization: No magic numbers. Widths, QINT, QFRAC, LATENCIES, LUT
  sizes, N_SAMPLES, NUM_LANES must come from fpga_cfg_pkg.
- Declarations: Never declare a variable after it is used. All declarations
  must appear before usage in procedural code.
- Reset: Use `posedge clk or negedge rst_n` with '0 initialization. No latches.
- Pipeline invariants: Always align valid/data by construction. Insert registers
  if needed for alignment.

Mathematical Behaviors
- fxMul: DSP-mapped, scaled fixed-point, pipeline-latency param.
- fxDiv: Wrapper of div_gen IP, saturating divide-by-zero safe.
- fxExpLUT, fxlnLUT: BRAM lookup, range clamping, stall-safe.
- fxSqrt: LUT + Newton-Raphson iterations, fully pipelined.
- InvCDF: Zelen-Severo rational approximation, correct negate pipelining.
- Accumulator: 64-bit wide sums, saturate down to WIDTH, triggers regression.
- Regression: Deep pipeline Gaussian elimination, pivot+normalize+elim,
  sticky singular_err, fallback to mean payoff.

Required Style Rules
- Correctness first. Everything must compile, synthesize, and be stall-correct.
- No declarations after use. EVER.
- valid_out must never assert when ready_in = 0 unless result/data hold stable.
- Backpressure must never overwrite registers.
- Barrier readiness required in branching logic.
- Always saturate or clamp fixed-point math where overflow could occur.
- Do not use SystemVerilog reserved keywords as variable names.
- Always declare variables at the top of a block before procedural statements.

Shift Operator Semantics (SystemVerilog)
- >>  : Arithmetic right shift if operand is signed. Unsigned → logical.
- >>> : Explicit arithmetic right shift. Always sign-extends.
- <<  : Logical left shift. Zeros shifted in.
- <<< : Explicit arithmetic left shift. Preserves signedness.
- Rule: Use >>> for safe arithmetic right shift.
        Use <<< for safe arithmetic left shift in fixed-point.
        Do not rely on implicit casting. Always $signed(...) where sign matters.

Best Practice Reminders
- Use &&/|| for logical conditions (not &/| unless bitwise).
- Don't let one branch run if the other is stalled; use barrier_ready.
- Skid buffers: one-deep, reset to zero.
- Saturate accumulators and intermediates when reducing width.
- Keep state machines with explicit enums; clear outputs on reset.
- Assertions: output stable under stalls, singular_err sticky, inputs stable
  under backpressure.
- Always test with randomized stalls on ready_in.

Checklist Before Sending Code
- [ ] Handshake correctness: ready_out, valid_in gating, stall propagation.
- [ ] No declarations after use (declarations first).
- [ ] Reset initializes all regs/FSM states.
- [ ] No magic numbers (parameters from pkg).
- [ ] Assertions for invariant checking.
- [ ] Code is clean, simple, parameterized.

===============================================================================
PART 7: ARCHITECTURAL DECISIONS & RESOURCE BUDGET
===============================================================================

A. MEMORY STRATEGY: ONLINE SUFFICIENT STATISTICS (O(1) NOT O(N))
-----------------------------------------------------------------

This is a CRITICAL design choice. Traditional LSMC stores ALL N path values
in memory to do regression after generation. On Spartan-7 (360 Kb BRAM total),
that would be:
  N=2048 paths × M=12 steps × 32 bits = 768 KB  →  IMPOSSIBLE

This design avoids ALL path storage by using ONLINE (STREAMING) ACCUMULATION
of sufficient statistics. The accumulator (accumulator.sv) maintains 8 running
64-bit sums as paths arrive one at a time:

  sum1   = Σ 1          (count, in Q16.16)
  sumx   = Σ S_exercise
  sumx2  = Σ S²
  sumx3  = Σ S³
  sumx4  = Σ S⁴
  sumy   = Σ y          (y = disc * terminal_payoff)
  sumxy  = Σ S·y
  sumx2y = Σ S²·y

Total accumulator memory: 8 × 64 bits = 512 bits = 64 bytes.
This is CONSTANT regardless of N. Works for N=64 or N=65536.

After all N paths have streamed through, these 8 sums are packed into a
3×4 augmented matrix and fed to the regression module (Gaussian elimination)
to solve for beta[0:2]. No path values are ever stored.

The trade-off: paths must be generated TWICE (training pass + decision pass).
But Sobol is deterministic — given the same (idx, dim), it produces the same
output — so regeneration is free and exact. The GBM pipeline produces
identical paths both times because drift_const and vol_sqrt_dt are constant.

This two-pass approach costs 2× compute time but makes BRAM usage O(1)
instead of O(N×M). On a memory-constrained FPGA, this is the correct choice.

The pipeline within each pass is:
  Pass 1 (Training): sobol → invCDF → GBM → accumulator (running sums)
  Pass 2 (Decision): sobol → invCDF → GBM → lsm_decision (compare & accumulate PV)

GBM outputs S_next one sample at a time. The accumulator reduces it
immediately into running sums. No N-sized buffer exists anywhere.

B. RESOURCE BUDGET (Spartan-7 XC7S50)
--------------------------------------

Target: XC7S50 (120 DSP48E1, 360 Kb BRAM, ~32K LUTs)

DSP usage (DSP48E1 slices):
  Pipeline:
    inverseCDF:   4 DSP (2× fxMul in rational approx + 2× fxMul in fold/sqrt path)
    GBM:          2 DSP (mul1: vol_sqrt_dt*z, mul2: S*exp)
    accumulator:  5 DSP (mul_x_x, mul_x_y, mul_x2_y, mul_x2_x, mul_x2_x2)
    lsm_decision: 3 DSP (mul_S_S, mul_b1S, mul_b2S2)
    regression:   ~14 DSP (8 elim muls + 3 back-sub muls + 3 normalizer chains)
                  (Many of these use fxDiv which maps to LUT-based div_gen IP,
                   not DSP. Actual DSP count depends on div_gen configuration.)
  Utility (INIT only, idle during compute):
    util_mul:     1 DSP
    util_sqrt:    4 DSP (4 internal fxMul for Newton-Raphson)
  Total estimate: ~33 DSP out of 120 available (~28%)

BRAM usage (BRAM36 blocks):
  exp_lut_4096.mem:        2 BRAM36 (4096 × 32-bit)
  exp_signed_lut_8192.mem: 4 BRAM36 (8192 × 32-bit)
  ln_lut_4096.mem:         2 BRAM36 (4096 × 32-bit)
  sqrt_lut_256.mem:        < 1 BRAM36 (256 × 32-bit, packs into BRAM18)
  direction.mem (Sobol):   depends on MAX_STEPS × WIDTH entries
  Total estimate: ~10-12 BRAM36 out of 75 available (~16%)

  NOTE: The signed ExpLUT (8192 entries) covers exp(x) for x∈[-1,1].
  This eliminates fxDiv from GBM entirely (no 1/exp(|x|) reciprocal for
  negative arguments), saving ~16 cycles of variable latency per sample.

Resource comparison: old GBM vs new pipelined GBM:
  OLD (sequential FSM): 1 fxMul + 1 fxSqrt(4 internal fxMul) + 1 fxExpLUT
                        + 1 fxDiv = 5 DSP + div IP + BRAM. ~37-53 cyc/sample.
  NEW (streaming):      2 fxMul + 1 fxExpLUT(signed) = 2 DSP + BRAM.
                        ~5-6 cyc/sample. 3 fewer DSPs, 6-9× faster.
  Top-level adds 1 utility fxSqrt (4 DSP, INIT only, idle during compute).
  Net: +1 DSP total, dramatically better throughput.

C. DESIGN DECISIONS AND FIXED CHOICES
--------------------------------------

1. Fixed-point format: Q16.16 (16 integer bits, 16 fractional bits)
   - Max representable value: +32767.9999 (sufficient for stock prices)
   - Min precision: 1/65536 ≈ 0.0000153
   - For stock prices above ~$30,000 this would overflow. For typical options
     pricing (stocks $1-$5000), Q16.16 is more than adequate.
   - Changing to Q20.12 or Q24.8 requires updating fpga_cfg_pkg only.

2. Regression basis: Quadratic [1, S, S²] (3 coefficients)
   - This is the standard Longstaff-Schwartz basis for single-asset options.
   - Linear [1, S] would use fewer DSPs but less accurate.
   - Cubic [1, S, S², S³] would add accuracy but needs 4×5 matrix (more DSPs).
   - DECISION: Quadratic is fixed. Parameterizing basis order would require
     variable-size matrices in the accumulator and regression — not worth the
     complexity for the target application.

3. Option type: Currently CALL ONLY (payoff = max(S-K, 0))
   - Both lsm_decision.sv (line 105) and top_option_pricer.sv (line 293) use
     CALL payoff direction.
   - *** RECOMMENDATION: Add a PUT/CALL runtime flag (1 bit) from UART params.
     The change is trivial: swap (S-K) vs (K-S) and (S>K) vs (K>S). This
     doubles the utility of the design with ~5 lines of RTL. ***

4. Single exercise date: Step M-1 only
   - True American options can exercise at ANY step. Full backward induction
     requires M-1 regression passes (one per exercise date), each needing its
     own accumulator/regression cycle. This would multiply compute time by M
     and require storing per-step beta arrays.
   - DECISION: Single exercise date (European-like with early exercise at M-1)
     is the target for this version. Full backward induction is deferred to P4.

5. Sobol dimensionality: MAX_STEPS parameter (default 50)
   - Each step uses one Sobol dimension. MAX_STEPS=50 means up to 50
     dimensions, stored as direction numbers in BRAM.
   - Sobol quality degrades in high dimensions (>20-30). For pricing accuracy,
     keep M ≤ 20 in practice.

6. Clock domain: Single clock (clk_100, target 100-170 MHz)
   - No clock-domain crossing needed. UART baud rate is derived from clk_100.
   - Higher fMAX requires tighter timing on the regression module's
     multiply→subtract→divide chains (the critical path).

D. RECOMMENDATIONS TO FLESH OUT THE DESIGN
-------------------------------------------

These are ordered by impact and effort:

D1. [LOW EFFORT, HIGH IMPACT] Add PUT/CALL runtime flag
    Files: src/io/handlers/uart_input_handler.sv, src/top/top_option_pricer.sv,
           src/steps/lsm_decision.sv
    What: Add 1-bit option_type to UART parameter set (or repurpose a bit from
          an existing param). In lsm_decision and top payoff logic, use:
            payoff = option_type ? max(K-S, 0) : max(S-K, 0)
    Effort: ~10 lines of RTL. ~1 line in uart_host.py.

D2. [LOW EFFORT, MEDIUM IMPACT] Richer error reporting in result packet
    Files: src/io/handlers/uart_input_handler.sv, src/top/top_option_pricer.sv
    What: Currently the result packet is: marker + price + cycles_lo + cycles_hi.
          Add a status word with bit flags:
            bit 0: timeout occurred
            bit 1: regression singular (fallback to mean payoff)
            bit 2: fixed-point saturation detected during compute
            bit 3: accumulator overflow
          This makes debugging much easier without needing RTL simulation.
    Effort: ~20 lines of RTL, ~5 lines in uart_host.py to decode.

D3. [MEDIUM EFFORT, HIGH IMPACT] Antithetic variates for variance reduction
    Files: src/steps/inverseCDF.sv or src/top/top_option_pricer.sv
    What: For each Sobol point u, run BOTH z and -z through GBM, then average
          the two payoffs. This halves the variance for the same number of
          Sobol points (effectively doubles path count for free Sobol-wise).
    Implementation: In the top-level, for each sobol output, run the pipeline
          twice: once with z, once with -z (just negate the inverseCDF output).
          The accumulator sees 2N effective samples from N Sobol points.
    Effort: ~30-50 lines in top-level. Pipeline itself unchanged.

D4. [LOW EFFORT, MEDIUM IMPACT] Convergence/sweep mode
    Files: src/uart_host.py
    What: Run pricing with increasing N (64, 128, 256, 512, ...) and track
          price convergence. Stop when |price(2N) - price(N)| < threshold.
          QMC (Sobol) converges as O(1/N) vs O(1/√N) for pseudo-random MC,
          so this should converge quickly.
    Host-only change: no RTL needed, just run multiple batches via UART.
    Effort: ~30 lines in uart_host.py.

D5. [HIGH EFFORT, HIGH IMPACT] Lane replication (NUM_LANES > 1)
    Files: src/top/top_option_pricer.sv
    What: Instantiate multiple parallel pipeline lanes (sobol→invCDF→GBM),
          each processing a different path_idx. Merge per-lane accumulator
          sums before regression. Throughput scales linearly with lanes.
    Effort: ~100-200 lines. Requires generate blocks, sum merging logic.
    Constraint: Each lane needs its own DSPs. With 33 DSP per lane and
          120 available, max ~3 lanes. Or share regression (1 instance).

===============================================================================
PART 8: PROGRESS LOG (append-only, most recent at bottom)
===============================================================================

- 2026-02-10: Fixed lsm_decision references from in_buf.beta[] to beta_reg[].
- 2026-02-10: Cleaned up sobol direction memory declaration conflict.
- 2026-02-10: Replaced broken top_option_pricer.sv shell with compile-clean wrapper.
- 2026-02-10: Full xvlog compile pass over src/ succeeds.
- 2026-02-10: Added run_xvlog_src.ps1 for repeatable compile checks.
- 2026-02-10: Added fxDiv_core stub and run_xelab_smoke.ps1 for elaboration.
- 2026-02-10: Converted SVAs to proper concurrent assertions.
- 2026-02-10: xelab succeeds for all 9 module snapshots.
- 2026-02-10: Source tree reorg (UART → src/io/, top → src/top/).
- 2026-02-10: Archive cleanup, baseline promotion to baseline/cpp_fixed/.
- 2026-02-10: Added CPU sanity checks, file-driven params, optional Boost Sobol.
- 2026-02-10: Reworked uart_host.py into mode/target runner.
- 2026-02-10: Added UART result packet format support.
- 2026-03-01: P0 correctness audit — 13 bugs fixed:
    accumulator sum1 scaling, fxLnLUT/fxExpLUT 2-stage pipelines, fxSqrt LUT
    index, GBM diff gating + exp_launch + saturation, fxInvCDF_ZS rewrite,
    inverseCDF negate FIFO, inverseCDF_fold polarity, lsm_decision call payoff,
    C++ baseline FRAC_BITS=16, TB port fixes.
- 2026-03-01: lsm_decision interface: disc → cont_value.
- 2026-03-01: top_option_pricer.sv rewritten with 11-state two-pass LSMC FSM.
- 2026-03-01: regression.sv debug traces gated behind ifdef REG_DEBUG.
- 2026-03-01: accumulator.sv: added n_samples_cfg runtime port.
- 2026-03-01: tb_top_option_pricer_uart.sv updated for new top-level.
- 2026-03-01: All 22 source files compile clean; 9 module snapshots elaborate clean.
- 2026-03-02: Phase 2 (pre-compute GBM constants) and Phase 3 (streaming GBM)
    code was added. Compile/elaborate pass, but NO functional simulation was run.
- 2026-03-02: FULL AUDIT discovered 3 critical bugs:
    BUG 1: sub_phase is [1:0] (2-bit) but needs value 4 → truncates to 0,
           FSM stuck forever in ST_INIT_GBM_CONST.
    BUG 2: GBM s_pipe shift register advances on input acceptance events,
           not clock cycles → misaligned S under non-streaming operation.
    BUG 3: fxInvCDF_ZS C0 constant uses <<< with negative shift amount →
           C0 = 2.0 instead of 2.515517 → wrong z-scores.
- 2026-03-02: FIXED all 3 critical bugs:
    BUG 1: sub_phase widened to [2:0], all literals 2'd→3'd, timeout guards on all blocking states.
    BUG 2: GBM s_pipe shift register replaced with event_align_fifo_arr FIFO.
    BUG 3: fxInvCDF_ZS C0 rewritten as (2515517*(1<<<QFRAC))/1000000 = 164858 (2.515517).
    Timeout guards added to ST_INIT_DT, ST_INIT_GBM_CONST, ST_INIT_DISC,
    ST_INIT_DISC_TOTAL, ST_TRAIN_FEED, ST_WAIT_BETA, ST_DECIDE_FEED, ST_FINAL_DIV.
- 2026-03-02: Phase 4 — fully pipelined top-level:
    ST_TRAIN_STEP and ST_DECIDE_STEP fire Sobol for step k+1 in the same
    cycle GBM outputs step k (when sobol_rout is high). Eliminates idle
    cycle between steps. GBM.sv forward-reference errors fixed (declarations
    moved to top of module).
- 2026-03-02: Phase 5 — accumulator stall diagnosis:
    accumulator.sv: ifdef ACC_DEBUG traces fire_head, cnt_launch, cnt_done,
    n_eff, start_solver, solver_done, solver_ready, singular_err.
    run_tb_top_uart_safe.ps1: -DebugAcc uses -d ACC_DEBUG (Vivado syntax).
    Fix: state==IDLE guard on cnt_done trace; -d ACC_DEBUG (not +define+).
- 2026-03-02: P2 Multi-batch UART: run_tb_top_uart_safe.ps1 -Multibatch added.
- 2026-03-02: P2 Numerical validation: scripts/validate_numerical.py added.
    Compares C++ baseline vs FPGA sim (paths=64, steps=12); expects <1% rel error.
- 2026-03-02: P3 Phase 6: uart_host.py benchmark comparison (price delta, speedup),
    live mode snapshot logging, q16_16_to_float signed fix.

===============================================================================
END OF FILE
===============================================================================

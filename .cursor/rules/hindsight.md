---
description: Learned behavioral patterns from past errors. Not retrieval — active behavior modification. Append new lessons, never delete.
globs: ["**/*.sv", "**/*.py", "**/*.ps1"]
alwaysApply: true
---

# Hindsight: Learned Behavioral Patterns

These are not facts to recall. They are rules that change how I act.

## Constant Definition Traps

RULE: Never use 1-bit signed literals for fixed-point constants.
- `1'sd1` is -1 in two's complement, not +1
- `1'sd1 <<< 16` = -65536, not +65536
- ALWAYS use `32'sd1 <<< QFRAC` or `fpga_cfg_pkg::FP_ONE`
- This single pattern caused bugs N1 (ONE_Q) and N4 (HALF) independently
- Both went undetected through compilation. Only functional sim caught them.

RULE: Never hand-compute Q16.16 literals. Use fp_from_real().
- `(2515517 * (1 <<< QFRAC)) / 1000000` overflows 32-bit signed silently
- Vivado truncates without warning. The constant looks plausible but is wrong.
- Precompute as `32'sd164857` and add elaboration assertion:
  `assert(C0 >= fpga_cfg_pkg::fp_from_real(2.515517) - 1)`
- This caught 3 wrong Z-S constants (C0, C1, D1) after initial precompute.

RULE: Elaboration assertions are not optional for precomputed constants.
- Every precomputed `localparam` that represents a real number must have
  a `// synthesis translate_off` assertion comparing against `fp_from_real`.
- Tolerance: +/- 1 LSB.

## Pipeline Alignment Traps

RULE: Registered FIFO outputs cause 1-cycle misalignment.
- `pop_data <= mem[rptr]` (registered) reflects PREVIOUS head, not current.
- Use combinational read: `assign pop_data = mem[rptr]`.
- This caused bug N8: negate_aligned was 1 cycle late, flipping signs.

RULE: Event-driven shift registers break under sporadic throughput.
- A shift register advancing on input events (not clock) works at full
  throughput but fails when only 1 sample is in flight (stale data at tail).
- Replace with event_align_fifo_arr (push on accept, pop on output valid).
- This caused bug 2: GBM s_pipe had stale S under serialized top-level.

RULE: Skid-buffer pattern is incompatible with multi-cycle compute blocks.
- A skid buffer assumes 1-cycle accept. If the downstream block takes N
  cycles, the circular ready dependency can deadlock.
- Use busy flag + started pulse pattern instead for multi-cycle blocks.
- This caused the lsm_decision stall.

## Fixed-Point Overflow Traps

RULE: Raw stock prices overflow Q16.16 in polynomial regression.
- S=100 → S^4=10^8, but Q16.16 max=32767. Saturates silently.
- ALWAYS normalize by moneyness (S/K ≈ 1.0) before regression.
- This caused bug N2: 842% pricing error from corrupted regression matrix.

RULE: Q0.32 to Q16.16 conversion is not just $signed().
- Sobol outputs Q0.32 unsigned. $signed(0x80000000) = -32768 in Q16.16.
- Correct: `$signed({16'd0, sobol_out[31:16]})` — explicit format conversion.
- This caused bug N3: inverseCDF received garbage uniform values.

RULE: LUT address wraparound corrupts interpolation at boundaries.
- addr_next = addr + 1 wraps from 4095 to 0 for 12-bit address.
- Clamp: `(&addr) ? addr : addr + 1'b1`
- This caused the fxLnLUT interpolation delta to be wildly wrong at boundary.

## Toolchain Traps (Vivado + PowerShell)

RULE: PowerShell $proc.ExitCode can be null with Start-Process.
- `$proc.ExitCode -ne 0` treats null as non-zero → false failure.
- Use: `$ec = $proc.ExitCode; if ($null -ne $ec -and $ec -ne 0)`
- This caused every script to report failure despite successful compilation.

RULE: Vivado xvlog uses `-d MACRO`, not `+define+MACRO`.
- `+define+` is VCS syntax. xvlog interprets it as a filename.
- Use `-d ACC_DEBUG` for conditional compilation.

RULE: Vivado silently truncates 32-bit integer overflow in localparams.
- `2515517 * 65536 = 164B` exceeds int32 max. Vivado wraps, no warning.
- Precompute constants externally and use `32'sd` literals.

RULE: xsim simulation speed does NOT represent FPGA hardware speed.
- xsim is behavioral simulation — ~1000x slower than RTL on FPGA.
- FPGA speed = core_cycles / fclk_hz. Use cycle counter, not wall time.
- Only synthesize + place-and-route timing gives real fMAX.

## Workflow Traps

RULE: When execution hangs, kill and restart. Do not sleep-retry.
- Stale xsim.dir locks cause indefinite hangs.
- Run `Remove-Item -Recurse -Force xsim.dir` before retrying.
- If xvlog times out, check for lock files first.

RULE: Run compile checks individually, never batched.
- Running xvlog + xelab + xsim in parallel can cause resource contention.
- Each tool should complete before the next starts.

RULE: PowerShell heredoc syntax fails in git commit messages.
- Multi-line commit messages with `@" ... "@` syntax fail.
- Use single-line commit messages: `git commit -m "single line"`.

RULE: Check git status before committing.
- Multiple agent sessions can leave conflicting unstaged changes.
- Always `git diff --stat` before `git add`.

## Algorithm Traps

RULE: fxLnLUT must compute ln(x), not ln(1+frac).
- Original LUT stored ln(1+frac) for frac∈[0,1). For x<1: wrong by 42%.
- Correct approach: range decomposition (find MSB, normalize, LUT lookup
  of fractional part, add int_log2 * ln(2)).

RULE: fxSqrt normalization must match refinement domain.
- If LUT uses normalized input a_norm∈[0.5,1.0), Newton refinement MUST
  also use normalized input. Mixing domains corrupts results.
- Current implementation: non-restoring digit-by-digit avoids this entirely.

RULE: Regression pivot fallback must use the correct valid signal.
- v6b (post-pivot2-divide) never fires if pivot2 is zero.
- fallback_req and singular_err must check v6 (pre-divide) when pivot2=0.
- v3 condition must not require && v2 (1-cycle pulse vs multi-cycle mul).

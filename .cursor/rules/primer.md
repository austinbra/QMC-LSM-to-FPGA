---
description: Session handoff state. Rewritten at end of each session. Read this FIRST to know where to pick up.
globs: ["**/*"]
alwaysApply: true
---

# Primer: Current Session State

Last updated: 2026-03-17

## Just Completed

- 5-layer memory system (rules.md, primer.md, hindsight.md, Obsidian vault)
- D2: richer error reporting (5-word result packet with status flags)
- D3: antithetic variates (paired z/-z paths, ANTITHETIC_EN parameter)
- D4: convergence sweep mode (uart_host.py --mode sweep)
- Synthesizable fxLnLUT (3-stage pipeline + linear interpolation)
- Synthesizable fxSqrt (non-restoring digit-by-digit, 25 cycles)
- Precision centralization (FP_ONE/HALF/NEG in fpga_cfg_pkg, elab assertions)
- Z-S constant corrections (C0, C1, D1 caught by elaboration assertions)
- Directory reorganization (PS1 scripts moved to scripts/)

## Numerical Status

- FPGA price (behavioral models, N=64): 6.553
- C++ baseline (N=64): 6.50
- Relative error: 0.8% (within QMC variance)
- With synthesizable math + antithetic (N=64 → 128 effective): needs revalidation

## Next 3 Priorities

1. **D5: Lane replication** (high effort, high impact)
   - `src/top/top_option_pricer.sv`: generate block for NUM_LANES > 1
   - Merge per-lane accumulator sums before regression
   - ~100-200 lines, needs DSP budget analysis

2. **Multi-exercise-date expansion** (high effort, high impact)
   - Full backward induction: M-1 regression passes
   - Per-step beta arrays, much more complex FSM
   - Currently exercises at step M-1 only

3. **FPGA hardware test** (medium effort, high impact)
   - Generate bitstream for XC7S50
   - On-board validation via UART
   - Compare hw results with simulation

## Open Blockers

- None. All modules compile, elaborate, and simulate clean.
- No behavioral models remain. Fully synthesizable.

## Branch

- `cursor/documentation-and-bug-fix-validation-d536`
- Working tree: clean (after pending commit of memory system + reorg)

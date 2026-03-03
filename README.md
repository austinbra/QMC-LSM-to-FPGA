# FPGA QMC‑LSMC American Option Pricer

## Overview
This project implements a **production‑grade, fully handshaked FPGA pipeline** for **American option pricing** using the **Longstaff–Schwartz Monte Carlo (LSMC)** method with **Quasi‑Monte Carlo (Sobol) sequences**.  
The design targets a **Xilinx Spartan‑7 FPGA** (Vivado flow) and is written in **SystemVerilog**.  

In addition to the FPGA implementation, the repository includes a **fixed‑point C++ baseline**:
- Located at `baseline/cpp_fixed/`.  
- Matches the FPGA-oriented fixed-point arithmetic flow for practical comparison.  

This allows direct comparison of **accuracy** and **performance** between CPU and FPGA implementations.

---

## Validation And Status
- Validation log: `VALIDATION.md` (commands run, results, known gaps).
- Active implementation tracker: `whats_next.md`.
- Current state: Pipeline stages (Sobol, InverseCDF, GBM, Accumulator, Regression, LSM Decision) are implemented with ready/valid + skid buffers. Top-level two-pass LSMC engine compiles/elaborates clean. Phase 4 streaming overlap is implemented (fire step k+1 same cycle as GBM output).

---

## Features
- **Fully pipelined streaming datapath** with skid buffers at every stage boundary:  
  Sobol → Inverse CDF (Zelen–Severo rational approx) → GBM path simulation → Accumulator → Regression (Gaussian elimination) → LSM decision → UART output.  
  Multiple samples in-flight simultaneously; backpressure propagates through ready/valid handshaking without data loss.
- **Fixed‑point math** (default Q16.16) with LUT‑based exp/ln/sqrt and Newton–Raphson refinement.
- **Two running modes** (host-side via `src/uart_host.py`):
  - **Benchmark**: CPU vs FPGA side-by-side with identical parameters; reports price, cycles, wall time, speedup.
  - **Live**: Fetches real market data from Yahoo Finance, derives S0/sigma, runs pricing with live parameters.
- **O(1) memory via streaming accumulation**: No path storage required. Running 64‑bit sufficient statistics (8 sums) replace O(N×M) BRAM. Paths are regenerated deterministically (Sobol) for the decision pass — 2× compute, but constant memory regardless of N.
- **Lane replication ready**: top‑level parameter to scale throughput by instantiating multiple parallel pipelines.
- **Assertions** for handshake invariants and stall stability.
- **Fixed‑point C++ baseline** for validation and performance comparison.

---

## Architecture

The design is a **fully pipelined, streaming datapath** with ready/valid handshaking and skid buffers at every stage boundary. The top-level orchestrates two passes (training + decision) while the pipeline stages process data in parallel with overlapping execution.

- **Sobol generator**: Gray‑coded XOR tree with BRAM‑stored direction numbers. Skid-buffered output.
- **Inverse CDF** (~15 cycles):  
  - Fold U(0,1) to (0,0.5] with negate flag (event-alignment FIFO for negate).
  - ln LUT + multiply by −2 + sqrt → t.  
  - Zelen–Severo rational polynomial → z‑score.  
- **GBM step** (~5 cycles, streaming pipeline with input skid buffer):  
  MUL1(vol_sqrt_dt × z) → ADD + saturate → EXP(signed LUT) → MUL2(S × exp).  
  Pre-computed constants (`drift_const`, `vol_sqrt_dt`) eliminate per-sample sqrt/mul overhead.
- **Accumulator** (O(1) memory, no path storage):  
  Collects 8 running sufficient statistics [Σ1, ΣS, ΣS², ΣS³, ΣS⁴, Σy, ΣSy, ΣS²y] in 64‑bit registers. Paths are consumed and reduced immediately — no N‑sized buffer exists anywhere. This is what makes the design feasible on a memory‑constrained Spartan‑7.
- **Regression**: Deeply pipelined Gaussian elimination with pivoting; fallback to mean payoff if singular.  
- **LSM decision**: Chooses between immediate exercise payoff and discounted continuation value.  
- **UART interface**: Streams results to host. Result packet: marker `0xABCD0001` + price + cycle count (lo/hi).

---

## Baselines (C++)
- **Fixed‑point baseline** (`baseline/cpp_fixed/`):  
  - Implements a fixed-point workflow aligned with the FPGA-oriented arithmetic path.  
  - Validates numerical behavior and supports CPU timing comparisons.  

---

## Build & Run
### FPGA (Vivado)

**Prerequisite:** Run from a shell where Vivado is in PATH (e.g. "Vivado 2023.x Command Prompt" or after sourcing `settings64.bat` / `settings64.sh`).

**Quick compile/simulate (recommended):**
```powershell
./run_xvlog_src.ps1          # Compile (uses vivado -mode batch by default)
./run_xelab_smoke.ps1       # Elaborate
./run_tb_top_uart_safe.ps1  # Simulate (timeout mode)
./run_tb_top_uart_safe.ps1 -ComputeMode  # Simulate (compute mode)
```

If scripts time out, ensure Vivado is in PATH. Alternatively run directly:
```bash
vivado -mode batch -source scripts/run_xvlog.tcl
```

**Numerical validation** (C++ vs FPGA sim):
```bash
cd baseline/cpp_fixed && g++ -std=c++17 main.cpp pricing.cpp linalg.cpp sobol_wrapper.cpp utils.cpp -o fixed_baseline
python scripts/validate_numerical.py
```

1. Add all SystemVerilog sources and memory initialization files (`*.mem`) to a Vivado project.  
2. Generate the `fxDiv_core` IP (Xilinx `div_gen`) with parameters matching `fxDiv.sv`.  
3. Add a clock constraint (e.g., 100 MHz).  
4. Run behavioral simulation with provided testbenches.  
5. Synthesize and implement for Spartan‑7.  

### C++ Baseline
1. Build `baseline/cpp_fixed/` with a modern C++ compiler (C++17 or later).  
2. Run with the same option parameters as the FPGA to compare results.  
3. For speed comparison, measure FPGA core cycles (exclude UART transfer time) and compare against baseline runtime.  
4. You can drive CPU/FPGA run modes from `src/uart_host.py` using `--mode benchmark|live` and `--target cpu|fpga|both`.  

### Running modes

Two host-side modes are supported via `src/uart_host.py`:

| Mode | Command | Purpose |
|------|---------|---------|
| **Benchmark** | `python src/uart_host.py --mode benchmark --target both --param-file baseline/cpp_fixed/params_example.txt` | Run CPU baseline and FPGA with identical params. Compare price, FPGA core cycles vs CPU wall time, speedup. UART I/O excluded from FPGA timing. |
| **Live** | `python src/uart_host.py --mode live --target fpga` | Fetch real market data from Yahoo Finance, derive S0 and sigma, run pricing. Logs input snapshot. |

### Current status
- Top-level two-pass LSMC engine compiles and elaborates clean.
- Three critical bugs fixed (sub_phase overflow, GBM S pipeline misalignment, InvCDF C0 constant).
- Phase 4 complete: FSM fires Sobol for step k+1 in the same cycle GBM outputs step k (zero idle cycles between steps).
- Phase 6 complete: benchmark + live host modes in `uart_host.py`.
- Next: numerical validation (`python scripts/validate_numerical.py`), FPGA hardware testing.

---

## Testing
- **Unit testbenches** for Sobol, inverse CDF, GBM, accumulator, and regression.  
- **Assertions** check handshake invariants and stall stability.  
- **C++ vs FPGA comparison**:  
  - Run both baselines and FPGA simulation with the same seeds/parameters.  
  - Compare option prices and timing.  
  - Expect <1% relative error (well within Monte Carlo variance).  

---

## Roadmap
- [x] Fixed‑point math library (fxMul, fxDiv, fxExpLUT, fxLnLUT, fxSqrt) with skid buffers.
- [x] Sobol generator (Gray-coded XOR tree, skid-buffered output).
- [x] Inverse CDF (fold + Zelen–Severo, event-alignment FIFO for negate flag).
- [x] GBM streaming pipeline (MUL→EXP→MUL, input skid buffer, pre-computed constants).
- [x] Accumulator + Regression (64-bit sums, Gaussian elimination, fallback).
- [x] LSM decision (exercise vs continuation comparison).
- [x] C++ fixed‑point baseline (Q16.16, aligned with FPGA arithmetic).
- [x] Top‑level two-pass LSMC integration with UART I/O.
- [x] **Phase 4: Fully pipelined top-level** — fire Sobol for step k+1 in same cycle as GBM output.
- [x] Two running modes: benchmark (CPU vs FPGA comparison) + live (Yahoo Finance data).
- [ ] PUT/CALL runtime flag (trivial: swap payoff direction, ~10 lines of RTL).
- [ ] Richer error reporting in result packet (timeout, singular regression, saturation flags).
- [ ] Numerical validation: `python scripts/validate_numerical.py` (paths=64, steps=12).
- [ ] Antithetic variates (run z and −z per Sobol point, halves variance for free).
- [ ] Lane replication (NUM_LANES > 1) for throughput scaling.
- [ ] Multi-exercise-date expansion (full backward induction).

> :warning: Active development — Phases 1-6 complete. See `whats_next.md` for full status.

---

## Contact
For questions or contributions, please open an issue or pull request.  

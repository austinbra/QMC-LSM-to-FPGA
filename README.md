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
- Active implementation tracker: `whats_next.txt`.
- Current state: compile/elaboration checks are passing, but full top-level pricing datapath integration is still in progress.

---

## Features
- **End‑to‑end pipeline**:  
  Sobol → Inverse CDF (Zelen–Severo rational approx) → GBM path simulation → Accumulator → Regression (Gaussian elimination) → LSM decision → UART output.
- **Fixed‑point math** (default Q16.16) with LUT‑based exp/ln/sqrt and Newton–Raphson refinement.
- **Fully handshaked ready/valid interfaces** with skid buffers and barrier synchronization for stall safety.
- **Mini‑batch accumulation**: accumulate regression sums across batches, run regression once, then sweep for path payoffs.
- **Lane replication ready**: top‑level parameter to scale throughput by instantiating multiple parallel pipelines.
- **Assertions** for handshake invariants and stall stability.
- **Fixed‑point C++ baseline** for validation and performance comparison.

---

## Architecture
- **Sobol generator**: Gray‑coded XOR tree with BRAM‑stored direction numbers.  
- **Inverse CDF**:  
  - Step1: Fold U(0,1) to (0,0.5] with negate flag.  
  - ln LUT + multiply by −2 + sqrt → t.  
  - Zelen–Severo rational polynomial → z‑score.  
- **GBM step**: Computes  
![equation](https://latex.codecogs.com/svg.latex?\dpi{120}\bg{transparent}\color{white}S_{t+1}=S_t\cdot\exp\big((r-0.5\sigma^2)\Delta%20t+\sigma\sqrt{\Delta%20t}\,z\big))

- **Accumulator**: Collects sufficient statistics for quadratic regression basis [1, S, S²] using 64‑bit accumulators.  
- **Regression**: Deeply pipelined Gaussian elimination with pivoting; fallback to mean payoff if singular.  
- **LSM decision**: Chooses between immediate exercise payoff and discounted continuation value.  
- **UART interface**: Streams results to host for comparison with C++ baselines.

---

## Baselines (C++)
- **Fixed‑point baseline** (`baseline/cpp_fixed/`):  
  - Implements a fixed-point workflow aligned with the FPGA-oriented arithmetic path.  
  - Validates numerical behavior and supports CPU timing comparisons.  

---

## Build & Run
### FPGA (Vivado)
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

### Current benchmark payload note
- The host script can decode an FPGA result payload marker (`0xABCD0001`) with `(price_raw, cycles_lo, cycles_hi)`.
- Placeholder result emission is disabled by default in `top_mc_option_pricer` to avoid misleading metrics.
- Connect real compute done/price signals in top-level integration to enable meaningful benchmark payloads.

### Next implementation steps (priority)
1. Integrate full pricing datapath in `src/top/top_option_pricer.sv` and wire real `result_price`.
2. Connect true pipeline-completion pulse to top-level `core_done` cycle-stop point.
3. Verify FPGA UART returns real `(marker, price, cycles_lo, cycles_hi)` packet.
4. Run benchmark mode with `src/uart_host.py` and report:
   - CPU runtime
   - FPGA core cycles and derived compute time (`--fpga-fclk-hz`)
   - price delta and speedup
5. Add live market mode verification (`--mode live --target cpu|fpga`) with logged input snapshot for repeatability.

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
- [x] Fixed‑point math library (fxMul, fxDiv, fxExpLUT, fxlnLUT, fxSqrt).  
- [x] Sobol generator.  
- [x] Inverse CDF (Step1 + Zelen–Severo).  
- [x] GBM step.  
- [x] Accumulator + Regression.  
- [x] LSM decision.  
- [x] C++ floating‑point baseline.  
- [x] C++ fixed‑point baseline.  
- [x] Top‑level integration with UART.  
- [ ] Lane replication (NUM_LANES > 4).  
- [x] Python host script for real‑time data fetch and FPGA/CPU timing comparison.  
:warning: Currently working on implementing some new features, so not everything works. 

---

## Contact
For questions or contributions, please open an issue or pull request.  

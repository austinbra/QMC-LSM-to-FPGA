# FPGA QMC‑LSMC American Option Pricer

## Overview
This project implements a **production‑grade, fully handshaked FPGA pipeline** for **American option pricing** using the **Longstaff–Schwartz Monte Carlo (LSMC)** method with **Quasi‑Monte Carlo (Sobol) sequences**.  
The design targets a **Xilinx Spartan‑7 FPGA** (Vivado flow) and is written in **SystemVerilog**.  

In addition to the FPGA implementation, the repository includes **C++ baselines**:
- A **floating‑point baseline** (using Boost libraries) for reference accuracy.  
- A **fixed‑point baseline** to match the FPGA’s Qm.n arithmetic and validate numerical trade‑offs.  

This allows direct comparison of **accuracy** and **performance** between CPU and FPGA implementations.

---

## Features
- **End‑to‑end pipeline**:  
  Sobol → Inverse CDF (Zelen–Severo rational approx) → GBM path simulation → Accumulator → Regression (Gaussian elimination) → LSM decision → UART output.
- **Fixed‑point math** (default Q16.16) with LUT‑based exp/ln/sqrt and Newton–Raphson refinement.
- **Fully handshaked ready/valid interfaces** with skid buffers and barrier synchronization for stall safety.
- **Mini‑batch accumulation**: accumulate regression sums across batches, run regression once, then sweep for path payoffs.
- **Lane replication ready**: top‑level parameter to scale throughput by instantiating multiple parallel pipelines.
- **Assertions** for handshake invariants and stall stability.
- **C++ baselines** (floating‑point and fixed‑point) for validation and performance comparison.

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
- **Floating‑point baseline**:  
  - Uses Boost libraries for Sobol sequence generation and inverse CDF.  
  - Provides high‑accuracy reference results.  
- **Fixed‑point baseline**:  
  - Implements the same Qm.n arithmetic as the FPGA.  
  - Validates numerical approximations and error bounds.  
- Both baselines are included in the repository and can be run on CPU for **accuracy checks** and **timing comparisons**.  

---

## Build & Run
### FPGA (Vivado)
1. Add all SystemVerilog sources and memory initialization files (`*.mem`) to a Vivado project.  
2. Generate the `fxDiv_core` IP (Xilinx `div_gen`) with parameters matching `fxDiv.sv`.  
3. Add a clock constraint (e.g., 100 MHz).  
4. Run behavioral simulation with provided testbenches.  
5. Synthesize and implement for Spartan‑7.  

### C++ Baselines
1. Build with a modern C++ compiler (C++17 or later).  
2. Floating‑point baseline requires Boost (for Sobol and statistical functions).  
3. Run with the same option parameters as the FPGA to compare results.  

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


---

## Contact
For questions or contributions, please open an issue or pull request.  

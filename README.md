# FPGA-Accelerated QMC + LSMC American Option Pricing Engine

## Overview

This project implements an American option pricer using the Least-Squares Monte Carlo (LSMC) approach with Quasi-Monte Carlo (QMC) Sobol sequences. The C++ prototype is fully quantized (fixed-point) to match later Verilog modules, enabling easy porting to FPGA platforms (Arty A7, PYNQ-Z2).

## Features

* **Fixed-Point C++ Prototype**: Uses Q9.23 format (32-bit) for all core arithmetic (stock price, normals, regression), ensuring bit-exact behavior when moved to hardware.
* **Sobol QMC Path Generation**: Leverages a Sobol generator for low-discrepancy sampling, mapped to standard normals via inverse-CDF and quantized to fixed-point.
* **LSMC Backward Induction**: Performs cross-sectional regression at each exercise date using a 3×3 fixed-point solver; compares immediate payoff vs. continuation.
* **Quantized Arithmetic Primitives**: Includes `fxMul`, `fxDiv`, `fxExp` (piecewise or LUT-based) for integer-only operations.
* **Verilog-Ready Modules**: Integer-based multipliers, adders, and shift operations mirror final FPGA pipelined datapath.

## Directory Structure

```
/ (root)
├── README.md               # This documentation
├── src/
│   ├── main.cpp            # Entry point, quantized LSMC workflow
│   ├── types.h             # Fixed-point typedefs and conversion helpers
│   ├── sobol_wrapper.h     # Sobol QMC interface (double → quantize)
│   ├── sobol_wrapper.cpp
│   ├── linalg.h            # Fixed-point 3×3 regression solver interface
│   ├── linalg.cpp          # Fixed-point Gaussian elimination
│   ├── pricing.h           # Pricing logic (simulate & backtrack)
│   ├── pricing.cpp
│   ├── utils.h             # Timer, argument parsing, fixed ↔ double
│   └── utils.cpp
├── verilog/                # Verilog modules for FPGA (Sobol, exp, reg-solver)
│   ├── sobol.v
│   ├── exp_approx.v
│   ├── regress3x3.v
│   └── top_pipeline.v      # Integration and control FSM
├── scripts/
│   ├── build.sh            # Compile C++ and run tests
│   └── sim.sh              # Launch Verilator simulation and compare to C++
└── docs/
    ├── FPGA_Integration.pdf # Timing/resource summary
    └── demo_results.csv     # Benchmark data (paths/sec, error)
```

## Requirements

* **C++17** compiler (e.g. g++ or clang++)
* **Boost.Math** (for `erf_inv`) or a local `erfinv` implementation
* **Verilator** (for Verilog simulation)
* **Vivado** (for synthesis on Arty A7 or PYNQ-Z2)
* **Make** or **CMake** for build scripts

## Building & Running C++ Prototype

```bash
# From project root:
cd src
bash ../scripts/build.sh
./lsmc_qmc --paths 100000 --steps 64 --S0 100.0 --K 100.0 --r 0.05 --sigma 0.2 --T 1.0
```

* `--paths N` : number of Monte Carlo paths (e.g. 100000)
* `--steps M` : number of time-steps/exercise dates (e.g. 64)
* `--S0`, `--K`, `--r`, `--sigma`, `--T`: option parameters

Example output:

```
Params: N=100000, M=64, S0=100, K=100, r=0.05, sigma=0.2, T=1
Simulation time:     0.45 s
Backward time:       1.20 s
Fixed-point price:   5.67
```

## Verilog Simulation & FPGA Synthesis

1. **Simulate Verilog modules** with Verilator:

   ```bash
   cd verilog
   bash ../scripts/sim.sh  # runs sobol, exp, regression testbenches
   ```
2. **Synthesize & Implement** on Arty A7 / PYNQ-Z2:

   ```bash
   vivado -mode batch -source synth.tcl  # reads Vivado project files
   ```
3. **Resource & Timing Reports** available in `docs/FPGA_Integration.pdf`.

## FPGA Integration Flow

1. **Sobol QMC Module** (`sobol.v`): produces 32-bit Sobol integer each cycle.
2. **Inverse-CDF Module** (`exp_approx.v`): LUT-based `fxExp`, `fxInvErf`, etc.
3. **GBM Pipeline**: fixed-point multiply, exp, multiply previous S to get new S.
4. **Path Storage**: on-chip BRAM for `M` steps per path.
5. **Backward FSM & Regression** (`regress3x3.v`): accumulators → 3×3 matrix solver.
6. **Control** (`top_pipeline.v`): sequences forward simulation, BRAM writes, backward pass, PV accumulation.

## Benchmark & Results

* **CPU (C++ reference)**: 64‑step LSMC, N=100k paths → 1.65 s, error \~0.3% vs. binomial.
* **FPGA (Arty A7 @100 MHz)**: 8‑pipeline latency per stage, 64‑step → \~2000 cycles/path → 50k paths/s.
* **Precision**: Q9.23 yields <0.1% pricing error compared to double‐precision.

## Contribution & License

* Contributions welcome: fork repository, submit pull requests.
* Licensed under MIT. See [LICENSE](LICENSE).

---

*For questions or demos, contact \[[your-email@example.com](mailto:your-email@example.com)]*

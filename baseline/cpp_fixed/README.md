# Fixed-Point C++ Baseline

This is the promoted CPU baseline used to compare against the FPGA SystemVerilog implementation.

## Purpose

- Numerical baseline for option price comparisons.
- CPU timing baseline for throughput/performance comparisons.
- Reference implementation for algorithm/debug sanity checks.

## Build and run (PowerShell + g++)

```powershell
g++ -std=c++17 main.cpp pricing.cpp linalg.cpp sobol_wrapper.cpp utils.cpp -o fixed_baseline
./fixed_baseline --paths 10000 --steps 50 --S0 100 --K 100 --r 0.05 --sigma 0.2 --T 1.0
```

### Boost Sobol build

```powershell
g++ -std=c++17 -DUSE_BOOST_SOBOL -I"<boost_include_path>" main.cpp pricing.cpp linalg.cpp sobol_wrapper.cpp utils.cpp -o fixed_baseline
```

PowerShell helper:

```powershell
./run_baseline.ps1 -UseBoost -BoostInclude "C:\path\to\boost"
```

### File-driven run

Input file format (`key=value`, one per line):

```text
paths=10000
steps=50
S0=100.0
K=100.0
r=0.05
sigma=0.2
T=1.0
```

Run:

```powershell
./fixed_baseline --input-file params.txt
```

Example file: `params_example.txt`

## Notes

- `USE_BOOST_SOBOL` enables Boost Sobol sequence generation.
- Without `USE_BOOST_SOBOL`, the code falls back to deterministic pseudo-random generation.
- For FPGA speed comparison, use FPGA core cycle counts (exclude UART transfer time), then compare with CPU runtime from this baseline.
- Unified benchmark/live runner is `src/uart_host.py` with selectable target: `cpu`, `fpga`, or `both`.

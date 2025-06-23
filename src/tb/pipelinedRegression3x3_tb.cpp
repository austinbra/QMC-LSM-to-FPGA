
// Drives one identity‐matrix solve through the pipeline and checks β=[1,2,3].

#include "VpipelinedRegression3x3.h"
#include "verilated.h"
#include <iostream>
#include <cassert>
#include <cmath>

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    auto *tb = new VpipelinedRegression3x3;

    // Constants must match your RTL parameters
    const int WIDTH   = 32;
    const int QINT    = 16;
    const double SCALE = double(1 << QINT);

    // Helpers to convert between real and Q16.16
    auto to_fixed = [&](double x) -> int32_t {
        return int32_t(std::round(x * SCALE));
    };
    auto to_real  = [&](int32_t x) -> double {
        return double(x) / SCALE;
    };

    // ------------------------------------------------------------------------
    // INITIALIZE
    // ------------------------------------------------------------------------
    tb->clk      = 0;
    tb->rst_n    = 0;
    tb->valid_in = 0;
    // zero out the arrays
    for (int i = 0; i < 9;  ++i) tb->A_flat[i] = 0;
    for (int i = 0; i < 3;  ++i) tb->B_flat[i] = 0;
    tb->eval();

    // ------------------------------------------------------------------------
    // RESET: hold rst_n low for 2 full cycles
    // ------------------------------------------------------------------------
    for (int cycle = 0; cycle < 4; ++cycle) {
        tb->clk = !tb->clk; tb->eval();
    }
    // release reset
    tb->rst_n = 1;
    tb->clk   = !tb->clk; tb->eval();
    tb->clk   = !tb->clk; tb->eval();

    // ------------------------------------------------------------------------
    // APPLY TEST VECTOR: A = I₃, B = [1,2,3] in Q16.16
    // ------------------------------------------------------------------------
    for (int i = 0; i < 9; ++i) {
        int row = i / 3, col = i % 3;
        tb->A_flat[i] = to_fixed(row == col ? 1.0 : 0.0);
    }
    for (int i = 0; i < 3; ++i) {
        tb->B_flat[i] = to_fixed(double(i + 1));
    }

    tb->eval();

    // ------------------------------------------------------------------------
    // PULSE valid_in for exactly one cycle
    // ------------------------------------------------------------------------
    tb->valid_in = 1;
    tb->clk      = !tb->clk; tb->eval();
    tb->clk      = !tb->clk; tb->eval();
    tb->valid_in = 0;

    // ------------------------------------------------------------------------
    // WAIT for valid_out (with timeout)
    // ------------------------------------------------------------------------
    const int MAX_CYCLES = 1000;
    int cycle = 0;
    while (!tb->valid_out && cycle < MAX_CYCLES) {
        tb->clk = !tb->clk; tb->eval();
        tb->clk = !tb->clk; tb->eval();
        ++cycle;
    }
    if (!tb->valid_out) {
        std::cerr << "ERROR: timed out waiting for valid_out\n";
        return 1;
    }

    // ------------------------------------------------------------------------
    // READ & CHECK β
    // ------------------------------------------------------------------------
    double b0 = to_real(int32_t(tb->beta[0]));
    double b1 = to_real(int32_t(tb->beta[1]));
    double b2 = to_real(int32_t(tb->beta[2]));

    std::cout << "Got beta = [" 
              << b0 << ", " << b1 << ", " << b2 << "]\n";

    // tolerance ±1 LSB
    assert(std::fabs(b0 - 1.0) < 1e-3);
    assert(std::fabs(b1 - 2.0) < 1e-3);
    assert(std::fabs(b2 - 3.0) < 1e-3);
    std::cout << "PASS\n";

    delete tb;
    return 0;
}

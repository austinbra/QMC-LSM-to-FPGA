// pipelinedRegression3x3_tb.cpp
#include "VpipelinedRegression3x3.h"
#include "verilated.h"
#include <iostream>
#include <cstdint>
#include <cassert>

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    auto *tb = new VpipelinedRegression3x3;

    const int WIDTH = 32;
    const int QINT  = 16;

    // Helper: convert real to Q16.16
    auto to_fixed = [&](double x) {
        return int32_t(x * (1<<QINT));
    };
    auto to_real  = [&](int32_t x) {
        return double(x) / (1<<QINT);
    };

    // INITIALIZE
    tb->clk      = 0;
    tb->rst_n    = 0;
    tb->valid_in = 0;
    for (int i = 0; i < 9; ++i) tb->A_flat[i] = 0;
    for (int i = 0; i < 3; ++i) tb->B_flat[i] = 0;
    tb->eval();

    // RESET: hold low for 2 cycles
    for (int i = 0; i < 4; ++i) {
        tb->clk = !tb->clk; tb->eval();
    }
    tb->rst_n = 1;  // release reset
    tb->clk   = !tb->clk; tb->eval();
    tb->clk   = !tb->clk; tb->eval();

    // APPLY TEST VECTOR: Identity A and B=[1,2,3]
    for (int i = 0; i < 9; ++i) {
        tb->A_flat[i] = to_fixed((i/3 == i%3) ? 1.0 : 0.0);
    }
    for (int i = 0; i < 3; ++i) {
        tb->B_flat[i] = to_fixed(double(i+1));
    }

    // PULSE valid_in for exactly one cycle
    tb->valid_in = 1;
    tb->clk      = !tb->clk; tb->eval();
    tb->clk      = !tb->clk; tb->eval();
    tb->valid_in = 0;

    // WAIT for valid_out
    const int MAX_CYCLES = 1000;
    int cycle = 0;
    while (!tb->valid_out && cycle < MAX_CYCLES) {
        tb->clk = !tb->clk; tb->eval();
        tb->clk = !tb->clk; tb->eval();
        ++cycle;
    }
    if (!tb->valid_out) {
        std::cerr << "FAIL: timed out waiting for valid_out\n";
        return 1;
    }

    // READ AND DISPLAY betas
    double b0 = to_real(int32_t(tb->beta[0]));
    double b1 = to_real(int32_t(tb->beta[1]));
    double b2 = to_real(int32_t(tb->beta[2]));
    std::cout << "beta = [" << b0 << ", " << b1 << ", " << b2 << "]\n";

    // CHECK against expected [1,2,3]
    assert(fabs(b0-1.0) < 1e-3);
    assert(fabs(b1-2.0) < 1e-3);
    assert(fabs(b2-3.0) < 1e-3);
    std::cout << "PASS\n";

    delete tb;
    return 0;
}

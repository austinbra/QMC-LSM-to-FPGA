// regression3x3_tb.cpp - Verilator C++ Testbench
#include "Vregression3x3.h"
#include "verilated.h"
#include <iostream>
#include <cstdint>

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    Vregression3x3* top = new Vregression3x3;

    // initialize
    top->clk = 0;
    top->rst_n = 0;
    top->start = 0;
    for (int i = 0; i < 9; ++i) top->A_flat[i] = 0;
    for (int i = 0; i < 3; ++i) top->B_flat[i] = 0;

    // reset sequence
    for (int cycle = 0; cycle < 2; ++cycle) {
        top->clk = !top->clk;
        top->eval();
    }
    top->rst_n = 1;
    top->eval();

    // load identity matrix A and B = [1,2,3] in Q16.16
    for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
            top->A_flat[i*3 + j] = (i == j ? (1 << 16) : 0);
        }
        top->B_flat[i] = ((i + 1) << 16);
    }

    // start operation
    top->start = 1;
    top->clk = !top->clk;
    top->eval();
    top->clk = !top->clk;
    top->eval();
    top->start = 0;

    // run until done or timeout
    const int MAX_CYCLES = 1000;
    int cycle_count = 0;
    while (!top->done && cycle_count < MAX_CYCLES) {
        top->clk = !top->clk;
        top->eval();
        top->clk = !top->clk;
        top->eval();
        ++cycle_count;
    }

    if (!top->done) {
        std::cerr << "ERROR: regression did not finish after " << MAX_CYCLES << " cycles\n";
        return 1;
    }

    // print results
    double beta0 = double(int32_t(top->beta[0])) / (1<<16);
    double beta1 = double(int32_t(top->beta[1])) / (1<<16);
    double beta2 = double(int32_t(top->beta[2])) / (1<<16);
    std::cout << "beta[0] = " << beta0 << "\n";
    std::cout << "beta[1] = " << beta1 << "\n";
    std::cout << "beta[2] = " << beta2 << "\n";

    delete top;
    return 0;
}

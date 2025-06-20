#include "VinverseCDF.h"
#include "verilated.h"
#include <iostream>
#include <iomanip>
#include <cmath>

// Q16.16 to float
double q16_16_to_float(int32_t val)
{
    return static_cast<double>(val) / (1 << 16);
}

int main(int argc, char **argv)
{
    Verilated::commandArgs(argc, argv);
    VinverseCDF *top = new VinverseCDF;

    // Test vectors (from earlier)
    int u_inputs[] = {655, 3277, 6554, 16384, 32768, 49152, 58982, 62259, 64881};
    int expected_z[] = {-152460, -107797, -83988, -44203, 0, 44203, 83988, 107797, 152460};
    const int num_tests = sizeof(u_inputs) / sizeof(u_inputs[0]);

    for (int test = 0; test < num_tests; ++test)
    {
        std::cout << "==== Test " << test << ": u_in = " << u_inputs[test] << " ====" << std::endl;

        // Reset
        top->clk = 0;
        top->rst_n = 0;
        top->eval();
        top->clk = 1;
        top->eval();
        top->rst_n = 1;

        // Apply input
        top->u_in = u_inputs[test];
        top->valid_in = 1;

        bool seen_output = false;
        int32_t z_result = 0;

        for (int cycle = 0; cycle < 50; ++cycle)
        {
            top->clk ^= 1;
            top->eval();

            // Drop valid_in after first cycle
            if (cycle == 1)
                top->valid_in = 0;

            if (top->valid_out && !seen_output)
            {
                seen_output = true;
                z_result = top->z_out;
            }
        }

        double z_float = q16_16_to_float(z_result);
        double expected_float = q16_16_to_float(expected_z[test]);
        double error = std::abs(z_float - expected_float);

        std::cout << std::fixed << std::setprecision(6);
        std::cout << "z_out (Q16.16) = " << z_result
                  << " → float = " << z_float << std::endl;
        std::cout << "expected       = " << expected_z[test]
                  << " → float = " << expected_float << std::endl;
        std::cout << "error          = " << error << "\n\n";

        if (error > 0.02)
        {
            std::cout << "❌ FAIL: Error exceeds tolerance\n";
        }
        else
        {
            std::cout << "✅ PASS\n";
        }
    }

    delete top;
    return 0;
}

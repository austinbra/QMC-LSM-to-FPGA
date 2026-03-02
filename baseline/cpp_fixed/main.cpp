#include "pricing.h"
#include "sobol_wrapper.h"
#include "types.h"
#include "utils.h"
#include <iostream>

int main(int argc, char *argv[])
{
    int N = N_DEFAULT;
    int M = M_DEFAULT;
    double S0_d = toDouble(S0_DEFAULT);
    double K_d = toDouble(K_DEFAULT);
    double r_d = toDouble(r_DEFAULT);
    double sigma_d = toDouble(sigma_DEFAULT);
    double T_d = toDouble(T_DEFAULT);

    if (!parseArgs(argc, argv, N, M, S0_d, K_d, r_d, sigma_d, T_d))
    {
        std::cerr << "Invalid arguments.\n";
        std::cerr << "Usage:\n"
                  << "  --input-file <path> Parameter file (key=value lines)\n"
                  << "  --paths   <int>     Number of simulated paths (e.g., 10000)\n"
                  << "  --steps   <int>     Number of time steps (e.g., 50)\n"
                  << "  --S0      <float>   Spot price (e.g., 100.0)\n"
                  << "  --K       <float>   Strike price (e.g., 100.0)\n"
                  << "  --r       <float>   Risk-free rate (e.g., 0.05)\n"
                  << "  --sigma   <float>   Volatility (e.g., 0.2)\n"
                  << "  --T       <float>   Time to maturity in years (e.g., 1.0)\n";
        return 1;
    }

    int32_t S0_q = toint32_t(S0_d);
    int32_t K_q = toint32_t(K_d);
    int32_t r_q = toint32_t(r_d);
    int32_t sigma_q = toint32_t(sigma_d);
    int32_t T_q = toint32_t(T_d);

    Timer timer;
    timer.reset();

    SobolGenerator sobol(M);
    std::vector<Path> paths(N, Path(M));
    simulatePaths(N, M, S0_q, r_q, sigma_q, T_q, sobol, paths);

    int32_t price_q;
    backwardInduction(N, M, r_q, T_q, K_q, paths, price_q);

    double price_d = toDouble(price_q);
    double elapsed = timer.elapsed();

    std::cout << "Estimated Option Price (Q16.16): " << price_q << "\n";
    std::cout << "Estimated Option Price (double): " << price_d << "\n";
    std::cout << "Elapsed Time: " << elapsed << " seconds\n";
    return 0;
}

#include "pricing.h"
#include "sobol_wrapper.h"
#include "types.h"
#include "utils.h"
#include <iostream>

int main(int argc, char *argv[])
{

    // initialize parameters with default values from types.h
    int N = N_DEFAULT;          // number of paths
    int M = M_DEFAULT;          // number of time steps
    int32_t S0 = S0_DEFAULT;       // spot price
    int32_t K = K_DEFAULT;         // strike price
    int32_t r = r_DEFAULT;         // risk-free rate
    int32_t sigma = sigma_DEFAULT; // volatility
    int32_t T = T_DEFAULT;

    // 2) Compute dt = T / M in Q9.23
    int32_t M_q   = toint32_t(double(M));
    int32_t dt    = fxDiv(T, M_q);

    // check for proper usage
    if (!parseArgs(argc, argv, N, M, S0, K, r, sigma, T))
    {
        std::cerr << "Invalid arguments.\n";
        std::cerr << "Usage:\n"
                  << "  --paths   <int>     Number of simulated paths (e.g., 10000)\n"
                  << "  --steps   <int>     Number of time steps (e.g., 50)\n"
                  << "  --S0      <float>   Spot price (e.g., 100.0)\n"
                  << "  --K       <float>   Strike price (e.g., 100.0)\n"
                  << "  --r       <float>   Risk-free rate (e.g., 0.05)\n"
                  << "  --sigma   <float>   Volatility (e.g., 0.2)\n"
                  << "  --T       <float>   Time to maturity in years (e.g., 1.0)\n";
        return 1;
    }

    // start timer to test simulation speed
    Timer timer;
    timer.reset();

    // create sobol generator
    SobolGenerator sobol(M);

    // generate paths using QMC Sobol and GBM
    std::vector<Path> paths(N, Path(M));
    simulatePaths(N, M, S0, r, sigma, T, sobol, paths);

    // perform LSM regression to compute price
    int32_t price;
    backwardInduction(N, M, r, T, K, paths, price);

    double price_d = toDouble(price);//back to 32


    // get time simulation took
    double elapsed = timer.elapsed();

    std::cout << "Estimated Option Price: " << price << "\n";
    std::cout << "Elapsed Time: " << elapsed << " seconds\n";
}

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
    Real S0 = S0_DEFAULT;       // spot price
    Real K = K_DEFAULT;         // strike price
    Real r = r_DEFAULT;         // risk-free rate
    Real sigma = sigma_DEFAULT; // volatility
    Real T = T_DEFAULT;

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

    // create sobol generator
    SobolGenerator sobol(M);
}

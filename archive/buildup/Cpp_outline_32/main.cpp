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
    double S0_d = S0_DEFAULT;       // spot price
    double K_d = K_DEFAULT;         // strike price
    double r_d = r_DEFAULT;         // risk-free rate
    double sigma_d = sigma_DEFAULT; // volatility
    double T_d = T_DEFAULT;

    

    // check for proper usage
    if (!parseArgs(argc, argv, N, M, S0_d, K_d, r_d, sigma_d, T_d))
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
    

    int32_t S0_q= toint32_t(S0_d);
    int32_t K_q = toint32_t(K_d);
    int32_t r_q = toint32_t(r_d);
    int32_t sigma_q = toint32_t(sigma_d);
    int32_t T_q = toint32_t(T_d);

    // Compute dt = T / M in Q9.23
    int32_t M_q = toint32_t(double(M));
    int32_t dt = fxDiv(T_q, M_q);



    // start timer to test simulation speed
    Timer timer;
    timer.reset();

    // create sobol generator
    SobolGenerator sobol(M);

    // generate paths using QMC Sobol and GBM
    std::vector<Path> paths(N, Path(M));
    simulatePaths(N, M, S0_q, r_q, sigma_q, T_q, sobol, paths);

    // perform LSM regression to compute price
    int32_t price_q;
    backwardInduction(N, M, r_q, T_q, K_q, paths, price_q);

    double price_d = toDouble(price_q);//back to 32


    // get time simulation took
    double elapsed = timer.elapsed();

    std::cout << "Estimated Option Price: " << price_q << "\n";
    std::cout << "Elapsed Time: " << elapsed << " seconds\n";
}

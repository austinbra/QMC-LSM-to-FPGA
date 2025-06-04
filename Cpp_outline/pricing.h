#ifndef PRICING_H
#define PRICING_H

#include <vector>
#include "types.h"
#include "sobol_wrapper.h"

struct Path {
    std::vector<Real> S;        // Asset prices at different time steps, length M+1
    std::vector<Real> cashflow; // Payouts at different time steps, length M+1
    Path(int M) : S(M+1), cashflow(M+1, 0.0){}
};

// Forward‐simulation using QMC Sobol
void simulatePaths(
    int N, int M,
    Real S0, Real r, Real sigma, Real T,
    SobolGenerator& sobol,
    std::vector<Path>& outPaths
);

// Backward‐induction and final pricing
void backwardInduction(
    int N, int M,
    Real r, Real T, Real K,
    std::vector<Path>& paths,
    Real& price_out
);

#endif

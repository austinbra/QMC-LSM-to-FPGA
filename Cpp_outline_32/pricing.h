#ifndef PRICING_H
#define PRICING_H

#include <vector>
#include "types.h"
#include "sobol_wrapper.h"

struct Path {
    std::vector<int32_t> S;        // length M+1
    std::vector<int32_t> cashflow; // length M+1
    Path(int M) : S(M+1), cashflow(M+1, 0.0) {}
};

// Forward‐simulation using QMC Sobol
void simulatePaths(
    int N, int M,
    int32_t S0, int32_t r, int32_t sigma, int32_t T,
    SobolGenerator& sobol,
    std::vector<Path>& outPaths
);

//max(S - K, 0), both Q11.21
inline int32_t compareint32_t(int32_t S, int32_t K) {
    return (S > K ? fxSub(S, K) : int32_t(0));
}

// Backward‐induction and final pricing
void backwardInduction(
    int N, int M,
    int32_t r, int32_t T, int32_t K,
    std::vector<Path>& paths,
    int32_t& price_out
);

#endif

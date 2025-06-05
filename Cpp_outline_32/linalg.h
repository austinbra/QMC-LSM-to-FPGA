#ifndef LINALG_H
#define LINALG_H

#include <vector>
#include "types.h"

// Solve Y ≈ β₀ + β₁ X + β₂ X² using 3×3 normal equations.
void solveRegression3x3(const std::vector<int32_t>& X, const std::vector<int32_t>& Y, int32_t beta_out[3]);

#endif

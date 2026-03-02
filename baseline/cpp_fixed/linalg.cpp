#include "linalg.h"
#include <cassert>
#include <cmath>
#include <iostream>

static void solve3x3System(const double A_in[3][3], const double B_in[3], double beta[3]) {
    double aug[3][4];
    for (int i = 0; i < 3; ++i) {
        aug[i][0] = A_in[i][0];
        aug[i][1] = A_in[i][1];
        aug[i][2] = A_in[i][2];
        aug[i][3] = B_in[i];
    }

    for (int pivot = 0; pivot < 3; ++pivot) {
        int best_row = pivot;
        double best_val = std::fabs(aug[pivot][pivot]);
        for (int r = pivot + 1; r < 3; ++r) {
            double val = std::fabs(aug[r][pivot]);
            if (val > best_val) {
                best_val = val;
                best_row = r;
            }
        }
        if (best_val < 1e-12) {
            std::cerr << "solve3x3System: pivot too small or det = 0.\n";
            return;
        }

        if (best_row != pivot) {
            for (int c = pivot; c < 4; ++c) std::swap(aug[pivot][c], aug[best_row][c]);
        }

        double diag = aug[pivot][pivot];
        for (int c = pivot; c < 4; ++c) aug[pivot][c] /= diag;

        for (int r = pivot + 1; r < 3; ++r) {
            double factor = aug[r][pivot];
            if (std::fabs(factor) < 1e-12) continue;
            for (int c = pivot; c < 4; ++c) aug[r][c] -= factor * aug[pivot][c];
        }
    }

    for (int r = 2; r >= 0; --r) {
        double value = aug[r][3];
        for (int c = r + 1; c < 3; ++c) value -= aug[r][c] * beta[c];
        beta[r] = value;
    }
}

void solveRegression3x3(const std::vector<int32_t>& X, const std::vector<int32_t>& Y, int32_t beta_out[3]) {
    int n = static_cast<int>(X.size());
    assert(n == static_cast<int>(Y.size()));

    int64_t s0 = 0, s1 = 0, s2 = 0, s3 = 0, s4 = 0;
    int64_t sy = 0, sxy = 0, sx2y = 0;

    for (int i = 0; i < n; ++i) {
        int32_t x = X[i];
        int32_t y = Y[i];
        int32_t x2 = fxMul(x, x);
        int32_t x3 = fxMul(x2, x);
        int32_t x4 = fxMul(x2, x2);
        int32_t xy = fxMul(x, y);
        int32_t x2y = fxMul(x2, y);
        s0 += ONE; s1 += x; s2 += x2; s3 += x3; s4 += x4;
        sy += y; sxy += xy; sx2y += x2y;
    }

    double A[3][3] = {
        {toDouble((int32_t)s0), toDouble((int32_t)s1), toDouble((int32_t)s2)},
        {toDouble((int32_t)s1), toDouble((int32_t)s2), toDouble((int32_t)s3)},
        {toDouble((int32_t)s2), toDouble((int32_t)s3), toDouble((int32_t)s4)}
    };
    double B[3] = {
        toDouble((int32_t)sy),
        toDouble((int32_t)sxy),
        toDouble((int32_t)sx2y)
    };

    double beta_d[3] = {0.0, 0.0, 0.0};
    solve3x3System(A, B, beta_d);
    beta_out[0] = toint32_t(beta_d[0]);
    beta_out[1] = toint32_t(beta_d[1]);
    beta_out[2] = toint32_t(beta_d[2]);
}

#include "linalg.h"
#include <cassert>
#include <iostream>
#include <vector>
#include <cmath>
#include <iomanip>

//starting with a 3x3, can talk about doing a 4x4 for more accurate maybe but more work

//helper- solve a 3×3 linear system A β = B by Gaussian‐elimination
//The result is placed in beta[].

static void solve3x3System(const Real A_in[3][3], const Real B_in[3], Real beta[3]){
    // Copy into a 3×4 matrix "aug", where
    //   aug[i][0..2] = A_in[i][0..2]
    //   aug[i][3]    = B_in[i]
    Real aug[3][4];
    for (int i = 0; i < 3; ++i){
        aug[i][0] = A_in[i][0];
        aug[i][1] = A_in[i][1];
        aug[i][2] = A_in[i][2];
        aug[i][3] = B_in[i];
    }

    for (int pivot = 0; pivot < 3; ++pivot){
        //1) find the best row to pivot (largest absolute value in column)
        int best_row = pivot;
        Real best_val = std::fabs(aug[pivot][pivot]);
        for (int r = pivot + 1; r < 3; ++r){
            Real val = std::fabs(aug[r][pivot]);
            if (val > best_val){
                best_val = val;
                best_row = r;
            }
        }
        if (best_val < 1e-12){
            std::cerr << "solve3x3System: pivot too small or det = 0.\n";
            return;
        }

        //2) swap the best row with the current pivot row
        if (best_row != pivot) {
            for (int c = pivot; c < 4; ++c){
                std::swap(aug[pivot][c], aug[best_row][c]);
            }
        }

        //3) Normalize pivot row so that aug[pivot][pivot] == 1
        Real diag = aug[pivot][pivot];
        for (int c = pivot; c < 4; ++c){
            aug[pivot][c] /= diag;
        }

        //4) get rid of everything below the num
        for (int r = pivot + 1; r < 3; ++r){
            Real factor = aug[r][pivot];
            
            if (std::fabs(factor) < 1e-12) continue;

            for (int c = pivot; c < 4; ++c){
                aug[r][c] -= factor * aug[pivot][c];
            }
        }
    }

    //back‐substitution: now aug is all 1s on the diag
    for (int r = 2; r >= 0; --r){
        Real value = aug[r][3]; // the rightmost column
        for (int c = r + 1; c < 3; ++c){
            value -= aug[r][c] * beta[c];
        }
        beta[r] = value;
    }
}

//kind of main
void solveRegression3x3(const std::vector<Real>& X, const std::vector<Real>& Y, Real beta_out[3]){
    int n = (int)X.size();
    assert(n == (int)Y.size());
    Real A[3][3] = {{0,0,0},{0,0,0},{0,0,0}};
    Real Bvec[3]  = {0,0,0};

    //make A and Bvec
    for (int i = 0; i < n; ++i){
        Real x = X[i];
        Real y = Y[i];
        Real b0 = 1.0;
        Real b1 = x;
        Real b2 = x * x;

        A[0][0] += b0 * b0; // = n if we use all X, but here only in‐the‐money
        A[0][1] += b0 * b1;
        A[0][2] += b0 * b2;
        A[1][0] += b1 * b0;
        A[1][1] += b1 * b1;
        A[1][2] += b1 * b2;
        A[2][0] += b2 * b0;
        A[2][1] += b2 * b1;
        A[2][2] += b2 * b2;

        Bvec[0] += b0 * y;
        Bvec[1] += b1 * y;
        Bvec[2] += b2 * y;
    }
    solve3x3System(A, Bvec, beta_out);
}

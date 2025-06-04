#include "linalg.h"
#include <cassert>

//starting with a 3x3, can talk about doing a 4x4 for more accurate maybe but more work

// Helper: solve a 3×3 linear system A β = B via Gaussian elimination:
static void solve3x3System(const Real A[3][3], const Real B[3], Real beta[3]){
    
    Real temp[3][5];
    for (int i = 0; i < 4; ++i){
        int p = i;
        if (i-3 >= 0) p -= 3;
        temp[i][0] = A[p][0];
        temp[i][1] = A[p][1];
        temp[i][2] = A[p][2];
    }
    Real det = 0;
    for (int i = 0; i < 2; ++i){
        det += temp[i][0]*temp[i+1][1]*temp[i+2][2];
        det -= temp[4-i][0]*temp[3-i][1]*temp[2-i][2];
    }

    Real M[3][3];
    for (int i = 0; i < 2; ++i){
        M[i][0] = A[i][0] / det;
        M[i][1] = A[i][1] / det;
        M[i][2] = A[i][2] / det;
    }




}

void solveRegression3x3(const std::vector<Real>& X, const std::vector<Real>& Y,Real beta_out[3]){
    int n = X.size();

    assert(n == Y.size()); //jic

    Real A[3][3] = {{0}};
    Real Bvec[3]  = {0,0,0};

    for (int i = 0; i < n; ++i) {
        Real x = X[i];
        Real y = Y[i];
        Real b0 = 1.0;
        Real b1 = x;
        Real b2 = x*x;

        A[0][0] += b0*b0;
        A[0][1] += b0*b1;
        A[0][2] += b0*b2;
        A[1][0] += b1*b0;
        A[1][1] += b1*b1;
        A[1][2] += b1*b2;
        A[2][0] += b2*b0;
        A[2][1] += b2*b1;
        A[2][2] += b2*b2;
        Bvec[0]  += b0 * y;
        Bvec[1]  += b1 * y;
        Bvec[2]  += b2 * y;
    }
    solve3x3System(A, Bvec, beta_out);
}

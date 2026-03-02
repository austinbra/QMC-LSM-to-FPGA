#include "pricing.h"
#include "linalg.h"
#include <cmath>
#include <algorithm>

static double inverseNormalCDF(double p) {
    static const double a1 = -3.969683028665376e+01;
    static const double a2 =  2.209460984245205e+02;
    static const double a3 = -2.759285104469687e+02;
    static const double a4 =  1.383577518672690e+02;
    static const double a5 = -3.066479806614716e+01;
    static const double a6 =  2.506628277459239e+00;
    static const double b1 = -5.447609879822406e+01;
    static const double b2 =  1.615858368580409e+02;
    static const double b3 = -1.556989798598866e+02;
    static const double b4 =  6.680131188771972e+01;
    static const double b5 = -1.328068155288572e+01;
    static const double c1 = -7.784894002430293e-03;
    static const double c2 = -3.223964580411365e-01;
    static const double c3 = -2.400758277161838e+00;
    static const double c4 = -2.549732539343734e+00;
    static const double c5 =  4.374664141464968e+00;
    static const double c6 =  2.938163982698783e+00;
    static const double d1 =  7.784695709041462e-03;
    static const double d2 =  3.224671290700398e-01;
    static const double d3 =  2.445134137142996e+00;
    static const double d4 =  3.754408661907416e+00;
    const double plow = 0.02425;
    const double phigh = 1.0 - plow;
    double q, r;

    p = std::clamp(p, 1e-12, 1.0 - 1e-12);
    if (p < plow) {
        q = std::sqrt(-2.0 * std::log(p));
        return (((((c1*q + c2)*q + c3)*q + c4)*q + c5)*q + c6) /
               ((((d1*q + d2)*q + d3)*q + d4)*q + 1.0);
    }
    if (p > phigh) {
        q = std::sqrt(-2.0 * std::log(1.0 - p));
        return -(((((c1*q + c2)*q + c3)*q + c4)*q + c5)*q + c6) /
                 ((((d1*q + d2)*q + d3)*q + d4)*q + 1.0);
    }
    q = p - 0.5;
    r = q * q;
    return (((((a1*r + a2)*r + a3)*r + a4)*r + a5)*r + a6) * q /
           (((((b1*r + b2)*r + b3)*r + b4)*r + b5)*r + 1.0);
}

inline int32_t compare(int32_t S, int32_t K) {
    return (S > K ? S - K : 0);
}

void simulatePaths(int N, int M, int32_t S0, int32_t r, int32_t sigma, int32_t T, SobolGenerator& sobol, std::vector<Path>& outPaths) {
    int32_t M_q = toint32_t(static_cast<double>(M));
    int32_t dt = fxDiv(T, M_q);
    int32_t half = toint32_t(0.5);
    int32_t sigma_sq = fxMul(sigma, sigma);
    int32_t half_sigma_sq = fxMul(half, sigma_sq);
    int32_t r_minus_half_sq = fxSub(r, half_sigma_sq);
    int32_t drift = fxMul(r_minus_half_sq, dt);
    double dt_d = toDouble(dt);
    double diff_coef_d = toDouble(sigma) * std::sqrt(dt_d);
    int32_t diff_coef = toint32_t(diff_coef_d);

    for (int i = 0; i < N; ++i) {
        outPaths[i].S[0] = S0;
        std::vector<Real> u = sobol.nextPoint();
        for (int j = 1; j <= M; ++j) {
            Real zd = inverseNormalCDF(u[j - 1]);
            int32_t Z = toint32_t(zd);
            int32_t term = fxMul(diff_coef, Z);
            int32_t exponent = fxAdd(drift, term);
            int32_t exp_fixed = fxExp(exponent);
            outPaths[i].S[j] = fxMul(outPaths[i].S[j - 1], exp_fixed);
        }
    }
}

void backwardInduction(int N, int M, int32_t r, int32_t T, int32_t K, std::vector<Path>& paths, int32_t& price_out) {
    int32_t M_q = toint32_t(static_cast<double>(M));
    int32_t dt = fxDiv(T, M_q);
    int32_t neg_r = fxSub(toint32_t(0.0), r);
    int32_t arg0 = fxMul(neg_r, dt);
    int32_t discount = fxExp(arg0);
    std::vector<int32_t> immediate(N), continuation(N);

    for (int i = 0; i < N; i++) {
        paths[i].cashflow[M] = compare(paths[i].S[M], K);
    }

    for (int j = M - 1; j > 0; --j) {
        std::vector<int> itm_indexes;
        itm_indexes.reserve(N);
        for (int i = 0; i < N; i++) {
            int32_t Sij = paths[i].S[j];
            immediate[i] = compare(Sij, K);
            continuation[i] = fxMul(discount, paths[i].cashflow[j + 1]);
            if (immediate[i] > 0) itm_indexes.push_back(i);
        }

        if (!itm_indexes.empty()) {
            std::vector<int32_t> X, Y;
            X.reserve(itm_indexes.size());
            Y.reserve(itm_indexes.size());
            for (int idx : itm_indexes) {
                X.push_back(paths[idx].S[j]);
                Y.push_back(continuation[idx]);
            }
            int32_t beta[3];
            solveRegression3x3(X, Y, beta);

            for (int i = 0; i < N; ++i) {
                if (immediate[i] == 0) {
                    paths[i].cashflow[j] = continuation[i];
                } else {
                    int32_t Sij = paths[i].S[j];
                    int32_t term1 = fxMul(beta[1], Sij);
                    int32_t term2 = fxMul(beta[2], fxMul(Sij, Sij));
                    int32_t cont_est = fxAdd(fxAdd(beta[0], term1), term2);
                    paths[i].cashflow[j] = (immediate[i] >= cont_est) ? immediate[i] : continuation[i];
                }
            }
        } else {
            for (int i = 0; i < N; ++i) paths[i].cashflow[j] = continuation[i];
        }
    }

    int64_t sumPV = 0;
    for (int i = 0; i < N; ++i) {
        int exercise_t = M;
        for (int j = 1; j <= M; ++j) {
            int32_t pay = compare(paths[i].S[j], K);
            if (pay > 0 && paths[i].cashflow[j] == pay) {
                exercise_t = j;
                break;
            }
        }
        int32_t tau = toint32_t(static_cast<double>(exercise_t));
        int32_t time_arg = fxMul(r, fxMul(tau, dt));
        int32_t df_tau = fxExp(fxSub(toint32_t(0.0), time_arg));
        int32_t pv_i = fxMul(paths[i].cashflow[exercise_t], df_tau);
        sumPV += static_cast<int64_t>(pv_i);
    }
    price_out = static_cast<int32_t>(sumPV / N);
}

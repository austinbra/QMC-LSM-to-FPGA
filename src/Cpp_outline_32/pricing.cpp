#include "pricing.h"
#include "linalg.h"
#include <cmath>
#include <cassert>
#include <boost/math/distributions/normal.hpp>

inline int32_t compare(int32_t S, int32_t K)
{
    return (S > K ? S - K : 0.0);
}

void simulatePaths(int N, int M, int32_t S0, int32_t r, int32_t sigma, int32_t T, SobolGenerator &sobol, std::vector<Path> &outPaths)
{
    // dt = T / M  in Q9.23
    int32_t M = toint32_t(static_cast<double>(M));
    int32_t dt = fxDiv(T, M);


    // drift = (r - 0.5 * sigma^2) * dt
    int32_t half = toint32_t(0.5);
    int32_t sigma_sq = fxMul(sigma, sigma);
    int32_t half_sigma_sq = fxMul(half, sigma_sq);
    int32_t r_minus_half_sq = fxSub(r, half_sigma_sq);
    int32_t drift = fxMul(r_minus_half_sq, dt);


    // diff_coef = sigma * sqrt(dt) ; compute sqrt(dt) in double then quantize
    double dt_d = toDouble(dt);
    double diff_coef_d = toDouble(sigma) * std::sqrt(dt_d);
    int32_t diff_coef = toint32_t(diff_coef_d);
    
    for (int i = 0; i < N; ++i)
    {
        outPaths[i].S[0] = S0;                   // initial price
        std::vector<Real> u = sobol.nextPoint(); // sobol run through boost
        for (int j = 1; j <= M; ++j)
        {
            Real ud = u[j-1];
            Real zd = boost::math::quantile(boost::math::normal_distribution<>(0.0, 1.0), ud);

            int32_t Z = toint32_t(zd);
            int32_t term = fxMul(diff_coef, Z);
            int32_t exponent = fxAdd(drift, term);//longstaff shwartz equaiton
            int32_t exp_int32_t = fxExp(exponent);
            outPaths[i].S[j] = fxMul(outPaths[i].S[j-1], exp_int32_t);
        }

    }
}

void backwardInduction(int N, int M, int32_t r, int32_t T, int32_t K, std::vector<Path> &paths, int32_t &price_out)
{
    // dt = T / M
    int32_t M = toint32_t(static_cast<double>(M)); 
    int32_t dt = fxDiv(T, M);

    // discount for one step: df = exp(-r * dt)
    int32_t neg_r = fxSub(toint32_t(0.0), r);
    int32_t arg0 = fxMul(neg_r, dt);
    int32_t discount = fxExp(arg0);

    std::vector<int32_t> immediate(N), continuation(N);

    for (int i = 0; i < N; i++)
    {
        paths[i].cashflow[M] = compare(paths[i].S[M], K);
    }

    for (int j = M - 1; j > 0; --j)
    {
        std::vector<int> itm_indexs;
        itm_indexs.reserve(N); // max

        for (int i = 0; i < N; i++)
        {
            int32_t Sij = paths[i].S[j];
            immediate[i] = compare(Sij, K);
            // Discounted continuation for each next step
            continuation[i] = fxMul(discount, paths[i].cashflow[j+1]);
            if (immediate[i] > 0.0)
            {
                itm_indexs.push_back(i);
            }
        }

        if (!itm_indexs.empty())
        {
            // get X and Y for in-the-money paths
            std::vector<int32_t> X, Y;
            X.reserve(itm_indexs.size()); // max
            Y.reserve(itm_indexs.size()); // max

            for (int idx : itm_indexs)
            {
                X.push_back(paths[idx].S[j]);
                Y.push_back(continuation[idx]);
            }
            int32_t beta[3];
            solveRegression3x3(X, Y, beta);
            for (int i = 0; i < N; ++i)
            {
                if (immediate[i] == 0.0)
                { // payoff is otm, so we automatically continue
                    paths[i].cashflow[j] = continuation[i];
                }
                else
                {
                    int32_t Sij = paths[i].S[j];
                    // cont_est = β0 + β1*S + β2*S^2
                    int32_t term1 = fxMul(beta[1], Sij);      
                    int32_t term2 = fxMul(beta[2], fxMul(Sij,Sij));
                    int32_t cont_est = fxAdd(fxAdd(beta[0], term1), term2);

                    if (immediate[i] >= cont_est) {
                        paths[i].cashflow[j] = immediate[i];
                    } else {
                        paths[i].cashflow[j] = continuation[i];
                    }
                }
            }
        }
        else
        {
            // No paths itm so auto continue
            for (int i = 0; i < N; ++i)
            {
                paths[i].cashflow[j] = continuation[i];
            }
        }
    }
    // final price using disounted cash flow

    int32_t sumPV = 0;
    for (int i = 0; i < N; ++i)
    {
        // find exercise time where cashflow[j] == payoff(S[j])
        // find the first j >= 1 where path should be exercised
        int exercise_T = M;
        for (int j = 1; j <= M; ++j)
        {
            int32_t pay = compare(paths[i].S[j], K);
            if (pay > 0.0 && paths[i].cashflow[j] == pay)
            {
                exercise_T = j;
                break;
            }
        }
        //discount = exp(-r * tau * dt)
        int32_t tau = toint32_t(static_cast<double>(tau));
        int32_t time_arg = fxMul(r, fxMul(tau, dt)); // r*τ*dt
        int32_t neg_time_arg = fxSub(toint32_t(0.0), time_arg);
        int32_t df_tau = fxExp(neg_time_arg);

        //PV_i = cashflow[tau] * df_tau
        int32_t pv_i = fxMul(paths[i].cashflow[tau], df_tau);

        // accumulate
        sumPV += static_cast<int64_t>(pv_i);
    }
    int64_t avg = sumPV / N;
    price_out = static_cast<int32_t>(avg);
}
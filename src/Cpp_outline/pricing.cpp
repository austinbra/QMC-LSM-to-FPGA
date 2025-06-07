#include "pricing.h"
#include "linalg.h"
#include <cmath>
#include <cassert>
#include <boost/math/distributions/normal.hpp>

inline Real compare(Real S, Real K)
{
    return (S > K ? S - K : 0.0);
}

void simulatePaths(int N, int M, Real S0, Real r, Real sigma, Real T, SobolGenerator &sobol, std::vector<Path> &outPaths)
{
    Real dt = T / M;
    Real drift = (r - 0.5 * sigma * sigma) * dt;
    Real diff_coef = sigma * std::sqrt(dt);
    for (int i = 0; i < N; ++i)
    {
        outPaths[i].S[0] = S0;                   // initial price
        std::vector<Real> u = sobol.nextPoint(); // sobol run through boost
        for (int j = 1; j <= M; ++j)
        {
            Real uval = std::min(std::max(u[j - 1], 1e-10), 1.0 - 1e-10);
            Real Z = boost::math::erf_inv(2 * uval - 1) * sqrt(2);
            outPaths[i].S[j] = outPaths[i].S[j - 1] * std::exp(drift + diff_coef * Z); // longstaff shwartz equation
        }
    }
}

void backwardInduction(int N, int M, Real r, Real T, Real K, std::vector<Path> &paths, Real &price_out)
{
    Real dt = T / M;
    Real discount = std::exp(-r * dt);
    std::vector<Real> immediate(N), continuation(N);

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
            Real Sij = paths[i].S[j];
            immediate[i] = compare(Sij, K);
            // Discounted continuation for each next step
            continuation[i] = discount * paths[i].cashflow[j + 1];
            if (immediate[i] > 0.0)
            {
                itm_indexs.push_back(i);
            }
        }

        if (!itm_indexs.empty())
        {
            // get X and Y for in-the-money paths
            std::vector<Real> X, Y;
            X.reserve(itm_indexs.size()); // max
            Y.reserve(itm_indexs.size()); // max

            for (int idx : itm_indexs)
            {
                X.push_back(paths[idx].S[j]);
                Y.push_back(continuation[idx]);
            }
            Real beta[3];
            solveRegression3x3(X, Y, beta);
            for (int i = 0; i < N; ++i)
            {
                if (immediate[i] == 0.0)
                { // payoff is otm, so we automatically continue
                    paths[i].cashflow[j] = continuation[i];
                }
                else
                {
                    Real Sij = paths[i].S[j];
                    Real continuation_est = beta[0] + beta[1] * Sij + beta[2] * Sij * Sij;
                    if (immediate[i] >= continuation_est)
                    {
                        paths[i].cashflow[j] = immediate[i]; // check which is better and add to cashflow in that index for that path
                    }
                    else
                    {
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

    Real sumPV = 0.0;
    for (int i = 0; i < N; ++i)
    {
        // find exercise time where cashflow[j] == payoff(S[j])
        // find the first j >= 1 where path should be exercised
        int exercise_T = M;
        for (int j = 1; j <= M; ++j)
        {
            Real pay = compare(paths[i].S[j], K);
            if (pay > 0.0 && paths[i].cashflow[j] == pay)
            {
                exercise_T = j;
                break;
            }
        }
        Real chosen_T = exercise_T * dt; // temp to check w/ test case
        sumPV += paths[i].cashflow[exercise_T] * std::exp(-r * chosen_T);
    }
    price_out = sumPV / static_cast<Real>(N);
}
#ifndef TYPES_H
#define TYPES_H

#include <cstdint>
#include <cmath>
#include <cassert>

//  Q11.21
//  1 sign bit, 10 integer bits, 21 fractional bits → 32‐bit signed

constexpr int   FRAC_BITS = 21;           // number of fractional bits
constexpr int32_t ONE = 1 << FRAC_BITS;   // “1.0” in Q11.21

using Real = double;


// Convert a (double) to Q11.21
inline int32_t toint32_t(double x){
    double maxRep = static_cast<double>((1 << (31 - FRAC_BITS)) - 1);  // 1024
    double minRep = -static_cast<double>(1 << (31 - FRAC_BITS));       // -1024
    if (x > maxRep) x = maxRep;
    if (x < minRep) x = minRep;
    return static_cast<int32_t>(std::llround(x * ONE));//reduce tiny rounding errors
}

// Convert Q11.21 back to double (for printing/debug)
inline double toDouble(int32_t x){
    return static_cast<double>(x) / ONE;
}

// int32_t‐point addition / subtraction
inline int32_t fxAdd(int32_t a, int32_t b){
    return static_cast<int32_t>(a + b);
}
inline int32_t fxSub(int32_t a, int32_t b){
    return static_cast<int32_t>(a - b);
}

// int32_t‐point multiplication: (Q11.21 × Q11.21 = Q11.21)
inline int32_t fxMul(int32_t a, int32_t b){
    // add space with 64‐bit, multiply, then round and shift right by FRAC_BITS
    int64_t prod = static_cast<int64_t>(a) * static_cast<int64_t>(b);
    prod += (int64_t(1) << (FRAC_BITS - 1));
    return static_cast<int32_t>(prod >> FRAC_BITS);
}

// int32_t‐point division: (Q11.21 / Q11.21 = Q11.21)
inline int32_t fxDiv(int32_t a, int32_t b){
    assert(b != 0);//check
    //promote to 64 bits: (a << FRAC_BITS) / b
    int64_t num = (static_cast<int64_t>(a) << FRAC_BITS);
    int64_t half_b = (b > 0 ? b : -b) / 2;

    if (num >= 0) num += half_b;
    else num -= half_b;
    return static_cast<int32_t>(num / b);
}

// Placeholder for exp(x) in Q11.21 → Q11.21.
// Replace this with a LUT or polynomial approximation to stay integer‐only.
inline int32_t fxExp(int32_t x) {
    double xd = toDouble(x);
    double ed = std::exp(xd);
    return toint32_t(ed);
}





constexpr int   N_DEFAULT = 10000;
constexpr int   M_DEFAULT =     50;

constexpr int32_t S0_DEFAULT   = int32_t(150 * ONE);        // $150.00 = 150.0
constexpr int32_t K_DEFAULT    = int32_t(100 * ONE);        // $100.00 = 100.0
constexpr int32_t r_DEFAULT    = int32_t(0.05 * ONE);       // 5% = 0.05
constexpr int32_t sigma_DEFAULT= int32_t(0.20 * ONE);       // 20% = 0.20
constexpr int32_t T_DEFAULT    = int32_t(1.0  * ONE);       // 1 year

#endif

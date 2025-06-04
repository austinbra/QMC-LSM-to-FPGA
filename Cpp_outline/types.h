// types.h
#ifndef TYPES_H
#define TYPES_H

using Real = double;

constexpr Real PI = 3.141592653589793;

// Default parameters
constexpr int   N_DEFAULT     = 10000;   // # of paths
constexpr int   M_DEFAULT     =   50;    // # of time‐steps
constexpr Real  T_DEFAULT     =  1.0;    // maturity (years)
constexpr Real  r_DEFAULT     = 0.05;
constexpr Real  sigma_DEFAULT = 0.20;
constexpr Real  K_DEFAULT     =100.00;   // strike

#endif // TYPES_H

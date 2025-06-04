#ifndef SOBOL_WRAPPER_H
#define SOBOL_WRAPPER_H

#include <vector>
#include <cstdint>
#include <boost/random/sobol.hpp>
#include "types.h"

class SobolGenerator{
public:
    // dimension = number of coordinates per Sobol point
    // skip is how many points to skip at the start (default 0)
    SobolGenerator(int dimension, std::uint32_t skip = 0);

    //gives me a length dimensional vector of real in [0,1)
    std::vector<Real> nextPoint();

private:
    int dim_;
    std::uint32_t skip_;
    boost::random::sobol engine_;  //32-bit sobol
};

#endif

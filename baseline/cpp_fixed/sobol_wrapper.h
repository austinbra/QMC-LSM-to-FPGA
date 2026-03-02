#ifndef SOBOL_WRAPPER_H
#define SOBOL_WRAPPER_H

#include <vector>
#include <cstdint>
#include <random>
#if defined(USE_BOOST_SOBOL)
#include <boost/random/sobol.hpp>
#endif
#include "types.h"

class SobolGenerator {
public:
    SobolGenerator(int dimension, std::uint32_t skip = 0);
    std::vector<Real> nextPoint();

private:
    int dim_;
    std::uint32_t skip_;
#if defined(USE_BOOST_SOBOL)
    boost::random::sobol engine_;
#else
    std::mt19937 engine_;
    std::uniform_real_distribution<Real> dist_;
#endif
};

#endif

#include "sobol_wrapper.h"
#include <boost/random/uniform_int_distribution.hpp>
#include <boost/math/distributions/normal.hpp>
#include <limits>

SobolGenerator::SobolGenerator(int dimension, std::uint32_t skip) : dim_(dimension), skip_(skip), engine_(static_cast<std::size_t>(dimension)){
    // construct a dim_‐dimensional Sobol engine:
    //skip that many points at beg
    if (skip_ > 0){
        engine_.discard(skip_);
    }
}

std::vector<Real> SobolGenerator::nextPoint()
{
    std::vector<std::uint32_t> ints(dim_);
    engine_.generate(ints.begin(), ints.end());

    //convert to Real num in domain [0,1) by dividing by 2^64
    const Real denom = 4294967296.0; // = 2^32
    std::vector<Real> result(dim_);
    for (int j = 0; j < dim_; ++j){
        result[j] = static_cast<Real>(ints[j]) / denom;
    }
    return result;
}

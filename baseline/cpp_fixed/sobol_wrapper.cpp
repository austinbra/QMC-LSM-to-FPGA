#include "sobol_wrapper.h"

SobolGenerator::SobolGenerator(int dimension, std::uint32_t skip)
    : dim_(dimension), skip_(skip)
#if defined(USE_BOOST_SOBOL)
    , engine_(static_cast<std::size_t>(dimension))
#else
    , engine_(123456789u), dist_(0.0, 1.0)
#endif
{
    if (skip_ > 0) {
#if defined(USE_BOOST_SOBOL)
        engine_.discard(skip_);
#else
        for (std::uint32_t i = 0; i < skip_; ++i) {
            (void)dist_(engine_);
        }
#endif
    }
}

std::vector<Real> SobolGenerator::nextPoint() {
    std::vector<Real> result(dim_);
#if defined(USE_BOOST_SOBOL)
    std::vector<std::uint32_t> ints(dim_);
    engine_.generate(ints.begin(), ints.end());
    const Real denom = 4294967296.0;
    for (int i = 0; i < dim_; ++i) {
        result[i] = static_cast<Real>(ints[i]) / denom;
    }
#else
    for (int i = 0; i < dim_; ++i) {
        result[i] = dist_(engine_);
    }
#endif
    return result;
}

#ifndef UTILS_H
#define UTILS_H

#include <chrono>
#include <string>

using Clock = std::chrono::high_resolution_clock;

//stopwatch for time it takes
struct Timer {
    Clock::time_point start;

    void reset() {
        start = Clock::now();
    }
    double elapsed() const{
        return std::chrono::duration<double>(Clock::now() - start).count();
    }
};

//in main we pass in argc/argv
//parseArgs scans for known flags and returns false if theres an unknown thing
bool parseArgs(int argc, char* argv[],
               int&   N,     // number of paths
               int&   M,     // number of steps
               double& S0,   // spot
               double& K,    // strike
               double& r,    // rate
               double& sigma,// volatility
               double& T     // maturity
);

#endif

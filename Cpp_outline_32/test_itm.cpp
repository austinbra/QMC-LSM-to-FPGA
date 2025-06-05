#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>


// Compare function (call payoff)
double payoffCall(double S, double K) {
    return (S > K ? S - K : 0.0);
}
// Compare function (put payoff)
double payoffPut(double S, double K) {
    return (S < K ? K - S : 0.0);
}

int main() {
    std::cout << std::fixed << std::setprecision(2);

    // 1) Simple ITM/OTM checks for a CALL
    std::cout << "=== Call Option ITM/OTM Test ===\n";
    std::vector<double> spots = { 80.0, 100.0, 120.0 };
    double K_call = 100.0;
    for (double S : spots) {
        double imm = payoffCall(S, K_call);
        bool itm = (imm > 0.0);
        std::cout
            << "Spot S = " << S
            << ", Strike K = " << K_call
            << " -> Payoff = " << imm
            << " => " << (itm ? "ITM" : "OTM/ATM")
            << "\n";
    }
    std::cout << "\n";

    // 2) Simple ITM/OTM checks for a PUT
    std::cout << "=== Put Option ITM/OTM Test ===\n";
    std::vector<double> spots2 = { 80.0, 100.0, 120.0 };
    double K_put = 100.0;
    for (double S : spots2) {
        double imm = payoffPut(S, K_put);
        bool itm = (imm > 0.0);
        std::cout
            << "Spot S = " << S
            << ", Strike K = " << K_put
            << " -> Payoff = " << imm
            << " => " << (itm ? "ITM" : "OTM/ATM")
            << "\n";
    }
    std::cout << "\n";

    // 3) “Exercise vs. Continue” decisions for a few example paths at an intermediate date
    //    Suppose at time t_j, for a given path:
    //      immediatePayoff = max(S - K, 0)  (we’ll use the same call payoff)
    //      continuationValue = (some estimated value)  
    //    We choose “exercise” if immediate >= continuation, else “continue.”

    std::cout << "=== Exercise vs. Continue ===\n";
    struct Case { double S, contVal; };
    std::vector<Case> cases = {
        {  95.0, 10.0 }, // OTM, immediate = 0 < cont → must continue
        { 105.0,  8.0 }, // ITM, immediate = 5 < cont(8) → continue
        { 110.0,  9.5 }, // ITM, immediate =10 > cont(9.5) → exercise
        { 100.0,  0.0 }, // ATM, immediate = 0, cont = 0 → exercise (ties favor exercise)
    };
    for (auto& c : cases) {
        double immediate = payoffCall(c.S, K_call);
        bool itm = (immediate > 0.0);
        bool exercise = (immediate >= c.contVal);

        std::cout
            << "Spot S = " << c.S
            << ", immediate = " << immediate
            << ", cont = " << c.contVal
            << " => "
            << (itm ? "ITM" : "OTM/ATM") << ", "
            << (exercise ? "EXERCISE" : "CONTINUE")
            << "\n";
    }
    std::cout << "\n";

    // 4) Edge cases: zero volatility (σ=0) → path never moves, so only the maturity payoff matters
    std::cout << "=== σ=0 Edge Case ===\n";
    // Simulate two steps: S0=100, σ=0 => S1=S0, S2=S0.
    double S0 = 100.0, K = 100.0, r = 0.05, dt = 0.5; // e.g. dt=0.5 year steps
    // At t=1: immediate = max(100-100,0)=0, cont = discounted payoff at t=2 = e^{-r*dt} * 0
    double imm_t1 = payoffCall(S0, K);
    double cont_t1 = std::exp(-r*dt) * payoffCall(S0, K); // both are 0
    std::cout << "At t1: S=100, immediate=" << imm_t1 << ", cont=" << cont_t1 
              << " => ATM, CONTINUE\n";
    // At t2: maturity, immediate = 0 (option worthless)
    double imm_t2 = payoffCall(S0, K);
    std::cout << "At t2: S=100, immediate=" << imm_t2 << " => OTM at maturity\n";

    return 0;
}

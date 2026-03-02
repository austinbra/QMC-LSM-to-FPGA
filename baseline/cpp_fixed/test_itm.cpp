#include <iostream>
#include <iomanip>
#include <vector>
#include <cmath>

double payoffCall(double S, double K) { return (S > K ? S - K : 0.0); }
double payoffPut(double S, double K) { return (S < K ? K - S : 0.0); }

int main() {
    std::cout << std::fixed << std::setprecision(2);

    std::cout << "=== Call Option ITM/OTM Test ===\n";
    std::vector<double> spots = {80.0, 100.0, 120.0};
    double K_call = 100.0;
    for (double S : spots) {
        double imm = payoffCall(S, K_call);
        std::cout << "Spot S = " << S << ", Strike K = " << K_call
                  << " -> Payoff = " << imm << " => "
                  << (imm > 0.0 ? "ITM" : "OTM/ATM") << "\n";
    }

    std::cout << "\n=== Put Option ITM/OTM Test ===\n";
    for (double S : spots) {
        double imm = payoffPut(S, K_call);
        std::cout << "Spot S = " << S << ", Strike K = " << K_call
                  << " -> Payoff = " << imm << " => "
                  << (imm > 0.0 ? "ITM" : "OTM/ATM") << "\n";
    }

    std::cout << "\n=== Exercise vs. Continue ===\n";
    struct Case { double S, contVal; };
    std::vector<Case> cases = {{95.0, 10.0}, {105.0, 8.0}, {110.0, 9.5}, {100.0, 0.0}};
    for (auto& c : cases) {
        double immediate = payoffCall(c.S, K_call);
        bool exercise = (immediate >= c.contVal);
        std::cout << "Spot S = " << c.S << ", immediate = " << immediate
                  << ", cont = " << c.contVal << " => "
                  << (exercise ? "EXERCISE" : "CONTINUE") << "\n";
    }
    return 0;
}

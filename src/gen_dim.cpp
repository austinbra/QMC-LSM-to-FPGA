#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <iomanip>
#include <cstdint>

int main(){
    const int M = 50; // Number of dimensions
    const int BITS = 32; // Number of direction values per dimension

    std::ifstream infile("gen/joe-kuo-6.21201.txt");
    if (!infile) {
        std::cerr << "cant open joe-kuo-6.21201.txt\n";
        return 1;
    }

    std::ofstream outfile("gen/direction.mem");
    if (!outfile) {
        std::cerr << "cant make direction.mem\n";
        return 1;
    }

    std::string line;
    int dim_count = 0;

    while (std::getline(infile, line)) {
        if (line.empty() || line[0] == '#') continue; // skip comments

        std::istringstream iss(line);
        int d, s, a;
        iss >> d >> s >> a;

        std::vector<uint32_t> v;
        for (int i = 0; i < s; ++i) {
            uint32_t vi;
            iss >> vi;
            v.push_back(vi << (32 - (i + 1)));
        }

        //compute directions
        for (int i = s; i < BITS; ++i) {
            uint32_t val = v[i - s] >> s;
            for (int k = 1; k <= s; ++k)
                if ((a >> (s - k)) & 1)
                    val ^= v[i - k];
            v.push_back(val);
        }

        // write hte first 32 direction numbers
        for (int i = 0; i < BITS; ++i) {
            outfile << std::hex << std::setw(8) << std::setfill('0') << v[i] << "\n";
        }

        if (++dim_count == M)
            break;
    }

    std::cout << "direction.mem created\n";
    return 0;
}

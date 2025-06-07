#include "utils.h"
#include <iostream>
#include <sstream>
using namespace std;

bool parseArgs(int argc, char* argv[], int& N,int& M, double& S0, double& K, double& r, double& sigma, double& T)
{//check for unknown data
    for (int i = 1; i < argc; ++i){
        string arg = argv[i];
        if (arg == "--paths" && i + 1 < argc){
            N = stoi(argv[++i]);
        }
        else if (arg == "--steps" && i + 1 < argc){
            M = stoi(argv[++i]);
        }
        else if (arg == "--S0" && i + 1 < argc){
            S0 = stod(argv[++i]);
        }
        else if (arg == "--K" && i + 1 < argc){
            K = stod(argv[++i]);
        }
        else if (arg == "--r" && i + 1 < argc){
            r = stod(argv[++i]);
        }
        else if (arg == "--sigma" && i + 1 < argc){
            sigma = stod(argv[++i]);
        }
        else if (arg == "--T" && i + 1 < argc){
            T = stod(argv[++i]);
        }
        else{
            cerr << "Unknown argument: " << arg << "\n";
            return false;
        }
    }
    return true;
}

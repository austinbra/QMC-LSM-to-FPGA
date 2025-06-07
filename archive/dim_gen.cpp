#include <fstream>
#include <vector>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <string>

#include <boost/random/sobol.hpp>
#include <boost/random/linear_congruential.hpp>
#include <boost/random/uniform_real.hpp>

//we are writing this in cpp because we dont want to do calculations for multiple dimensions during the sim
//we want to calcualte at compile time and you can't dynamically calculate constants after bitstream generation.

main(){
    int M = 50;
    int dim = M;

    int bits = 32;

    std::ofstream file("gen/direction.mem");
    if (!file){
        std::cerr << "something wrong with direction.mem" << std::endl;
        return 1;
    }
    for (int d = 0; d < dim; ++d){
        boost::random::sobol sobol_gen(dim + 1); // dimensions are 1-based in Boost
        for (int j = 0; j < bits; ++j){
            //uint32_t direction_int = 1U << (31 - j); //use 1U because the direction_int is 32 w/ 1 signed. BUT, no variation per dimension and this copies the same 32 numbers M times.
            //so we use boost to give us the randomness

            sobol_gen.discard(j);
            uint32_t direction_int = sobol_gen.direction_integer(j, d);//problem since boost doesnt make the values availible for some reason
        }//makes 32 directional numbers per dimension M
    }   

    return 0;
}

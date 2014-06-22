/****************************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef FINDUNDEF_H
#define FINDUNDEF_H

#ifdef _MSC_VER
#include "msvc/stdint.h"
#else
#include <stdint.h>
#endif //_MSC_VER
#include <vector>
using std::vector;

#include "Solver.h"

namespace MINISAT
{
using namespace MINISAT;

class FindUndef {
    public:
        FindUndef(Solver& _solver);
        uint unRoll();

    private:
        Solver& solver;

        void moveBinToNormal();
        void moveBinFromNormal();
        bool updateTables();
        void fillPotential();
        void unboundIsPotentials();

        vector<bool> dontLookAtClause; //If set to TRUE, then that clause already has only 1 lit that is true, so it can be skipped during updateFixNeed()
        vector<uint32_t> satisfies;
        vector<bool> isPotential;
        uint32_t isPotentialSum;
        uint32_t binPosition;

};

}; //NAMESPACE MINISAT

#endif //

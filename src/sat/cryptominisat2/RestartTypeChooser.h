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

#ifndef RESTARTTYPECHOOSER_H
#define RESTARTTYPECHOOSER_H

#include "Solver.h"
#include <vector>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "SolverTypes.h"

using std::vector;

namespace MINISAT
{
using namespace MINISAT;

class Solver;

class RestartTypeChooser
{
    public:
        RestartTypeChooser(const Solver& s);
        void addInfo();
        RestartType choose();
        void reset();

    private:
        void calcHeap();
        double avg() const;
        const std::pair<double, double> countVarsDegreeStDev() const;
        double stdDeviation(vector<uint32_t>& measure) const;

        template<class T>
        void addDegrees(const vec<T*>& cs, vector<uint32_t>& degrees) const;

        const Solver& solver;
        const uint32_t topX;
        const uint32_t limit;
        vector<Var> sameIns;

        vector<Var> firstVars, firstVarsOld;
};

inline void RestartTypeChooser::reset()
{
    sameIns.clear();
}

}; //NAMESPACE MINISAT

#endif //RESTARTTYPECHOOSER_H

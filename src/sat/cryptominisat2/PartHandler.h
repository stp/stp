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

#ifndef PARTHANDLER_H
#define PARTHANDLER_H

#include "Solver.h"
#include "PartFinder.h"
#include "Vec.h"
#include "SolverTypes.h"

#include <map>
#include <vector>
using std::map;
using std::vector;
using std::pair;

namespace MINISAT
{
using namespace MINISAT;

class PartHandler
{
    public:
        PartHandler(Solver& solver);
        bool handle();
        const vec<lbool>& getSavedState();
        void newVar();
        void addSavedState();
        void readdRemovedClauses();

        friend class ClauseAllocator;

    private:
        struct sort_pred {
            bool operator()(const std::pair<int,int> &left, const std::pair<int,int> &right) {
                return left.second < right.second;
            }
        };

        //For moving clauses
        void moveClauses(vec<XorClause*>& cs, Solver& newSolver, uint32_t part, PartFinder& partFinder);
        void moveClauses(vec<Clause*>& cs, Solver& newSolver, uint32_t part, PartFinder& partFinder);
        void moveLearntClauses(vec<Clause*>& cs, Solver& newSolver, uint32_t part, PartFinder& partFinder);

        //Checking moved clauses
        bool checkClauseMovement(const Solver& thisSolver, uint32_t part, const PartFinder& partFinder) const;
        template<class T>
        bool checkOnlyThisPart(const vec<T*>& cs, uint32_t part, const PartFinder& partFinder) const;

        Solver& solver;
        vec<lbool> savedState;
        vec<Var> decisionVarRemoved; //variables whose decision-ness has been removed
        vec<Clause*> clausesRemoved;
        vec<XorClause*> xorClausesRemoved;
};

inline const vec<lbool>& PartHandler::getSavedState()
{
    return savedState;
}

inline void PartHandler::newVar()
{
    savedState.push(l_Undef);
}

}; //NAMESPACE MINISAT

#endif //PARTHANDLER_H

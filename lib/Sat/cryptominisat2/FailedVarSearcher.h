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

#ifndef FAILEDVARSEARCHER_H
#define FAILEDVARSEARCHER_H

#include <set>
#include <map>
using std::map;

#include "SolverTypes.h"
#include "Clause.h"
#include "BitArray.h"

namespace MINISAT
{
using namespace MINISAT;

class Solver;

class TwoLongXor
{
    public:
        bool operator==(const TwoLongXor& other) const
        {
            if (var[0] == other.var[0] && var[1] == other.var[1] && inverted == other.inverted)
                return true;
            return false;
        }
        bool operator<(const TwoLongXor& other) const
        {
            if (var[0] < other.var[0]) return true;
            if (var[0] > other.var[0]) return false;

            if (var[1] < other.var[1]) return true;
            if (var[1] > other.var[1]) return false;

            if (inverted < other.inverted) return true;
            if (inverted > other.inverted) return false;

            return false;
        }

        Var var[2];
        bool inverted;
};

class FailedVarSearcher {
    public:
        FailedVarSearcher(Solver& _solver);

        bool search(uint64_t numProps);

    private:
        //For 2-long xor
        const TwoLongXor getTwoLongXor(const XorClause& c);
        void addFromSolver(const vec<XorClause*>& cs);
        uint32_t newBinXor;

        //For detach&re-attach (when lots of vars found)
        template<class T>
        void cleanAndAttachClauses(vec<T*>& cs);
        bool cleanClause(Clause& ps);
        bool cleanClause(XorClause& ps);
        void completelyDetachAndReattach();

        //For re-adding old removed learnt clauses
        bool readdRemovedLearnts();
        void removeOldLearnts();

        //Main
        bool tryBoth(const Lit lit1, const Lit lit2);
        bool tryAll(const Lit* begin, const Lit* end);
        void printResults(const double myTime) const;

        Solver& solver;

        //For failure
        bool failed;

        //bothprop finding
        BitArray propagated;
        BitArray propValue;
        vec<Lit> bothSame;

        //2-long xor-finding
        vec<uint32_t> xorClauseSizes;
        vector<vector<uint32_t> > occur;
        void removeVarFromXors(const Var var);
        void addVarFromXors(const Var var);
        BitArray xorClauseTouched;
        vec<uint32_t> investigateXor;
        std::set<TwoLongXor> twoLongXors;
        bool binXorFind;
        uint32_t lastTrailSize;

        //2-long xor-finding no.2 through
        // 1) (a->b, ~a->~b) -> a=b
        // 2) binary clause (a,c):  (a->g, c->~g) -> a = ~c
        uint32_t bothInvert;

        //finding HyperBins
        void addBinClauses(const Lit& lit);
        BitArray unPropagatedBin;
        vec<Var> propagatedVars;
        void addBin(const Lit& lit1, const Lit& lit2);
        void fillImplies(const Lit& lit);
        BitArray myimplies;
        vec<Var> myImpliesSet;
        uint64_t hyperbinProps;
        vector<uint32_t> litDegrees;
        bool orderLits();
        uint64_t maxHyperBinProps;
        uint64_t binClauseAdded;

        //Temporaries
        vec<Lit> tmpPs;

        //State for this run
        uint32_t toReplaceBefore;
        uint32_t origTrailSize;
        uint64_t origProps;
        uint32_t numFailed;
        uint32_t goodBothSame;

        //State between runs
        bool finishedLastTimeVar;
        uint32_t lastTimeWentUntilVar;
        bool finishedLastTimeBin;
        uint32_t lastTimeWentUntilBin;

        double numPropsMultiplier;
        uint32_t lastTimeFoundTruths;

        uint32_t numCalls;
};

} //NAMESPACE MINISAT

#endif //FAILEDVARSEARCHER_H


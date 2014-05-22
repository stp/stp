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

#ifndef PARTFINDER_H
#define PARTFINDER_H

#include <vector>
#include <map>
#ifdef _MSC_VER
#include "msvc/stdint.h"
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Clause.h"

namespace MINISAT
{
using namespace MINISAT;

class Solver;

using std::map;
using std::vector;
using std::pair;

class PartFinder {

    public:
        PartFinder(Solver& solver);
        bool findParts();

        const map<uint32_t, vector<Var> >& getReverseTable() const; // part->var
        uint32_t getVarPart(const Var var) const;
        const vector<uint32_t>& getTable() const; //var -> part
        const vector<Var>& getPartVars(const uint32_t part);

    private:
        uint setParts();
        template<class T>
        void addToPart(const vec<T*>& cs);

        struct mysorter
        {
            bool operator () (const pair<uint, uint>& left, const pair<uint, uint>& right)
            {
                return left.second < right.second;
            }
        };

        //const bool findParts(vector<Var>& xorFingerprintInMatrix, vector<XorClause*>& xorsInMatrix);
        template<class T>
        void calcIn(const vec<T*>& cs, vector<uint>& numClauseInPart, vector<uint>& sumLitsInPart);

        map<uint32_t, vector<Var> > reverseTable; //part -> vars
        vector<uint32_t> table; //var -> part
        uint32_t part_no;

        Solver& solver;
};

inline const map<uint32_t, vector<Var> >& PartFinder::getReverseTable() const
{
    return reverseTable;
}

inline const vector<Var>& PartFinder::getTable() const
{
    return table;
}

inline uint32_t PartFinder::getVarPart(const Var var) const
{
    return table[var];
}

inline const vector<Var>& PartFinder::getPartVars(const uint32_t part)
{
    return reverseTable[part];
}

}; //NAMESPACE MINISAT

#endif //PARTFINDER_H

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

#ifndef XORFINDER_H
#define XORFINDER_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#define DEBUG_XORFIND
//#define DEBUG_XORFIND2

#include "Clause.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"

class Solver;

using std::pair;

namespace MINISAT
{
using namespace MINISAT;

class XorFinder
{
    public:

        XorFinder(Solver& _solver, vec<Clause*>& cls, ClauseCleaner::ClauseSetType _type);
        bool doNoPart(uint minSize, uint maxSize);
        void addAllXorAsNorm();

    private:
        typedef vector<pair<Clause*, uint> > ClauseTable;

        bool findXors(uint& sumLengths);
        bool getNextXor(ClauseTable::iterator& begin, ClauseTable::iterator& end, bool& impair);

        struct clause_hasher {
            size_t operator()(const Clause* c) const
            {
                size_t hash = 5381;
                hash = ((hash << 5) + hash) ^ c->size();
                for (uint i = 0, size = c->size(); i < size; i++)
                    hash = ((hash << 5) + hash) ^ (*c)[i].var();

                return hash;
            }
        };

        struct clause_sorter_primary {
            bool operator()(const pair<Clause*, uint>& c11, const pair<Clause*, uint>& c22)
            {
                if (c11.first->size() != c22.first->size())
                    return (c11.first->size() < c22.first->size());

                #ifdef DEBUG_XORFIND2
                Clause& c1 = *c11.first;
                for (uint i = 0; i+1 < c1.size(); i++)
                    assert(c1[i].var() <= c1[i+1].var());

                Clause& c2 = *c22.first;
                for (uint i = 0; i+1 < c2.size(); i++)
                    assert(c2[i].var() <= c2[i+1].var());
                #endif //DEBUG_XORFIND2

                for (a = c11.first->getData(), b = c22.first->getData(), end = a + c11.first->size(); a != end; a++, b++) {
                    if (a->var() != b->var())
                        return (a->var() > b->var());
                }

                return false;
            }

            Lit const *a;
            Lit const *b;
            Lit const *end;
        };

        struct clause_sorter_secondary {
            bool operator()(const pair<Clause*, uint>& c11, const pair<Clause*, uint>& c22) const
            {
                const Clause& c1 = *(c11.first);
                const Clause& c2 = *(c22.first);

                for (uint i = 0, size = c1.size(); i < size; i++) {
                    if (c1[i].sign() !=  c2[i].sign())
                        return c1[i].sign();
                }

                return false;
            }
        };

        bool clause_vareq(const Clause* c1, const Clause* c2) const
        {
            if (c1->size() != c2->size())
                return false;

            for (uint i = 0, size = c1->size(); i < size; i++)
                if ((*c1)[i].var() != (*c2)[i].var())
                    return false;

            return true;
        }

        ClauseTable table;
        vector<bool> toRemove;
        vector<bool> toLeaveInPlace;
        void clearToRemove();
        uint32_t foundXors;

        //For adding xor as norm
        void addXorAsNormal3(XorClause& c);
        void addXorAsNormal4(XorClause& c);

        vec<Clause*>& cls;
        ClauseCleaner::ClauseSetType type;

        bool clauseEqual(const Clause& c1, const Clause& c2) const;
        bool impairSigns(const Clause& c) const;
        void countImpairs(const ClauseTable::iterator& begin, const ClauseTable::iterator& end, uint& numImpair, uint& numPair) const;
        bool isXor(const uint32_t size, const ClauseTable::iterator& begin, const ClauseTable::iterator& end, bool& impair);

        Solver& solver;
};

}; //NAMESPACE MINISAT

#endif //XORFINDER_H

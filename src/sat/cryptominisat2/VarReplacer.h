/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#ifndef VARREPLACER_H
#define VARREPLACER_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include <map>
#include <vector>
using std::map;
using std::vector;

#include "Solver.h"
#include "SolverTypes.h"
#include "Clause.h"
#include "Vec.h"

namespace MINISAT
{
using namespace MINISAT;

class VarReplacer
{
    public:
        VarReplacer(Solver& solver);
        ~VarReplacer();
        bool performReplace(bool always = false);
        bool needsReplace();
        template<class T>
        bool replace(T& ps, bool xor_clause_inverted, const uint group);

        void extendModelPossible() const;
        void extendModelImpossible(Solver& solver2) const;
        void reattachInternalClauses();

        uint getNumReplacedLits() const;
        uint getNumReplacedVars() const;
        uint getNumLastReplacedVars() const;
        uint getNewToReplaceVars() const;
        uint32_t getNumTrees() const;
        const vector<Var> getReplacingVars() const;
        const vector<Lit>& getReplaceTable() const;
        const vec<Clause*>& getClauses() const;
        bool varHasBeenReplaced(const Var var) const;
        bool replacingVar(const Var var) const;
        void newVar();

        //No need to update, only stores binary clauses, that
        //have been allocated within pool
        //friend class ClauseAllocator;

    private:
        bool performReplaceInternal();

        bool replace_set(vec<Clause*>& cs, bool binClauses);
        bool replace_set(vec<XorClause*>& cs);
        bool handleUpdatedClause(Clause& c, const Lit origLit1, const Lit origLit2);
        bool handleUpdatedClause(XorClause& c, const Var origVar1, const Var origVar2);
        template<class T>
        void addBinaryXorClause(T& ps, bool xor_clause_inverted, uint group, bool internal = false);

        void setAllThatPointsHereTo(const Var var, const Lit lit);
        bool alreadyIn(const Var var, const Lit lit);

        vector<Lit> table;
        map<Var, vector<Var> > reverseTable;
        vec<Clause*> clauses;

        uint replacedLits;
        uint replacedVars;
        uint lastReplacedVars;
        Solver& solver;
};

inline bool VarReplacer::performReplace(const bool always)
{
    //uint32_t limit = std::min((uint32_t)((double)solver.order_heap.size()*PERCENTAGEPERFORMREPLACE), FIXCLEANREPLACE);
    uint32_t limit = (uint32_t)((double)solver.order_heap.size()*PERCENTAGEPERFORMREPLACE);
    if ((always && getNewToReplaceVars() > 0) || getNewToReplaceVars() > limit)
        return performReplaceInternal();

    return true;
}

inline bool VarReplacer::needsReplace()
{
    uint32_t limit = (uint32_t)((double)solver.order_heap.size()*PERCENTAGEPERFORMREPLACE);
    return (getNewToReplaceVars() > limit);
}

inline uint VarReplacer::getNumReplacedLits() const
{
    return replacedLits;
}

inline uint VarReplacer::getNumReplacedVars() const
{
    return replacedVars;
}

inline uint VarReplacer::getNumLastReplacedVars() const
{
    return lastReplacedVars;
}

inline uint VarReplacer::getNewToReplaceVars() const
{
    return replacedVars-lastReplacedVars;
}

inline const vector<Lit>& VarReplacer::getReplaceTable() const
{
    return table;
}

inline const vec<Clause*>& VarReplacer::getClauses() const
{
    return clauses;
}

inline bool VarReplacer::varHasBeenReplaced(const Var var) const
{
    return table[var].var() != var;
}

inline bool VarReplacer::replacingVar(const Var var) const
{
    return (reverseTable.find(var) != reverseTable.end());
}

inline uint32_t VarReplacer::getNumTrees() const
{
    return reverseTable.size();
}

}; //NAMESPACE MINISAT

#endif //VARREPLACER_H

/***********************************************************************
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
************************************************************************/

#ifndef ONLYNONLEARNTBINS_H
#define ONLYNONLEARNTBINS_H

#include "Solver.h"
#include <set>
using std::set;

namespace MINISAT
{
using namespace MINISAT;

class OnlyNonLearntBins {
    public:
        OnlyNonLearntBins(Solver& solver);

        //propagation
        bool propagate();
        bool propagateBinExcept(const Lit& exceptLit);
        bool propagateBinOneLevel();

        //Management of clauses
        bool fill();
        void removeBin(Lit lit1, Lit lit2);
        void removeClause(Clause& c);
        uint32_t removeBins();

    private:
        vec<vec<WatchedBin> > binwatches;
        set<uint64_t> toRemove;

        Solver& solver;
};

}; //NAMESPACE MINISAT

#endif //ONLYNONLEARNTBINS_H


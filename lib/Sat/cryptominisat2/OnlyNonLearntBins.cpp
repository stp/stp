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

#include "OnlyNonLearntBins.h"

#include <iomanip>
#include "Solver.h"
#include "Clause.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"

namespace MINISAT
{
using namespace MINISAT;

OnlyNonLearntBins::OnlyNonLearntBins(Solver& _solver) :
    solver(_solver)
{}

bool OnlyNonLearntBins::propagate()
{
    while (solver.qhead < solver.trail.size()) {
        Lit p   = solver.trail[solver.qhead++];
        vec<WatchedBin> & wbin = binwatches[p.toInt()];
        solver.propagations += wbin.size()/2;
        for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
            lbool val = solver.value(k->impliedLit);
            if (val.isUndef()) {
                solver.uncheckedEnqueueLight(k->impliedLit);
            } else if (val == l_False) {
                return false;
            }
        }
    }

    return true;
}

bool OnlyNonLearntBins::propagateBinExcept(const Lit& exceptLit)
{
    while (solver.qhead < solver.trail.size()) {
        Lit p   = solver.trail[solver.qhead++];
        vec<WatchedBin> & wbin = binwatches[p.toInt()];
        solver.propagations += wbin.size()/2;
        for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
            lbool val = solver.value(k->impliedLit);
            if (val.isUndef() && k->impliedLit != exceptLit) {
                solver.uncheckedEnqueueLight(k->impliedLit);
            } else if (val == l_False) {
                return false;
            }
        }
    }

    return true;
}

bool OnlyNonLearntBins::propagateBinOneLevel()
{
    Lit p   = solver.trail[solver.qhead];
    vec<WatchedBin> & wbin = binwatches[p.toInt()];
    solver.propagations += wbin.size()/2;
    for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
        lbool val = solver.value(k->impliedLit);
        if (val.isUndef()) {
            solver.uncheckedEnqueueLight(k->impliedLit);
        } else if (val == l_False) {
            return false;
        }
    }

    return true;
}

bool OnlyNonLearntBins::fill()
{
    double myTime = cpuTime();
    assert(solver.performReplace);
    while (solver.performReplace && solver.varReplacer->getClauses().size() > 0) {
        if (!solver.varReplacer->performReplace(true)) return false;
        solver.clauseCleaner->removeAndCleanAll(true);
    }
    assert(solver.varReplacer->getClauses().size() == 0);
    solver.clauseCleaner->moveBinClausesToBinClauses();
    binwatches.growTo(solver.nVars()*2);

    for(Clause **i = solver.binaryClauses.getData(), **end = solver.binaryClauses.getDataEnd(); i != end; i++) {
        Clause& c = **i;
        if (c.learnt()) continue;

        binwatches[(~c[0]).toInt()].push(WatchedBin(c[1]));
        binwatches[(~c[1]).toInt()].push(WatchedBin(c[0]));
    }

    if (solver.verbosity >= 2) {
        std::cout << "c Time to fill non-learnt binary watchlists:"
        << std::fixed << std::setprecision(2) << std::setw(5)
        << cpuTime() - myTime << " s" << std::endl;
    }

    return true;
}

void OnlyNonLearntBins::removeBin(Lit lit1, Lit lit2)
{
    uint32_t index0 = lit1.toInt();
    uint32_t index1 = lit2.toInt();
    if (index1 > index0) std::swap(index0, index1);
    uint64_t final = index0;
    final |= ((uint64_t)index1) << 32;
    toRemove.insert(final);

    solver.removeWatchedBinClAll(binwatches[(~lit1).toInt()], lit2);
    solver.removeWatchedBinClAll(binwatches[(~lit2).toInt()], lit1);
}

uint32_t OnlyNonLearntBins::removeBins()
{
    Clause **i, **j;
    i = j = solver.binaryClauses.getData();
    uint32_t num = 0;
    for (Clause **end = solver.binaryClauses.getDataEnd(); i != end; i++, num++) {
        Clause& c = **i;
        uint32_t index0 = c[0].toInt();
        uint32_t index1 = c[1].toInt();
        if (index1 > index0) std::swap(index0, index1);
        uint64_t final = index0;
        final |= ((uint64_t)index1) << 32;

        if (toRemove.find(final) == toRemove.end()) {
            *j++ = *i;
        } else {
            solver.clauseAllocator.clauseFree(*i);
        }
    }
    solver.binaryClauses.shrink(i-j);
    return (i - j);
}

} //NAMESPACE MINISAT

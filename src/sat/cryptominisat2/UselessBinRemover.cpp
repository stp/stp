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

#include <iomanip>
#include "UselessBinRemover.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "OnlyNonLearntBins.h"

namespace MINISAT
{
using namespace MINISAT;

UselessBinRemover::UselessBinRemover(Solver& _solver, OnlyNonLearntBins& _onlyNonLearntBins) :
    solver(_solver)
    , onlyNonLearntBins(_onlyNonLearntBins)
{
}

#define MAX_REMOVE_BIN_FULL_PROPS 20000000
#define EXTRATIME_DIVIDER 2

bool UselessBinRemover::removeUslessBinFull()
{
    double myTime = cpuTime();
    toDeleteSet.clear();
    toDeleteSet.growTo(solver.nVars()*2, 0);
    uint32_t origHeapSize = solver.order_heap.size();
    uint64_t origProps = solver.propagations;
    bool fixed = false;
    uint32_t extraTime = solver.binaryClauses.size() / EXTRATIME_DIVIDER;

    uint32_t startFrom = solver.mtrand.randInt(solver.order_heap.size());
    for (uint32_t i = 0; i != solver.order_heap.size(); i++) {
        Var var = solver.order_heap[(i+startFrom)%solver.order_heap.size()];
        if (solver.propagations - origProps + extraTime > MAX_REMOVE_BIN_FULL_PROPS) break;
        if (solver.assigns[var] != l_Undef || !solver.decision_var[var]) continue;

        Lit lit(var, true);
        if (!removeUselessBinaries(lit)) {
            fixed = true;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) return false;
            continue;
        }

        lit = ~lit;
        if (!removeUselessBinaries(lit)) {
            fixed = true;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) return false;
            continue;
        }
    }

    uint32_t removedUselessBin = onlyNonLearntBins.removeBins();

    if (fixed) solver.order_heap.filter(Solver::VarFilter(solver));

    if (solver.verbosity >= 1) {
        std::cout
        << "c Removed useless bin:" << std::setw(8) << removedUselessBin
        << "  fixed: " << std::setw(5) << (origHeapSize - solver.order_heap.size())
        << "  props: " << std::fixed << std::setprecision(2) << std::setw(6) << (double)(solver.propagations - origProps)/1000000.0 << "M"
        << "  time: " << std::fixed << std::setprecision(2) << std::setw(5) << cpuTime() - myTime << " s"
        << std::setw(16)  << "   |" << std::endl;
    }

    return true;
}

bool UselessBinRemover::removeUselessBinaries(const Lit& lit)
{
    solver.newDecisionLevel();
    solver.uncheckedEnqueueLight(lit);
    failed = !onlyNonLearntBins.propagateBinOneLevel();
    if (failed) return false;
    bool ret = true;

    oneHopAway.clear();
    assert(solver.decisionLevel() > 0);
    int c;
    if (solver.trail.size()-solver.trail_lim[0] == 0) {
        solver.cancelUntil(0);
        goto end;
    }
    extraTime += (solver.trail.size() - solver.trail_lim[0]) / EXTRATIME_DIVIDER;
    for (c = solver.trail.size()-1; c > (int)solver.trail_lim[0]; c--) {
        Lit x = solver.trail[c];
        toDeleteSet[x.toInt()] = true;
        oneHopAway.push(x);
        solver.assigns[x.var()] = l_Undef;
    }
    solver.assigns[solver.trail[c].var()] = l_Undef;

    solver.qhead = solver.trail_lim[0];
    solver.trail.shrink_(solver.trail.size() - solver.trail_lim[0]);
    solver.trail_lim.clear();
    //solver.cancelUntil(0);

    wrong.clear();
    for(uint32_t i = 0; i < oneHopAway.size(); i++) {
        //no need to visit it if it already queued for removal
        //basically, we check if it's in 'wrong'
        if (toDeleteSet[oneHopAway[i].toInt()]) {
            if (!fillBinImpliesMinusLast(lit, oneHopAway[i], wrong)) {
                ret = false;
                goto end;
            }
        }
    }

    for (uint32_t i = 0; i < wrong.size(); i++) {
        removeBin(~lit, wrong[i]);
    }

    end:
    for(uint32_t i = 0; i < oneHopAway.size(); i++) {
        toDeleteSet[oneHopAway[i].toInt()] = false;
    }

    return ret;
}

void UselessBinRemover::removeBin(const Lit& lit1, const Lit& lit2)
{
    /*******************
    Lit litFind1 = lit_Undef;
    Lit litFind2 = lit_Undef;

    if (solver.binwatches[(~lit1).toInt()].size() < solver.binwatches[(~lit2).toInt()].size()) {
        litFind1 = lit1;
        litFind2 = lit2;
    } else {
        litFind1 = lit2;
        litFind2 = lit1;
    }
    ********************/

    //Find AND remove from watches
    #ifdef VERBOSE_DEBUG
    std::cout << "Removing useless bin: ";
    lit1.print(); lit2.printFull();
    #endif //VERBOSE_DEBUG

    solver.removeWatchedBinClAll(solver.binwatches[(~lit1).toInt()], lit2);
    solver.removeWatchedBinClAll(solver.binwatches[(~lit2).toInt()], lit1);
    onlyNonLearntBins.removeBin(lit1, lit2);
}

bool UselessBinRemover::fillBinImpliesMinusLast(const Lit& origLit, const Lit& lit, vec<Lit>& wrong)
{
    solver.newDecisionLevel();
    solver.uncheckedEnqueueLight(lit);
    //if it's a cycle, it doesn't work, so don't propagate origLit
    failed = !onlyNonLearntBins.propagateBinExcept(origLit);
    if (failed) return false;

    assert(solver.decisionLevel() > 0);
    int c;
    extraTime += (solver.trail.size() - solver.trail_lim[0]) / EXTRATIME_DIVIDER;
    for (c = solver.trail.size()-1; c > (int)solver.trail_lim[0]; c--) {
        Lit x = solver.trail[c];
        if (toDeleteSet[x.toInt()]) {
            wrong.push(x);
            toDeleteSet[x.toInt()] = false;
        };
        solver.assigns[x.var()] = l_Undef;
    }
    solver.assigns[solver.trail[c].var()] = l_Undef;

    solver.qhead = solver.trail_lim[0];
    solver.trail.shrink_(solver.trail.size() - solver.trail_lim[0]);
    solver.trail_lim.clear();
    //solver.cancelUntil(0);

    return true;
}

}; //NAMESPACE MINISAT

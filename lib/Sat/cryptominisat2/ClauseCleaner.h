/*****************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef CLAUSECLEANER_H
#define CLAUSECLEANER_H

#ifdef _MSC_VER
#include "msvc/stdint.h"
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Solver.h"
#include "Subsumer.h"
#include "XorSubsumer.h"

namespace CMSat2
{
using namespace CMSat2;

class ClauseCleaner
{
public:
  ClauseCleaner(Solver& solver);

  enum ClauseSetType
  {
    clauses,
    xorclauses,
    learnts,
    binaryClauses,
    simpClauses,
    xorSimpClauses
  };

  void cleanClauses(vec<Clause*>& cs, ClauseSetType type, unsigned limit = 0);
  void cleanClausesBewareNULL(vec<ClauseSimp>& cs, ClauseSetType type,
                              Subsumer& subs, unsigned limit = 0);
  void cleanXorClausesBewareNULL(vec<XorClauseSimp>& cs, ClauseSetType type,
                                 XorSubsumer& subs, unsigned limit = 0);
  bool cleanClauseBewareNULL(ClauseSimp c, Subsumer& subs);
  bool cleanXorClauseBewareNULL(XorClauseSimp c, XorSubsumer& subs);

  void cleanClauses(vec<XorClause*>& cs, ClauseSetType type, unsigned limit = 0);
  void removeSatisfied(vec<Clause*>& cs, ClauseSetType type, unsigned limit = 0);
  void removeSatisfied(vec<XorClause*>& cs, ClauseSetType type, unsigned limit = 0);
  void removeAndCleanAll(bool nolimit = false);
  bool satisfied(const Clause& c) const;
  bool satisfied(const XorClause& c) const;

  void moveBinClausesToBinClauses();

private:
  bool cleanClause(XorClause& c);
  bool cleanClause(Clause*& c);

  unsigned lastNumUnitarySat[6];
  unsigned lastNumUnitaryClean[6];

  Solver& solver;
};

inline void ClauseCleaner::removeAndCleanAll(bool nolimit)
{
  // unsigned limit = std::min((unsigned)((double)solver.order_heap.size() *
  // PERCENTAGECLEANCLAUSES), FIXCLEANREPLACE);
  unsigned limit = (double)solver.order_heap.size() * PERCENTAGECLEANCLAUSES;
  if (nolimit)
    limit = 0;

  removeSatisfied(solver.binaryClauses, ClauseCleaner::binaryClauses, limit);
  cleanClauses(solver.clauses, ClauseCleaner::clauses, limit);
  cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses, limit);
  cleanClauses(solver.learnts, ClauseCleaner::learnts, limit);
}

} // NAMESPACE CMSat2

#endif // CLAUSECLEANER_H

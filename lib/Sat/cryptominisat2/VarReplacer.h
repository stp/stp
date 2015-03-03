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

#ifndef VARREPLACER_H
#define VARREPLACER_H

#ifdef _MSC_VER
#include "msvc/stdint.h"
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

namespace CMSat2
{
using namespace CMSat2;

class VarReplacer
{
public:
  VarReplacer(Solver& solver);
  ~VarReplacer();
  bool performReplace(bool always = false);
  bool needsReplace();
  template <class T>
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

  // No need to update, only stores binary clauses, that
  // have been allocated within pool
  // friend class ClauseAllocator;

private:
  bool performReplaceInternal();

  bool replace_set(vec<Clause*>& cs, bool binClauses);
  bool replace_set(vec<XorClause*>& cs);
  bool handleUpdatedClause(Clause& c, const Lit origLit1, const Lit origLit2);
  bool handleUpdatedClause(XorClause& c, const Var origVar1,
                           const Var origVar2);
  template <class T>
  void addBinaryXorClause(T& ps, bool xor_clause_inverted, uint group,
                          bool internal = false);

  void setAllThatPointsHereTo(const Var var, const Lit lit);
  bool alreadyIn(const Var var, const Lit lit);

  vector<Lit> table;
  map<Var, vector<Var>> reverseTable;
  vec<Clause*> clauses;

  uint replacedLits;
  uint replacedVars;
  uint lastReplacedVars;
  Solver& solver;
};

inline bool VarReplacer::performReplace(const bool always)
{
  // uint32_t limit =
  // std::min((uint32_t)((double)solver.order_heap.size()*PERCENTAGEPERFORMREPLACE),
  // FIXCLEANREPLACE);
  uint32_t limit =
      (uint32_t)((double)solver.order_heap.size() * PERCENTAGEPERFORMREPLACE);
  if ((always && getNewToReplaceVars() > 0) || getNewToReplaceVars() > limit)
    return performReplaceInternal();

  return true;
}

inline bool VarReplacer::needsReplace()
{
  uint32_t limit =
      (uint32_t)((double)solver.order_heap.size() * PERCENTAGEPERFORMREPLACE);
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
  return replacedVars - lastReplacedVars;
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

} // NAMESPACE CMSat2

#endif // VARREPLACER_H

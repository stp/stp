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

#ifndef XORSIMPLIFIER_H
#define XORSIMPLIFIER_H

#include "Solver.h"
#include "Vec.h"
#include "XSet.h"

namespace CMSat2
{
using namespace CMSat2;

class ClauseCleaner;

class XorSubsumer
{
public:
  XorSubsumer(Solver& S2);
  bool simplifyBySubsumption(bool doFullSubsume = false);
  void unlinkModifiedClause(vec<Lit>& origClause, XorClauseSimp c);
  void unlinkModifiedClauseNoDetachNoNULL(vec<Lit>& origClause,
                                          XorClauseSimp c);
  void unlinkClause(XorClauseSimp cc, Var elim = var_Undef);
  XorClauseSimp linkInClause(XorClause& cl);
  void linkInAlreadyClause(XorClauseSimp& c);
  void newVar();
  void extendModel(Solver& solver2);
  uint32_t getNumElimed() const;
  const vec<char>& getVarElimed() const;
  bool unEliminate(const Var var);
  bool checkElimedUnassigned() const;
  double getTotalTime() const;

private:
  friend class ClauseCleaner;
  friend class ClauseAllocator;

  // Main
  vec<XorClauseSimp> clauses;
  vec<vec<XorClauseSimp>>
      occur; // 'occur[index(lit)]' is a list of constraints containing 'lit'.
  Solver& solver; // The Solver

  // Temporaries (to reduce allocation overhead):
  //
  vec<char> seen_tmp; // (used in various places)

  // Start-up
  void addFromSolver(vec<XorClause*>& cs);
  void addBackToSolver();

  // Subsumption:
  void findSubsumed(XorClause& ps, vec<XorClauseSimp>& out_subsumed);
  bool isSubsumed(XorClause& ps);
  void subsume0(XorClauseSimp ps);
  template <class T1, class T2> bool subset(const T1& A, const T2& B);
  bool subsetAbst(uint32_t A, uint32_t B);
  template <class T>
  void findUnMatched(const T& A, const T& B, vec<Lit>& unmatchedPart);

  // helper
  void testAllClauseAttach() const;

  // dependent removal
  bool removeDependent();
  void fillCannotEliminate();
  vec<char> cannot_eliminate;
  void addToCannotEliminate(Clause* it);
  void removeWrong(vec<Clause*>& cs);

  // Global stats
  double totalTime;
  map<Var, vector<XorClause*>> elimedOutVar;
  vec<char> var_elimed;
  uint32_t numElimed;

  // Heule-process
  template <class T>
  void xorTwoClauses(const T& c1, const T& c2, vec<Lit>& xored);
  bool localSubstitute();
  uint32_t localSubstituteUseful;

  uint32_t clauses_subsumed;
  uint32_t clauses_cut;
  uint32_t origNClauses;
  uint32_t clauseID;
};

inline bool XorSubsumer::subsetAbst(uint32_t A, uint32_t B)
{
  return !(A & ~B);
}

// Assumes 'seen' is cleared (will leave it cleared)
template <class T1, class T2> bool XorSubsumer::subset(const T1& A, const T2& B)
{
  for (uint32_t i = 0; i != B.size(); i++)
    seen_tmp[B[i].var()] = 1;
  for (uint32_t i = 0; i != A.size(); i++)
  {
    if (!seen_tmp[A[i].var()])
    {
      for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].var()] = 0;
      return false;
    }
  }
  for (uint32_t i = 0; i != B.size(); i++)
    seen_tmp[B[i].var()] = 0;
  return true;
}

inline void XorSubsumer::newVar()
{
  occur.push();
  seen_tmp.push(0);
  cannot_eliminate.push(0);
  var_elimed.push(0);
}

inline const vec<char>& XorSubsumer::getVarElimed() const
{
  return var_elimed;
}

inline uint32_t XorSubsumer::getNumElimed() const
{
  return numElimed;
}

inline double XorSubsumer::getTotalTime() const
{
  return totalTime;
}

} // NAMESPACE CMSat2

#endif // XORSIMPLIFIER_H

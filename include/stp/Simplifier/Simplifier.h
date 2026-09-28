/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
 *
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

#ifndef SIMPLIFIER_H
#define SIMPLIFIER_H

#include "SubstitutionMap.h"
#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{
DLL_PUBLIC ASTNode NonMemberBVConstEvaluator(STPMgr* _bm, const ASTNode& t);
DLL_PUBLIC ASTNode NonMemberBVConstEvaluator(STPMgr* _bm, const Kind k,
                                  const ASTVec& input_children,
                                  unsigned int inputwidth);

// The two evaluators above, but straight on the bit-vectors, for callers
// that don't want a hash-consed node built for the result.

// The bit-vector term kinds. Only reads the arguments; returns a fresh
// CBV the caller owns. outputWidth is the evaluated node's width, though
// BVEXTRACT and BVCONCAT compute their own from the arguments.
DLL_PUBLIC CBV NonMemberBVConstEvaluator(const Kind k,
                                         const std::vector<CBV>& args,
                                         unsigned outputWidth);

// The predicate kinds over two bit-vector arguments: the comparisons,
// equality, boolean extraction, and the overflow tests.
DLL_PUBLIC bool NonMemberBVConstPredicateEvaluator(const Kind k, const CBV a,
                                                   const CBV b);

// The same two again, over values that fit in 64 bits, for callers that
// evaluate in bulk. Each argument is masked to its width; argWidths gives
// the width of each argument (used by the extends and concat -- the
// other kinds take it from outputWidth or from the argument values).
DLL_PUBLIC uint64_t NonMemberBVConstEvaluator64(
    const Kind k, const std::vector<uint64_t>& args,
    const std::vector<unsigned>& argWidths, unsigned outputWidth);

// width is the width of a and b. BOOLEXTRACT's b is the bit index, and
// the only predicate whose arguments' widths differ.
DLL_PUBLIC bool NonMemberBVConstPredicateEvaluator64(const Kind k,
                                                     const uint64_t a,
                                                     const uint64_t b,
                                                     const unsigned width);

class Simplifier // not copyable
{
  friend class counterexample;

private:
  // Handy defs
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Memo table for simplifcation. Key is unsimplified node, and
  // value is simplified node. Flat maps: probed and written once per node
  // visit across the whole recursive simplifier, never iterated except to
  // filter constants (order-independent).
  DenseNodeMap* SimplifyMap;
  DenseNodeMap* SimplifyNegMap;
  DenseNodeMap MultInverseMap;

  NodeFactory* nf;

  SubstitutionMap& substitutionMap;
  STPMgr *_bm;

public:
  Simplifier(STPMgr *bm, SubstitutionMap* sm) : substitutionMap(*sm), _bm(bm)
  {
    nf = _bm->defaultNodeFactory;

    SimplifyMap = new DenseNodeMap(INITIAL_TABLE_SIZE);
    SimplifyNegMap = new DenseNodeMap(INITIAL_TABLE_SIZE);

    ASTTrue = nf->getTrue();
    ASTFalse = nf->getFalse();
    ASTUndefined = nf->getUndefined();
  }

  ~Simplifier()
  {
    delete SimplifyMap;
    delete SimplifyNegMap;
  }

  // One-shot, equivalence-preserving simplification over a throwaway
  // substitution map, so nothing can couple across calls. The
  // constructor demands a SubstitutionMap, which had three callers
  // hand-rolling the empty-map pairing to get exactly this.
  static ASTNode simplifyAlone(STPMgr* bm, const ASTNode& n);

  Simplifier(Simplifier const&) = delete;
  Simplifier& operator=(Simplifier const&) = delete;

  // functions for checking and updating simplification map
  bool CheckSimplifyMap(const ASTNode& key, ASTNode& output, bool pushNeg);
  void UpdateSimplifyMap(const ASTNode& key, const ASTNode& value, bool pushNeg);
  bool CheckMultInverseMap(const ASTNode& key, ASTNode& output);
  void UpdateMultInverseMap(const ASTNode& key, const ASTNode& value);

  // Map for solved variables
  bool UpdateSolverMap(const ASTNode& e0, const ASTNode& e1);
  ASTNode topLevel(const ASTNode& a, ArrayTransformer* at);

  // substitution
  bool InsideSubstitutionMap(const ASTNode& a, ASTNode& output);
  bool InsideSubstitutionMap(const ASTNode& a);
  bool UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1);
  bool UpdateSubstitutionMapFewChecks(const ASTNode& e0, const ASTNode& e1);

  DLL_PUBLIC ASTNode applySubstitutionMap(const ASTNode& n);
  ASTNode applySubstitutionMapUntilArrays(const ASTNode& n,
                                          DenseNodeMap& cache);

  
  #ifdef _MSC_VER
  #include <sal.h>
  #define WARN_UNUSED_RESULT _Check_return_
  #else
  #define WARN_UNUSED_RESULT __attribute__((warn_unused_result))
  #endif

  DLL_PUBLIC WARN_UNUSED_RESULT ASTNode applySubstitutionMapAtTopLevel(const ASTNode& topLevel) WARN_UNUSED_RESULT;
    
  #undef WARN_UNUSED_RESULT

  /****************************************************************
   * Simplification functions                                     *
   ****************************************************************/

  ASTNodeMap FindConsts_TopLevel(const ASTNode& b, bool pushNeg);


  ASTNode SimplifyFormula_TopLevel(const ASTNode& a, bool pushNeg);

  ASTNode SimplifyTerm_TopLevel(const ASTNode& b);

  ASTNode SimplifyTerm(const ASTNode& inputterm);

  ASTNode SimplifyFormula(const ASTNode& a, bool pushNeg);

  ASTNode CreateSimplifiedEQ(const ASTNode& t1, const ASTNode& t2);

  ASTNode CreateSimplifiedTermITE(const ASTNode& t1, const ASTNode& t2,
                                  const ASTNode& t3);

  ASTNode BVConstEvaluator(const ASTNode& t);

  // checks if the input constant is odd or not
  bool BVConstIsOdd(const ASTNode& c);

  // computes the multiplicatve inverse of the input
  ASTNode MultiplicativeInverse(const ASTNode& c);

  void printCacheStatus();

  bool hasUnappliedSubstitutions()
  {
    return substitutionMap.hasUnappliedSubstitutions();
  }

  DenseNodeMap* Return_SolverMap()
  {
    return substitutionMap.Return_SolverMap();
  }

  void haveAppliedSubstitutionMap()
  {
    substitutionMap.haveAppliedSubstitutionMap();
  }

  void ClearAllTables()
  {
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    MultInverseMap.clear();
    substitutionMap.clear();
  }

  // These can be cleared (to save memory) without changing the answer.
  void ClearCaches()
  {
    MultInverseMap.clear();
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    getVariablesInExpression().ClearAllTables();
  }

  VariablesInExpression& getVariablesInExpression()
  {
    return substitutionMap.getVariablesInExpression();
  }

private:
  class SimplifyDriver;

  enum class SimplifyJob
  {
    Formula,
    Term,
    Array
  };

  // Formulae, bit-vector/floating-point terms, and the array terms reached by
  // READ all share one continuation stack. A generated rewrite is scheduled
  // on that stack just like an input child, so neither input depth nor rewrite
  // depth becomes C++ call depth.
  ASTNode simplifyNode(const ASTNode& n, bool pushNeg, SimplifyJob job);

  ASTNode makeTower(const Kind k, const ASTVec& children);

  ASTNode pullUpBVSX(const ASTNode output);

  ASTNode simplify_term_switch(const ASTNode& actualInputterm,
                               ASTNode& inputterm, ASTNode& output, Kind k,
                               const unsigned int inputValueWidth);

  void ResetSimplifyMaps(void);

  bool hasBeenSimplified(const ASTNode& n);

  ASTNode ITEOpt_InEqs(const ASTNode& in1, ASTNode& conditionToNegate);

  ASTNode PullUpITE(const ASTNode& in);

  ASTNode CreateSimplifiedINEQ(const Kind k, const ASTNode& a0,
                               const ASTNode& a1, bool pushNeg);

  // SimplifyFormula's head: the answers it gives without dispatching at all,
  // plus the PullUpITE'd node the dispatch would run on. True when `out` is
  // the answer.
  bool formulaShortcut(const ASTNode& b, bool pushNeg, ASTNode& a,
                       ASTNode& out);

  ASTNode CombineLikeTerms(const ASTNode& a);
  ASTNode CombineLikeTerms(const ASTVec& a);

  ASTNode LhsMinusRhsTerm(const ASTNode& eq,
                          const ASTNode& simplifiedNegatedRhs);

  ASTNode DistributeMultOverPlus(const ASTNode& a,
                                 bool startdistribution = false);

};
} // end of namespace
#endif

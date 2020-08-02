/********************************************************************
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

class Simplifier // not copyable
{
  friend class counterexample;

private:
  // Handy defs
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Memo table for simplifcation. Key is unsimplified node, and
  // value is simplified node.
  ASTNodeMap* SimplifyMap;
  ASTNodeMap* SimplifyNegMap;
  std::unordered_set<int> AlwaysTrueHashSet;
  ASTNodeMap MultInverseMap;

  // For ArrayWrite Abstraction: map from read-over-write term to
  // newname.
  // ASTNodeMap * ReadOverWrite_NewName_Map;

  // For ArrayWrite Refinement: Map new arraynames to
  // Read-Over-Write terms
  // ASTNodeMap NewName_ReadOverWrite_Map;

  // Ptr to STP Manager
  STPMgr* _bm;

  NodeFactory* nf;

  SubstitutionMap substitutionMap;

  void checkIfInSimplifyMap(const ASTNode& n, ASTNodeSet visited);

  ASTNode makeTower(const Kind k, const ASTVec& children);

  ASTNode pullUpBVSX(const ASTNode output);

  ASTNode simplify_term_switch(const ASTNode& actualInputterm,
                               ASTNode& inputterm, ASTNode& output,
                               ASTNodeMap* VarConstMap, Kind k,
                               const unsigned int inputValueWidth);

public:
  static ASTNode convertArithmeticKnownShiftAmount(const Kind k,
                                                   const ASTVec& children,
                                                   STPMgr& bm, NodeFactory* nf);
  static ASTNode convertKnownShiftAmount(const Kind k, const ASTVec& children,
                                         STPMgr& bm, NodeFactory* nf);

  Simplifier(STPMgr* bm) : _bm(bm), substitutionMap(this, bm)
  {
    SimplifyMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
    SimplifyNegMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
    // ReadOverWrite_NewName_Map = new ASTNodeMap();

    ASTTrue = bm->CreateNode(TRUE);
    ASTFalse = bm->CreateNode(FALSE);
    ASTUndefined = bm->CreateNode(UNDEFINED);

    nf = bm->defaultNodeFactory;
  }

  ~Simplifier()
  {
    delete SimplifyMap;
    delete SimplifyNegMap;
    // delete ReadOverWrite_NewName_Map;
  }

  // Check the map passed to SimplifyTerm
  bool CheckMap(ASTNodeMap* VarConstMap, const ASTNode& key, ASTNode& output);

  // functions for checking and updating simplification map
  bool CheckSimplifyMap(const ASTNode& key, ASTNode& output, bool pushNeg,
                        ASTNodeMap* VarConstMap = NULL);
  void UpdateSimplifyMap(const ASTNode& key, const ASTNode& value, bool pushNeg,
                         ASTNodeMap* VarConstMap = NULL);
  bool CheckAlwaysTrueFormSet(const ASTNode& key, bool& result);
  void UpdateAlwaysTrueFormSet(const ASTNode& val);
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
  DLL_PUBLIC ASTNode applySubstitutionMapUntilArrays(const ASTNode& n);

  void ResetSimplifyMaps(void);

  /****************************************************************
   * Simplification functions                                     *
   ****************************************************************/

  ASTNode SimplifyFormula_TopLevel(const ASTNode& a, bool pushNeg,
                                   ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyTerm_TopLevel(const ASTNode& b);

  ASTNode SimplifyFormula(const ASTNode& a, bool pushNeg,
                          ASTNodeMap* VarConstMap = NULL);

  bool hasBeenSimplified(const ASTNode& n);

  ASTNode SimplifyTerm(const ASTNode& inputterm,
                       ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyFormula_NoRemoveWrites(const ASTNode& a, bool pushNeg,
                                         ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyAtomicFormula(const ASTNode& a, bool pushNeg,
                                ASTNodeMap* VarConstMap = NULL);

  ASTNode CreateSimplifiedEQ(const ASTNode& t1, const ASTNode& t2);

  ASTNode ITEOpt_InEqs(const ASTNode& in1, ASTNodeMap* VarConstMap = NULL);

  ASTNode PullUpITE(const ASTNode& in);

  ASTNode CreateSimplifiedTermITE(const ASTNode& t1, const ASTNode& t2,
                                  const ASTNode& t3);

  ASTNode CreateSimplifiedFormulaITE(const ASTNode& in0, const ASTNode& in1,
                                     const ASTNode& in2);

  ASTNode CreateSimplifiedINEQ(const Kind k, const ASTNode& a0,
                               const ASTNode& a1, bool pushNeg);

  ASTNode SimplifyNotFormula(const ASTNode& a, bool pushNeg,
                             ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyAndOrFormula(const ASTNode& a, bool pushNeg,
                               ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyXorFormula(const ASTNode& a, bool pushNeg,
                             ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyNandFormula(const ASTNode& a, bool pushNeg,
                              ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyNorFormula(const ASTNode& a, bool pushNeg,
                             ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyImpliesFormula(const ASTNode& a, bool pushNeg,
                                 ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyIffFormula(const ASTNode& a, bool pushNeg,
                             ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyIteFormula(const ASTNode& a, bool pushNeg,
                             ASTNodeMap* VarConstMap = NULL);

  ASTNode CombineLikeTerms(const ASTNode& a);
  ASTNode CombineLikeTerms(const ASTVec& a);

  ASTNode LhsMinusRhs(const ASTNode& eq);

  ASTNode DistributeMultOverPlus(const ASTNode& a,
                                 bool startdistribution = false);

  // ASTNode ConvertBVSXToITE(const ASTNode& a);

  ASTNode BVConstEvaluator(const ASTNode& t);

  // checks if the input constant is odd or not
  bool BVConstIsOdd(const ASTNode& c);

  // computes the multiplicatve inverse of the input
  ASTNode MultiplicativeInverse(const ASTNode& c);

  // Replaces WRITE(Arr,i,val) with ITE(j=i, val, READ(Arr,j))
  ASTNode RemoveWrites_TopLevel(const ASTNode& term);
  ASTNode RemoveWrites(const ASTNode& term);
  ASTNode SimplifyWrites_InPlace(const ASTNode& term,
                                 ASTNodeMap* VarConstMap = NULL);

  ASTNode SimplifyArrayTerm(const ASTNode& term, ASTNodeMap* VarConstMap);

  void printCacheStatus();

  bool hasUnappliedSubstitutions()
  {
    return substitutionMap.hasUnappliedSubstitutions();
  }

  ASTNodeMap* Return_SolverMap() { return substitutionMap.Return_SolverMap(); }

  void haveAppliedSubstitutionMap()
  {
    substitutionMap.haveAppliedSubstitutionMap();
  }

  void ClearAllTables()
  {
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    // ReadOverWrite_NewName_Map->clear();
    // NewName_ReadOverWrite_Map.clear();
    AlwaysTrueHashSet.clear();
    MultInverseMap.clear();
    substitutionMap.clear();
  }

  // These can be cleared (to save memory) without changing the answer.
  void ClearCaches()
  {
    AlwaysTrueHashSet.clear();
    MultInverseMap.clear();
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    getVariablesInExpression().ClearAllTables();
  }

  VariablesInExpression& getVariablesInExpression()
  {
    return substitutionMap.getVariablesInExpression();
  }
};
} // end of namespace
#endif

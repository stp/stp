/*
 * substitutionMap.cpp
 *
 */

#include "SubstitutionMap.h"
#include "simplifier.h"
#include "../AST/ArrayTransformer.h"

namespace BEEV
{

SubstitutionMap::~SubstitutionMap()
{
	delete SolverMap;
}


//The big substitution function
ASTNode SubstitutionMap::CreateSubstitutionMap(const ASTNode& a,  ArrayTransformer*at
)
{
  if (!bm->UserFlags.wordlevel_solve_flag)
    return a;

  ASTNode output = a;
  //if the variable has been solved for, then simply return it
  if (CheckSubstitutionMap(a, output))
    return output;

  //traverse a and populate the SubstitutionMap
  const Kind k = a.GetKind();
  if (SYMBOL == k && BOOLEAN_TYPE == a.GetType())
    {
      bool updated = UpdateSubstitutionMap(a, ASTTrue);
      output = updated ? ASTTrue : a;
      return output;
    }
  if (NOT == k && SYMBOL == a[0].GetKind())
    {
      bool updated = UpdateSubstitutionMap(a[0], ASTFalse);
      output = updated ? ASTTrue : a;
      return output;
    }

  if (IFF == k)
    {
      ASTVec c = a.GetChildren();
      SortByArith(c);
      if (SYMBOL != c[0].GetKind() ||
          bm->VarSeenInTerm(c[0],
                            simp->SimplifyFormula_NoRemoveWrites(c[1], false)))
        {
          return a;
        }
      bool updated =
        UpdateSubstitutionMap(c[0],
                                    simp->SimplifyFormula(c[1], false));
      output = updated ? ASTTrue : a;
      return output;
    }

  if (EQ == k)
    {
      //fill the arrayname readindices vector if e0 is a
      //READ(Arr,index) and index is a BVCONST
      ASTVec c = a.GetChildren();
      SortByArith(c);
      ASTNode c1 = simp->SimplifyTerm(c[1]);
      at->FillUp_ArrReadIndex_Vec(c[0], c1);

      if (SYMBOL == c[0].GetKind()
          && bm->VarSeenInTerm(c[0], c1))
        {
          return a;
        }

      if (1 == TermOrder(c[0], c1)
          && READ == c[0].GetKind()
          && bm->VarSeenInTerm(c[0][1], c1))
        {
          return a;
        }
      bool updated = UpdateSubstitutionMap(c[0], c1);
      output = updated ? ASTTrue : a;
      return output;
    }

  if (AND == k)
    {
      ASTVec o;
      ASTVec c = a.GetChildren();
      for (ASTVec::iterator
             it = c.begin(), itend = c.end();
           it != itend; it++)
        {
          simp->UpdateAlwaysTrueFormMap(*it);
          ASTNode aaa = CreateSubstitutionMap(*it,at);

          if (ASTTrue != aaa)
            {
              if (ASTFalse == aaa)
                return ASTFalse;
              else
                o.push_back(aaa);
            }
        }
      if (o.size() == 0)
        return ASTTrue;

      if (o.size() == 1)
        return o[0];

      return bm->CreateNode(AND, o);
    }

  //printf("I gave up on kind: %d node: %d\n", k, a.GetNodeNum());
  return output;
} //end of CreateSubstitutionMap()

};

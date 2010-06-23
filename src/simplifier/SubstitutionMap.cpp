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

// if false. Don't simplify while creating the substitution map.
// This makes it easier to spot how long is spent in the simplifier.
const bool simplify_during_create_subM = false;

//if a is READ(Arr,const) or SYMBOL, and b is BVCONST then return 1
//if b is READ(Arr,const) or SYMBOL, and a is BVCONST then return -1
//
//else return 0 by default
int TermOrder(const ASTNode& a, const ASTNode& b)
{
  Kind k1 = a.GetKind();
  Kind k2 = b.GetKind();

  //a is of the form READ(Arr,const), and b is const, or
  //a is of the form var, and b is const
  if ((k1 == READ
       && a[0].GetKind() == SYMBOL
       && a[1].GetKind() == BVCONST
       && (k2 == BVCONST)))
    // || k2 == READ && b[0].GetKind() == SYMBOL && b[1].GetKind()
    // == BVCONST)))
    return 1;

  if (SYMBOL == k1 && (BVCONST == k2 || TRUE == k2 || FALSE == k2))
    return 1;

  //b is of the form READ(Arr,const), and a is const, or
  //b is of the form var, and a is const
  if ((k1 == BVCONST)
      && ((k2 == READ
           && b[0].GetKind() == SYMBOL
           && b[1].GetKind() == BVCONST)))
    return -1;

  if (SYMBOL == k2
      && (BVCONST == k1
          || TRUE == k1
          || FALSE == k1))
    return -1;

  return 0;
} //End of TermOrder()


//This finds everything which is (= SYMBOL BVCONST) and everything that is (READ SYMBOL BVCONST).
//i.e. anything that has a termorder of 1 or -1.
// The bvsolver puts expressions of the form (= SYMBOL TERM) into the solverMap.

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

  if (IFF == k || EQ == k)
    {
      ASTVec c = a.GetChildren();
      SortByArith(c);

      ASTNode c1;
      if (EQ == k)
    	  c1 = simplify_during_create_subM ? simp->SimplifyTerm(c[1]) : c[1];
      else// (IFF == k )
    	  c1= simplify_during_create_subM ?  simp->SimplifyFormula_NoRemoveWrites(c[1], false) : c[1];

      //fill the arrayname readindices vector if e0 is a
      //READ(Arr,index) and index is a BVCONST
      int to;
      if ((to =TermOrder(c[0],c1))==1 && c[0].GetKind() == READ)
    	  at->FillUp_ArrReadIndex_Vec(c[0], c1);
      else if (to ==-1 && c1.GetKind() == READ)
		at->FillUp_ArrReadIndex_Vec(c1,c[0]);

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

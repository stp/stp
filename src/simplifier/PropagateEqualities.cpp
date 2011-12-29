#include <string>
#include "PropagateEqualities.h"
#include "simplifier.h"
#include "../AST/ArrayTransformer.h"

namespace BEEV
{
    const string PropagateEqualities::message = "After Propagating Equalities: ";

    // if false. Don't simplify while creating the substitution map.
    // This makes it easier to spot how long is spent in the simplifier.
    const bool simplify_during_create_subM = false;


    //This finds conjuncts which are one of: (= SYMBOL BVCONST), (= BVCONST (READ SYMBOL BVCONST)),
    // (IFF SYMBOL TRUE), (IFF SYMBOL FALSE), (IFF SYMBOL SYMBOL), (=SYMBOL SYMBOL)
    // or (=SYMBOL BVCONST).
    // It tries to remove the conjunct, storing it in the substitutionmap. It replaces it in the
    // formula by true.
    // The bvsolver puts expressions of the form (= SYMBOL TERM) into the solverMap.

    ASTNode PropagateEqualities::propagate(const ASTNode& a,  ArrayTransformer*at)
    {
      if (!bm->UserFlags.propagate_equalities)
        return a;

      ASTNode output;
      //if the variable has been solved for, then simply return it
      if (simp->CheckSubstitutionMap(a, output))
        return output;

      if (!alreadyVisited.insert(a.GetNodeNum()).second)
      {
        return a;
      }

      output = a;

      //traverse a and populate the SubstitutionMap
      const Kind k = a.GetKind();
      if (SYMBOL == k && BOOLEAN_TYPE == a.GetType())
        {
          bool updated = simp->UpdateSubstitutionMap(a, ASTTrue);
          output = updated ? ASTTrue : a;
        }
      else if (NOT == k && SYMBOL == a[0].GetKind())
        {
          bool updated = simp->UpdateSubstitutionMap(a[0], ASTFalse);
          output = updated ? ASTTrue : a;
        }
      else if (IFF == k || EQ == k)
        {
              ASTVec c = a.GetChildren();

              if (simplify_during_create_subM)
                      SortByArith(c);

              if (c[0] == c[1])
                      return ASTTrue;

          ASTNode c1;
          if (EQ == k)
              c1 = simplify_during_create_subM ? simp->SimplifyTerm(c[1]) : c[1];
          else// (IFF == k )
              c1= simplify_during_create_subM ?  simp->SimplifyFormula_NoRemoveWrites(c[1], false) : c[1];

          bool updated = simp->UpdateSubstitutionMap(c[0], c1);
          output = updated ? ASTTrue : a;

          if (updated)
            {
              //fill the arrayname readindices vector if e0 is a
              //READ(Arr,index) and index is a BVCONST
              int to;
              if ((to =TermOrder(c[0],c1))==1 && c[0].GetKind() == READ)
                  at->FillUp_ArrReadIndex_Vec(c[0], c1);
              else if (to ==-1 && c1.GetKind() == READ)
                        at->FillUp_ArrReadIndex_Vec(c1,c[0]);
            }
        }
      else if (XOR == k)
      {
              if (a.Degree() !=2)
                return output;

              int to = TermOrder(a[0],a[1]);
              if (0 == to)
                {
                  if (a[0].GetKind() == NOT && a[0][0].GetKind() == EQ && a[0][0][0].GetValueWidth() ==1 && a[0][0][1].GetKind() == SYMBOL)
                    {
                      // (XOR (NOT(= (1 v)))  ... )
                      const ASTNode& symbol = a[0][0][1];
                      const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], a[0][0][0], nf->CreateTerm(BVNEG, 1,a[0][0][0]));

                      if (simp->UpdateSolverMap(symbol, newN))
                          output =  ASTTrue;
                    }
                  else if (a[1].GetKind() == NOT && a[1][0].GetKind() == EQ && a[1][0][0].GetValueWidth() ==1 && a[1][0][1].GetKind() == SYMBOL)
                    {
                      const ASTNode& symbol = a[1][0][1];
                      const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], a[1][0][0], nf->CreateTerm(BVNEG, 1,a[1][0][0]));

                      if (simp->UpdateSolverMap(symbol, newN))
                          output =  ASTTrue;
                    }
                  else if (a[0].GetKind() == EQ && a[0][0].GetValueWidth() ==1 && a[0][1].GetKind() == SYMBOL)
                    {
                      // XOR ((= 1 v) ... )

                      const ASTNode& symbol = a[0][1];
                      const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], nf->CreateTerm(BVNEG, 1,a[0][0]), a[0][0]);

                      if (simp->UpdateSolverMap(symbol, newN))
                          output =  ASTTrue;
                    }
                  else if (a[1].GetKind() == EQ && a[1][0].GetValueWidth() ==1 && a[1][1].GetKind() == SYMBOL)
                    {
                      const ASTNode& symbol = a[1][1];
                      const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], nf->CreateTerm(BVNEG, 1,a[1][0]), a[1][0]);

                      if (simp->UpdateSolverMap(symbol, newN))
                          output =  ASTTrue;
                    }
                  else
                  return output;
                }
              else
                {
                    ASTNode symbol,rhs;
                    if (to==1)
                    {
                        symbol = a[0];
                        rhs = a[1];
                    }
                    else
                    {
                        symbol = a[1];
                        rhs = a[0];
                    }

                    assert(symbol.GetKind() == SYMBOL);

                    if (simp->UpdateSolverMap(symbol, nf->CreateNode(NOT, rhs)))
                       output =  ASTTrue;
                }
      }
      else if (AND == k)
        {
              const ASTVec& c = a.GetChildren();
              ASTVec o;
          o.reserve(c.size());

          for (ASTVec::const_iterator
                 it = c.begin(), itend = c.end();
               it != itend; it++)
            {
              simp->UpdateAlwaysTrueFormSet(*it);
              ASTNode aaa = propagate(*it,at);

              if (ASTTrue != aaa)
                {
                  if (ASTFalse == aaa)
                    return ASTFalse;
                  else
                    o.push_back(aaa);
                }
            }
          if (o.size() == 0)
            output =  ASTTrue;
          else if (o.size() == 1)
            output = o[0];
          else if (o != c)
            output = nf->CreateNode(AND, o);
          else
            output = a;
        }

      return output;
    } //end of CreateSubstitutionMap()


};

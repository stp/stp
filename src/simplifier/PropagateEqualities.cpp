#include <string>
#include "PropagateEqualities.h"
#include "simplifier.h"
#include "../AST/ArrayTransformer.h"

namespace BEEV
{

  // This doesn't rewrite changes through properly so needs to have a substitution applied to its output.

    ASTNode
    PropagateEqualities::propagate(const ASTNode& a, ArrayTransformer*at)
    {
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
                const ASTVec& c = a.GetChildren();

                if (c[0] == c[1])
                    return ASTTrue;

                bool updated = simp->UpdateSubstitutionMap(c[0], c[1]);
                output = updated ? ASTTrue : a;

                if (updated)
                    {
                        //fill the arrayname readindices vector if e0 is a
                        //READ(Arr,index) and index is a BVCONST
                        int to;
                        if ((to = TermOrder(c[0], c[1])) == 1 && c[0].GetKind() == READ)
                            at->FillUp_ArrReadIndex_Vec(c[0], c[1]);
                        else if (to == -1 && c[1].GetKind() == READ)
                            at->FillUp_ArrReadIndex_Vec(c[1], c[0]);
                    }
            }
        else if (XOR == k)
            {
                if (a.Degree() != 2)
                    return output;

                int to = TermOrder(a[0], a[1]);
                if (0 == to)
                    {
                        if (a[0].GetKind() == NOT && a[0][0].GetKind() == EQ && a[0][0][0].GetValueWidth() == 1
                                && a[0][0][1].GetKind() == SYMBOL)
                            {
                                // (XOR (NOT(= (1 v)))  ... )
                                const ASTNode& symbol = a[0][0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], a[0][0][0],
                                        nf->CreateTerm(BVNEG, 1, a[0][0][0]));

                                if (simp->UpdateSolverMap(symbol, newN))
                                    output = ASTTrue;
                            }
                        else if (a[1].GetKind() == NOT && a[1][0].GetKind() == EQ && a[1][0][0].GetValueWidth() == 1
                                && a[1][0][1].GetKind() == SYMBOL)
                            {
                                const ASTNode& symbol = a[1][0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], a[1][0][0],
                                        nf->CreateTerm(BVNEG, 1, a[1][0][0]));

                                if (simp->UpdateSolverMap(symbol, newN))
                                    output = ASTTrue;
                            }
                        else if (a[0].GetKind() == EQ && a[0][0].GetValueWidth() == 1 && a[0][1].GetKind() == SYMBOL)
                            {
                                // XOR ((= 1 v) ... )

                                const ASTNode& symbol = a[0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], nf->CreateTerm(BVNEG, 1, a[0][0]),
                                        a[0][0]);

                                if (simp->UpdateSolverMap(symbol, newN))
                                    output = ASTTrue;
                            }
                        else if (a[1].GetKind() == EQ && a[1][0].GetValueWidth() == 1 && a[1][1].GetKind() == SYMBOL)
                            {
                                const ASTNode& symbol = a[1][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], nf->CreateTerm(BVNEG, 1, a[1][0]),
                                        a[1][0]);

                                if (simp->UpdateSolverMap(symbol, newN))
                                    output = ASTTrue;
                            }
                        else
                            return output;
                    }
                else
                    {
                        ASTNode symbol, rhs;
                        if (to == 1)
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
                            output = ASTTrue;
                    }
            }
        else if (AND == k)
            {
                const ASTVec& c = a.GetChildren();
                ASTVec o;
                o.reserve(c.size());

                for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
                    {
                        if (always_true)
                          simp->UpdateAlwaysTrueFormSet(*it);
                        ASTNode aaa = propagate(*it, at);

                        if (ASTTrue != aaa)
                            {
                                if (ASTFalse == aaa)
                                    return ASTFalse;
                                else
                                    o.push_back(aaa);
                            }
                    }
                if (o.size() == 0)
                    output = ASTTrue;
                else if (o.size() == 1)
                    output = o[0];
                else if (o != c)
                    output = nf->CreateNode(AND, o);
                else
                    output = a;
            }

        return output;
    } //end of CreateSubstitutionMap()

}
;

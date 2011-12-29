#ifndef PROPAGATEEQUALITIES_H_
#define PROPAGATEEQUALITIES_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"

    //This finds conjuncts which are one of: (= SYMBOL BVCONST), (= BVCONST (READ SYMBOL BVCONST)),
    // (IFF SYMBOL TRUE), (IFF SYMBOL FALSE), (IFF SYMBOL SYMBOL), (=SYMBOL SYMBOL)
    // or (=SYMBOL BVCONST).
    // It tries to remove the conjunct, storing it in the substitutionmap. It replaces it in the
    // formula by true.


namespace BEEV
{

    class Simplifier;
    class ArrayTransformer;

    class PropagateEqualities
    {

        ASTNode
        topLevelReal(const ASTNode& a, ArrayTransformer*at);

        Simplifier *simp;
        NodeFactory *nf;
        STPMgr *bm;
        const ASTNode ASTTrue, ASTFalse;
        HASHSET<int> alreadyVisited;

    public:
        const static string message;

        PropagateEqualities(Simplifier *simp_, NodeFactory *nf_, STPMgr *bm_) :
                ASTTrue(bm_->ASTTrue), ASTFalse(bm_->ASTTrue)

        {
            simp = simp_;
            nf = nf_;
            bm = bm_;
        }

        ASTNode
        topLevel(const ASTNode& a, ArrayTransformer*at);
    };
}

#endif

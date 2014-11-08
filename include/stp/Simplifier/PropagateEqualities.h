// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: December, 2011
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

#ifndef PROPAGATEEQUALITIES_H_
#define PROPAGATEEQUALITIES_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/simplifier.h"

//This finds conjuncts which are one of: (= SYMBOL BVCONST), (= BVCONST (READ SYMBOL BVCONST)),
// (IFF SYMBOL TRUE), (IFF SYMBOL FALSE), (IFF SYMBOL SYMBOL), (=SYMBOL SYMBOL)
// or (=SYMBOL BVCONST).
// It tries to remove the conjunct, storing it in the substitutionmap. It replaces it in the
// formula by true.

namespace BEEV
{
    class Simplifier;
    class ArrayTransformer;

    class PropagateEqualities :  boost::noncopyable
    {

        Simplifier *simp;
        NodeFactory *nf;
        STPMgr *bm;
        const ASTNode ASTTrue, ASTFalse;

        bool searchXOR(const ASTNode& lhs, const ASTNode& rhs);
        bool searchTerm(const ASTNode& lhs, const ASTNode& rhs);

        ASTNode
        propagate(const ASTNode& a, ArrayTransformer*at);
        hash_set<int> alreadyVisited;

        const bool always_true;
    public:

        PropagateEqualities(Simplifier *simp_, NodeFactory *nf_, STPMgr *bm_) :
                ASTTrue(bm_->ASTTrue), ASTFalse(bm_->ASTFalse),
                always_true(bm_->UserFlags.isSet("always_true","1"))
        {
            simp = simp_;
            nf = nf_;
            bm = bm_;
        }

        ASTNode
        topLevel(const ASTNode& a, ArrayTransformer* at)
        {
          if (!bm->UserFlags.propagate_equalities)
              return a;

          bm->GetRunTimes()->start(RunTimes::PropagateEqualities);
          ASTNode result = propagate(a, at);
          bm->GetRunTimes()->stop(RunTimes::PropagateEqualities);
          return result;
        }

    };
}

#endif

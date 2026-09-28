/***********
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

#ifndef EMBEDDEDCONSTRAINTS_H
#define EMBEDDEDCONSTRAINTS_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{

// A top-level assertion is true everywhere, including where it appears
// inside another one.
//
// A query that asserts `p` and separately asserts something with `p` buried
// in it has said the same thing twice, and the second copy is dead weight:
// it is bit-blasted, it becomes CNF, and the solver rediscovers what the
// first copy already fixed. Replacing the embedded occurrence with `true`
// costs a walk and can collapse whatever was built over it.
//
// PropagateEqualities already does this for the shapes it recognises -- a
// bare Boolean symbol, an equality, a two-argument XOR. What it cannot take
// is an assertion that is anything else, and on the industrial bit-vector
// queries this is for that is most of them: of 11627 top-level assertions
// measured across forty such files, two were bare symbols. The rest were
// equalities, which PropagateEqualities does take, and some three thousand
// implications and inequalities, which nothing took.
//
// The assertion's own occurrence is never replaced. Each one is rebuilt from
// its *children*, so the top node keeps its identity -- substituting there
// would turn the assertion into `true` and drop the constraint, which is
// sound for a definition and emphatically not for a constraint. A negated
// assertion is unwrapped first for the same reason: `not p` maps p to false,
// and rebuilding it from its own child would erase it.
class DLL_PUBLIC EmbeddedConstraints
{
  STPMgr* bm;

public:
  explicit EmbeddedConstraints(STPMgr* bm_) : bm(bm_) {}

  // `input` unchanged when it is not a conjunction -- a lone assertion has
  // no siblings to be embedded in -- and otherwise with every embedded
  // occurrence of a sibling replaced by what that sibling says.
  ASTNode topLevel(const ASTNode& input);
};

} // namespace stp

#endif

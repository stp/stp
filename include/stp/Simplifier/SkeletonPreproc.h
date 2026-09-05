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

#ifndef SKELETONPREPROC_H
#define SKELETONPREPROC_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <unordered_map>
#include <vector>

namespace stp
{

// What the propositional structure of a query decides on its own.
//
// Every predicate over bit-vectors is replaced by a free Boolean variable
// and nothing else changes: the connectives keep their meaning, the atoms
// lose theirs. The result is implied by the query -- a model of the query
// gives every atom a value, and those values satisfy the skeleton -- so it
// is an over-approximation, and that is what makes this worth doing:
//
//   * an atom the skeleton forces is an atom the query forces, and can be
//     asserted at the top level, where the ordinary simplifier can act on
//     it and the bit-blaster is spared deriving it;
//
//   * a skeleton with no model at all means the query has none either.
//
// Neither direction can be run backwards. The skeleton is weaker than the
// query, so a *satisfiable* skeleton says nothing, and an atom it leaves
// free may still be forced by the arithmetic. Everything this reports is a
// one-way implication.
//
// The propositional problem is small -- it holds one variable per distinct
// predicate, against the hundreds of thousands of variables the same query
// bit-blasts to -- which is why asking a SAT solver about it is cheap
// enough to do before solving properly.
class DLL_PUBLIC SkeletonPreproc
{
  STPMgr* bm;

  // One variable per distinct predicate, and the way back.
  std::unordered_map<ASTNode, unsigned, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      atomToVar;
  std::vector<ASTNode> varToAtom;

  // Tseitin output for a subformula, as a literal in the 2*var+sign
  // encoding the SAT layer uses.
  std::unordered_map<ASTNode, int, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      litOf;

public:
  explicit SkeletonPreproc(STPMgr* bm_) : bm(bm_) {}

  // The facts the skeleton forces, as top-level formulas: an atom, or its
  // negation. `unsat` comes back true when the skeleton has no model, in
  // which case the query has none and the returned vector is empty.
  //
  // An empty vector with `unsat` false means the structure decides nothing,
  // which is the common case for a query whose difficulty is arithmetic.
  ASTVec derive(const ASTNode& input, bool& unsat);

  // Whether this node is one the skeleton keeps rather than abstracts: a
  // connective whose children are all Boolean. A predicate over
  // bit-vectors has bit-vector children and so becomes an atom, which is
  // the whole of the abstraction.
  static bool isConnective(const ASTNode& n);
};

} // namespace stp

#endif

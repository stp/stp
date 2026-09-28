/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: September, 2026
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

/*
 Common factor extraction.

 Multiplication distributes over addition modulo 2^w, so an operand that
 several of a sum's products all multiply by comes out of the sum:

    (x*a) + (x*b) + c  -->  (x*(a + b)) + c

 Every participant loses one multiplier and one is spent on the extracted
 factor, so k participants pay for k-1 multipliers, and the adders are the
 same either way: the sum loses k-1 operands and the new inner sum gains
 them. A multiplier is quadratic in the width where an adder is linear, so
 this is the largest of the sharing rewrites by what it removes.

 CommonSubSum is the same idea one level up -- it shares what two
 applications of one operator have in common -- but it cannot reach this:
 the shared thing here is a single operand rather than a pair, and it is
 shared between the operands of a sum rather than between two sums.

 Where the sum is an equality's side, the extraction is often the whole
 answer rather than a saving: a variable that occurs once outside the
 factored group is unconstrained once it is a factor of the sum, which is
 what makes (31*c1*c2*z + 31*c3*c4*z + ... = 0) satisfiable by inspection.

 Flatten is what makes this live, as it is for CommonSubSum. The rule in
 Rewriting.cpp fires on the binary spelling of the same shape -- two
 two-operand products under a two-operand sum -- and flattening widens
 both past what that rule accepts. Here the sum and the products are read
 as the operand lists they became.

 Sharing-aware, which is what keeps every extraction a strict improvement:
 a product is only taken apart when this sum is its single reference. One
 referenced anywhere else is built whatever this pass does, so reducing it
 would build the smaller product beside the one that stays -- a
 multiplication added rather than removed -- and a negated addend needs
 both of its nodes to be this sum's own. References are counted over the
 pass's input and carried across the rewrite, so an operand is judged by
 what holds it once its own children have been rewritten, and two operands
 that rewrite to one node are one node holding both their references.

 The sum itself may be shared: the rewrite replaces it, so every place that
 held it holds the factored form and the products still die. So may the
 factor, which is the operand being multiplied in once instead of several
 times whatever else it is used for.

 Negated products join in: -(x*b) is x*(-b), so an addend that negates a
 product contributes the negation of its remainder to the inner sum. This
 is what a subtraction of products arrives as -- the factory rewrites
 (p - q) to (p + -q) at creation, and pulls the negation out of a product
 to sit on top of it.
*/

#ifndef COMMONFACTOR_H_
#define COMMONFACTOR_H_

#include <ankerl/unordered_dense.h>
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include <map>

namespace stp
{

class CommonFactor
{
  STPMgr* stpMgr;
  NodeFactory* nf;

  // Multiplications removed, counting the one spent on each extracted
  // factor.
  long saved;

  // References to each node of the input, by node number, and the same for
  // the nodes the rewrite produces. A product is only reduced when it has
  // one reference: see the header comment. The rewritten map is what the
  // guard reads, because by the time a sum is reached its operands are
  // whatever their own children rewrote them into -- and two operands that
  // rewrite to one node are one node with both their references.
  ankerl::unordered_dense::map<uint64_t, uint32_t> refs;
  ankerl::unordered_dense::map<uint64_t, uint32_t> rewrittenRefs;

  void buildRefs(const ASTNode& n);

  // How many places hold this node. A node this pass built is held by the
  // one thing it was built for, unless it hash-conses onto a node of the
  // input, which the map answers for.
  uint32_t references(const ASTNode& n) const;

  // The product an addend contributes, and whether the addend negates it.
  // Absent when the addend is not a product, or is one that survives the
  // rewrite.
  struct Addend
  {
    ASTNode product;
    bool negated = false;
  };
  bool productOf(const ASTNode& addend, Addend& out) const;

  ASTNode without(const Addend& a, const ASTNode& factor, unsigned width);
  ASTNode sumOf(const ASTVec& addends, unsigned width);

  // One extraction: the operand that the most of these addends can give up,
  // taken out of all of them. False when no operand is shared by two.
  bool extractOne(ASTVec& addends, unsigned width);

  // Extractions until the operands share nothing, the inner sums included.
  bool extract(ASTVec& addends, unsigned width);

  ASTNode rewrite(const ASTNode& n);

public:
  CommonFactor(const CommonFactor&) = delete;
  CommonFactor& operator=(const CommonFactor&) = delete;

  CommonFactor(STPMgr* stp_, NodeFactory* nf_)
      : stpMgr(stp_), nf(nf_), saved(0)
  {
  }

  ASTNode topLevel(const ASTNode& n);

  // What the last run removed.
  long multipliesSaved() const { return saved; }
};
}

#endif

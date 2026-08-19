/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2010
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

/* A node factory that:
 *	    * Sorts children to increases sharing,
 *	    * Performs constant evaluation,
 *	    * Performs simplify boolean simplifications,
 *	    * Converts less thans to greater thans.
 *
 * NOTE: CreateNode/CreateTerm doesn't necessary return a node with the same Kind as what
 * it was called with. For example: (AND TRUE FALSE) will return FALSE. Which
 * isn't an AND node.
 *
 * We will never create the node (NOT(NOT x))
 * This is an example of a multi-level rule that won't increases the global
 * number of nodes. That is, you request the creation of an extra node, but
 * you are returned an (already existing) descendant node. If (NOT x) is not
 * used anywhere else, you requested a new node, and reduced the global count of 
 * nodes by 1. Because (NOT x) will be garbage collected if it's not used anywhere else.
 *
 *
 * There are some exceptions to this. NOTs are cheap, so when we convert comparisons
 * (for example), Creating BVSLT(x,y), will create NOT(BVGT(y,x)). i.e. it will 
 * create an extra node.
 *
 */

#ifndef SIMPLIFYINGNODEFACTORY_H
#define SIMPLIFYINGNODEFACTORY_H

#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/Attributes.h"

class DLL_PUBLIC SimplifyingNodeFactory : public NodeFactory
{

public:
  using NodeFactory::CreateArrayTerm;
  using NodeFactory::CreateNode;
  using NodeFactory::CreateTerm;

  virtual ASTNode CreateNode(Kind kind, ASTChildren children) override;
  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                             ASTChildren children) override;
  virtual std::string getName() override { return "simplifying"; }

  SimplifyingNodeFactory(NodeFactory& raw_, STPMgr& bm_)
      : NodeFactory(bm_), hashing(raw_), ASTTrue(bm_.ASTTrue),
        ASTFalse(bm_.ASTFalse), ASTUndefined(bm_.ASTUndefined){};
  ~SimplifyingNodeFactory() {}

  SimplifyingNodeFactory(const SimplifyingNodeFactory&) = delete;
  SimplifyingNodeFactory& operator=(const SimplifyingNodeFactory&) = delete;

  static ASTNode convertKnownShiftAmount(const Kind k,
                                         ASTChildren children, STPMgr& bm,
                                         NodeFactory* nf);
private:
  NodeFactory& hashing;

  const ASTNode& ASTTrue;
  const ASTNode& ASTFalse;
  const ASTNode& ASTUndefined;

  ASTNode CreateSimpleFormITE(ASTChildren children);
  ASTNode CreateSimpleXor(ASTChildren children);

  ASTNode CreateSimpleAndOr(bool IsAnd, ASTChildren children);
  ASTNode CreateSimpleAndOr(bool IsAnd, const ASTNode& form1, const ASTNode& form2);
  ASTNode handle_2_children(bool IsAnd, ASTChildren children);

  ASTNode CreateSimpleNot(const ASTNode& form);
  ASTNode CreateSimpleNot(ASTChildren children);

  ASTNode CreateSimpleEQ(ASTChildren children);
  ASTNode CreateSimpleEQConstConcat(const ASTNode& constant,
                                    const ASTNode& concat);

  ASTNode chaseRead(ASTChildren children, unsigned int width);

  // Push an extract down through the operators it passes through, in a loop.
  // Null if none of them applies.
  ASTNode narrowExtract(unsigned width, ASTChildren children);

  ASTNode simplifyArrayEquality(const ASTNode& a, const ASTNode& b);

  // A = write(A, i, v) becomes select(A, i) = v; Null otherwise.
  ASTNode selfStoreEquality(const ASTNode& a, const ASTNode& b);

  ASTNode plusRules(const ASTNode& n0, const ASTNode& n1);

  // Rebuild a remainder from the dividend and the "- b * (a / b)" product
  // that a plus was given. Null if the two do not have that shape.
  ASTNode remainderFromDivision(const ASTNode& a, const ASTNode& product);

  // One pass of the above over a sum's operands, replacing every dividend
  // and product pair it finds. True if it folded anything.
  bool foldRemainders(ASTVec& children);

  //Helper functions
  bool children_all_constants(ASTChildren children) const;
  ASTNode get_smallest_number(const unsigned width);
  ASTNode get_largest_number(const unsigned width);
  ASTNode handle_bvxor(unsigned int width, ASTChildren input_children);
  ASTNode handle_bvand(unsigned int width, ASTChildren children);
  ASTNode create_gt_node(ASTChildren children);

  // abs/neg of a constant float: clear (flip=false) or flip (flip=true) the
  // sign bit, keeping the rest of the packed bits and the format.
  ASTNode foldFPSign(const ASTNode& fpConst, bool flip);

  // The special constants of a format, for rules whose result is not one of
  // the operands: interning canonicalises the NaN.
  ASTNode makeFPNaN(unsigned eb, unsigned sb);
  ASTNode makeFPZero(unsigned eb, unsigned sb, bool negative);

  // The neighbouring value of a non-NaN float constant in its own format
  // (up = the next value above). Null for NaN.
  ASTNode fpConstAdjacent(const ASTNode& fpConst, bool up);

  // The wide constant rounded into (te, ts) toward +oo (up) or -oo, or
  // Null. Assertion builds and the DirectedNarrowing unit test hold the
  // result to the directed rounding's defining property.
  ASTNode narrowFPConstDirected(const ASTNode& c, unsigned te, unsigned ts,
                                bool up);

  // fp.gt / fp.geq over an exactly-widened operand: drop the widening(s),
  // moving a constant other side into the operand's format. Null when the
  // rule does not apply.
  ASTNode narrowWidenedFPComparison(Kind kind, const ASTNode& a,
                                    const ASTNode& b);

  ASTNode plusRules(ASTChildren oldChildren);
  ASTNode multRules(ASTChildren oldChildren);

};

#endif

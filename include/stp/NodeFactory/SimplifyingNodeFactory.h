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
  virtual ASTNode CreateNode(const Kind kind, const ASTVec& children) override;
  virtual ASTNode CreateTerm(const Kind kind, const unsigned int width, const ASTVec& children) override;
  virtual std::string getName() override { return "simplifying"; }

  SimplifyingNodeFactory(NodeFactory& raw_, STPMgr& bm_)
      : NodeFactory(bm_), hashing(raw_), ASTTrue(bm_.ASTTrue),
        ASTFalse(bm_.ASTFalse), ASTUndefined(bm_.ASTUndefined){};
  ~SimplifyingNodeFactory() {}

  SimplifyingNodeFactory(const SimplifyingNodeFactory&) = delete;
  SimplifyingNodeFactory& operator=(const SimplifyingNodeFactory&) = delete;

  static ASTNode convertKnownShiftAmount(const Kind k,
                                            const ASTVec& children, STPMgr& bm,
                                            NodeFactory* nf);
private:
  NodeFactory& hashing;

  const ASTNode& ASTTrue;
  const ASTNode& ASTFalse;
  const ASTNode& ASTUndefined;

  ASTNode CreateSimpleFormITE(const ASTVec& children);
  ASTNode CreateSimpleXor(const ASTVec& children);

  ASTNode CreateSimpleAndOr(bool IsAnd, const ASTVec& children);
  ASTNode CreateSimpleAndOr(bool IsAnd, const ASTNode& form1, const ASTNode& form2);
  ASTNode handle_2_children(bool IsAnd, const ASTVec& children);

  ASTNode CreateSimpleNot(const ASTNode& form);
  ASTNode CreateSimpleNot(const ASTVec& children);

  ASTNode CreateSimpleEQ(const ASTVec& children);


  ASTNode chaseRead(const ASTVec& children, unsigned int width);

  ASTNode plusRules(const ASTNode& n0, const ASTNode& n1);

  //Helper functions
  bool children_all_constants(const ASTVec& children) const;
  ASTNode get_smallest_number(const unsigned width);
  ASTNode get_largest_number(const unsigned width);
  ASTNode handle_bvxor(unsigned int width, const ASTVec& input_children);
  ASTNode handle_bvand(unsigned int width, const ASTVec& children);
  ASTNode create_gt_node(const ASTVec& children);

};

#endif

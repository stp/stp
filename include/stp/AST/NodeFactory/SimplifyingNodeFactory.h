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
 *	    * performs simplify boolean simplifications,
 *	    * converts less thans to greater thans.
 *
 * NOTE: CreateNode doesn't necessary return a node with the same Kind as what
 * it was called with. For example: (AND TRUE FALSE) will return FALSE. Which
 * isn't an AND node.
 *
 * The intention is to never create nodes that will later be simplified by
 * single level re-write rules. So we will never create the node (NOT(NOT x))
 * This is an example of a multi-level rule that never increases the global
 * number of nodes.
 *
 * BUG: below are two different, contradictory claims.
 * 1) These rules never increase the total number of nodes.  They are complimented
 * by multi-level re-write rules that consider the global reference count when
 * simplifying.
 *
 * 2) These rules (mostly) don't increase the total number of nodes by more than
 * one.
 *
 * Sometimes the number of nodes is increased. e.g. creating BVSLT(x,y), will
 * create NOT(BVGT(y,x)). i.e. it will create an extra node.
 *
 * I think we've got all the two input cases that either map to a constant, or
 * to an input value. e.g.
 * (a >> a), (a xor a), (a or a), (a and a), (a + 0), (a-0)..
 */

#ifndef SIMPLIFYINGNODEFACTORY_H
#define SIMPLIFYINGNODEFACTORY_H

#include "stp/AST/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/Attributes.h"

class SimplifyingNodeFactory : public NodeFactory
{

public:
  DLL_PUBLIC virtual ASTNode CreateNode(Kind kind, const ASTVec& children);
  DLL_PUBLIC virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                                        const ASTVec& children);

  DLL_PUBLIC virtual std::string getName() { return "simplifying"; }

  DLL_PUBLIC SimplifyingNodeFactory(NodeFactory& raw_, STPMgr& bm_)
      : NodeFactory(bm_), hashing(raw_), ASTTrue(bm_.ASTTrue),
        ASTFalse(bm_.ASTFalse), ASTUndefined(bm_.ASTUndefined){};
  DLL_PUBLIC ~SimplifyingNodeFactory() {}

private:
  SimplifyingNodeFactory(const SimplifyingNodeFactory&);
  NodeFactory& hashing;

  const ASTNode& ASTTrue;
  const ASTNode& ASTFalse;
  const ASTNode& ASTUndefined;

  ASTNode CreateSimpleFormITE(const ASTVec& children);
  ASTNode CreateSimpleXor(const ASTVec& children);

  ASTNode CreateSimpleAndOr(bool IsAnd, const ASTVec& children);
  ASTNode CreateSimpleAndOr(bool IsAnd, const ASTNode& form1,
                            const ASTNode& form2);
  ASTNode handle_2_children(bool IsAnd, const ASTVec& children);

  ASTNode CreateSimpleNot(const ASTNode& form);
  ASTNode CreateSimpleNot(const ASTVec& children);

  ASTNode CreateSimpleEQ(const ASTVec& children);

  SimplifyingNodeFactory& operator=(const SimplifyingNodeFactory&);

  ASTNode chaseRead(const ASTVec& children, unsigned int width);

  ASTNode plusRules(const ASTNode& n0, const ASTNode& n1);

  //Helper functions
  bool children_all_constants(const ASTVec& children) const;
  ASTNode get_smallest_number(const unsigned width);
  ASTNode get_largest_number(const unsigned width);
  void handle_bvand(Kind kind, unsigned int width, const ASTVec& children,
                    ASTNode& result);
  ASTNode create_gt_node(const ASTVec& children);
};

#endif

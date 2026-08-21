/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2010
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

#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/STPManager/STP.h"

using namespace stp;

HashingNodeFactory::~HashingNodeFactory()
{
}

// Get structurally hashed version of the node.
ASTNode HashingNodeFactory::CreateNode(const Kind kind,
                                       const ASTChildren back_children)
{
  if (kind == UF_APPLY)
  {
    std::string error;
    UFContext* context = bm.getUFContextIfAny();
    if (context == NULL ||
        !context->validateApplicationChildren(back_children, &error))
      FatalError(("UF_APPLY: " + error).c_str());
  }

  // We can't create NOT(NOT (..)) nodes because of how the numbering scheme we
  // use works. So you can't trust the hashing node factory even to return
  // nodes of the same kind that you ask for.
  if (kind == NOT && back_children[0].GetKind() == NOT)
  {
    return back_children[0][0];
  }

  // Array equality: every front end's node creation bottoms out here. Keep
  // the operands visible in an opaque node until query construction and
  // function/let substitution are complete; TopLevelSTPAux lowers ARRAY_EQ
  // before any ordinary preprocessing can encounter it.
  const bool array_eq_from_source =
      kind == EQ && back_children.size() == 2 &&
      back_children[0].GetIndexWidth() > 0;
  if (array_eq_from_source || kind == ARRAY_EQ)
  {
    if (back_children.size() != 2)
      FatalError("array-equality: expected exactly two operands");

    if (array_eq_from_source && !bm.UserFlags.enable_array_equality)
      FatalError("STP cannot decide equality between whole array terms "
                 "without --array-equality (the C API's vc_setFlag(vc, "
                 "'x'), or Solver(array_equality=True) in Python).");

    if (back_children[0].GetType() != ARRAY_TYPE ||
        back_children[1].GetType() != ARRAY_TYPE ||
        back_children[0].GetIndexWidth() !=
            back_children[1].GetIndexWidth() ||
        back_children[0].GetValueWidth() !=
            back_children[1].GetValueWidth())
      FatalError("array-equality: operands must have identical index and "
                 "element widths");

    const SourceSort left_sort = back_children[0].GetSourceSort();
    const SourceSort right_sort = back_children[1].GetSourceSort();
    if (left_sort.kind() != SourceSort::Kind::Array ||
        right_sort.kind() != SourceSort::Kind::Array ||
        left_sort != right_sort)
      FatalError("array-equality: operands must have identical source sorts");

    if (array_eq_from_source)
      return CreateNode(ARRAY_EQ, back_children);
  }
  
  if (back_children.size()  <= 1 || !isCommutative(kind))
  {
    // Don't create a new vector if it won't be sorted.
    ASTNode result(bm.LookupOrCreateInterior(kind, back_children));
    if (kind == UF_APPLY)
      bm.getUFContext()->noteApplication(result);
    return result;
  }
  else if (is_Form_kind(kind)) // formula and commutative.
  {
    const bool isSorted =  std::is_sorted(back_children.begin(),back_children.end(),stp::ExprLess{});
    if (isSorted)
    {
      ASTNode result(bm.LookupOrCreateInterior(kind, back_children));
      if (kind == UF_APPLY)
        bm.getUFContext()->noteApplication(result);
      return result;
    }

    ASTVec sorted_children(back_children.begin(), back_children.end());
    SortByExprNum(sorted_children);
    ASTNode result(bm.LookupOrCreateInterior(kind, sorted_children));
    if (kind == UF_APPLY)
      bm.getUFContext()->noteApplication(result);
    return result;
  }
  else
  {
    if (std::is_sorted(back_children.begin(), back_children.end(),
                       stp::ArithLess{}))
    {
      // Don't create a new vector if it's already sorted.
      ASTNode result(bm.LookupOrCreateInterior(kind, back_children));
      if (kind == UF_APPLY)
        bm.getUFContext()->noteApplication(result);
      return result;
    }

    ASTVec children(back_children.begin(), back_children.end());
    // The Bitvector solver seems to expect constants on the RHS, variables on the
    // LHS.
    SortByArith(children);

    ASTNode result(bm.LookupOrCreateInterior(kind, children));
    if (kind == UF_APPLY)
      bm.getUFContext()->noteApplication(result);
    return result;
  }
}

// Create and return an ASTNode for a term
ASTNode HashingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                       const ASTChildren children)
{
  ASTNode n = CreateNode(kind, children);
  n.SetValueWidth(width);

  // by default we assume that the term is a Bitvector. If
  // necessary the indexwidth can be changed later
  n.SetIndexWidth(0);
  return n;
}

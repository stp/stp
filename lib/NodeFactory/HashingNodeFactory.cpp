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

#include <sstream>

using namespace stp;

namespace {

bool isRealOperator(Kind kind)
{
  switch (kind)
  {
    case REAL_ADD:
    case REAL_SUB:
    case REAL_NEG:
    case REAL_MUL:
    case REAL_DIV:
    case REAL_LT:
    case REAL_LE:
    case REAL_GT:
    case REAL_GE:
      return true;
    default:
      return false;
  }
}

// The Real kinds whose value is determined by concrete operands.  The
// comparisons are left out: they are predicates, and STPMgr::CreateRealTerm
// takes arithmetic only.
bool isFoldableRealArithmetic(Kind kind)
{
  switch (kind)
  {
    case REAL_ADD:
    case REAL_SUB:
    case REAL_NEG:
    case REAL_MUL:
    case REAL_DIV:
      return true;
    default:
      return false;
  }
}

bool allRealConstants(ASTChildren children)
{
  if (children.empty())
    return false;
  for (const ASTNode& child : children)
    if (child.GetKind() != REAL_CONST)
      return false;
  return true;
}

std::string realOperatorSignature(Kind kind, ASTChildren children)
{
  std::ostringstream out;
  out << _kind_names[kind] << '(';
  for (std::size_t i = 0; i < children.size(); ++i)
  {
    if (i != 0)
      out << ", ";
    out << children[i].GetSourceSort();
  }
  return out.str() + ')';
}

[[noreturn]] void invalidRealOperator(Kind kind, ASTChildren children,
                                      const char* detail)
{
  const std::string diagnostic =
      "Real operator " + realOperatorSignature(kind, children) + ": " +
      detail;
  stp::FatalError(diagnostic.c_str());
}

void validateRealOperator(Kind kind, ASTChildren children)
{
  const size_t degree = children.size();
  const bool arity_ok =
      (kind == REAL_ADD && degree >= 2) ||
      (kind == REAL_SUB && degree >= 1) ||
      (kind == REAL_NEG && degree == 1) ||
      ((kind == REAL_MUL || kind == REAL_DIV || kind == REAL_LT ||
        kind == REAL_LE || kind == REAL_GT || kind == REAL_GE) &&
       degree == 2);
  if (!arity_ok)
    invalidRealOperator(kind, children, "invalid arity");

  for (const ASTNode& child : children)
  {
    if (child.GetSourceSort().kind() != SourceSort::Kind::Real)
      invalidRealOperator(kind, children,
                          "every operand must have mathematical Real sort");
  }

  // Linearity is the requirement, so what has to be refused is a product of
  // two symbolic operands.  A product of two constants is a constant, and
  // CreateNode folds it before reaching here, which is why this asks for an
  // exact coefficient rather than for exactly one.  STPMgr::CreateRealTerm
  // states the same rule the same way.
  if (kind == REAL_MUL && children[0].GetKind() != REAL_CONST &&
      children[1].GetKind() != REAL_CONST)
    invalidRealOperator(kind, children,
                        "multiplication requires an exact concrete "
                        "coefficient");
  if (kind == REAL_DIV)
  {
    if (children[1].GetKind() != REAL_CONST)
      invalidRealOperator(kind, children,
                          "division requires an exact concrete divisor");
    if (children[1].GetRealCanonical() == "0")
      invalidRealOperator(kind, children, "division by exact zero");
  }
}

} // namespace

HashingNodeFactory::~HashingNodeFactory()
{
}

// Get structurally hashed version of the node.
ASTNode HashingNodeFactory::CreateNode(const Kind kind,
                                       const ASTChildren back_children)
{
  if (kind == DISTINCT)
  {
    if (back_children.size() < 2)
      FatalError("distinct: expected at least two operands");

    const SourceSort sort = back_children[0].GetSourceSort();
    if (!sort.isKnown())
      FatalError("distinct: operands must have a known source sort");
    for (size_t i = 1; i < back_children.size(); ++i)
      if (back_children[i].GetSourceSort() != sort)
        FatalError("distinct: operands must have identical source sorts");

    // Lowering an array-valued distinct creates whole-array equalities, so
    // enforce the same public option at construction time as source `=`.
    if (sort.kind() == SourceSort::Kind::Array &&
        !bm.UserFlags.enable_array_equality)
      FatalError("STP cannot decide equality between whole array terms "
                 "without --array-equality (the C API's vc_setFlag(vc, "
                 "'x'), or Solver(array_equality=True) in Python).");

    bm.noteDistinct();
  }

  if (kind == UF_APPLY)
  {
    std::string error;
    UFContext* context = bm.getUFContextIfAny();
    if (context == NULL ||
        !context->validateApplicationChildren(back_children, &error))
      FatalError(("UF_APPLY: " + error).c_str());
  }
  if (kind == REAL_CONST)
    stp::FatalError("REAL_CONST is a private exact leaf; use CreateRealConst");

  if (isRealOperator(kind))
  {
    for (const ASTNode& child : back_children)
      if (child.GetSTPMgr() != &bm)
        stp::FatalError(
            "Real operator received an operand owned by another manager");

    // Concrete arithmetic folds to a constant rather than being built as a
    // term.  The frontend already folds what it parses, but a node can also
    // be rebuilt here from children a rewrite has since made concrete --
    // SubstitutionMap::replace putting a literal where a symbol was is the
    // way it happens -- and the result has to be the same node either way.
    // Without this, a product whose coefficient and operand are both
    // concrete reaches validateRealOperator as a REAL_MUL of two constants,
    // which is neither buildable nor a linearity violation.
    //
    // CreateRealTerm owns the arithmetic, the number budget and the
    // interning.  It is safe against recursion for exactly the argument
    // that makes this correct: it only calls back into a node factory when
    // its operands are not all concrete, which is the case this excludes.
    if (isFoldableRealArithmetic(kind) && allRealConstants(back_children))
      return bm.CreateRealTerm(kind, ASTVec(back_children.begin(),
                                            back_children.end()));

    validateRealOperator(kind, back_children);
  }

  if (kind == EQ && back_children.size() == 2)
  {
    const SourceSort left = back_children[0].GetSourceSort();
    const SourceSort right = back_children[1].GetSourceSort();
    if ((left.kind() == SourceSort::Kind::Real ||
         right.kind() == SourceSort::Kind::Real) &&
        (back_children[0].GetSTPMgr() != &bm ||
         back_children[1].GetSTPMgr() != &bm))
      stp::FatalError(
          "Real equality received an operand owned by another manager");
    if ((left.kind() == SourceSort::Kind::Real ||
         right.kind() == SourceSort::Kind::Real) &&
        (left != SourceSort::real() || right != SourceSort::real()))
    {
      const std::string diagnostic =
          "Real operator =( " + left.name() + ", " + right.name() +
          "): equality requires two operands of mathematical Real sort";
      stp::FatalError(diagnostic.c_str());
    }
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
      back_children[0].GetSourceSort().kind() == SourceSort::Kind::Array;
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

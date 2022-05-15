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

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Simplifier/Simplifier.h"
#include <cassert>
#include <cmath>

using stp::Kind;

using stp::SYMBOL;
using stp::BVNOT;
using stp::BVMOD;
using stp::BVUMINUS;
using stp::BVMULT;
using stp::ITE;
using stp::EQ;
using stp::BVSRSHIFT;
using stp::SBVREM;
using stp::SBVMOD;
using stp::SBVDIV;
using stp::BVCONCAT;
using stp::BVEXTRACT;
using stp::BVRIGHTSHIFT;
using stp::BVPLUS;
using stp::BVXOR;
using stp::BVDIV;

using std::cout;
using std::endl;

static bool debug_simplifyingNodeFactory = false;

bool SimplifyingNodeFactory::children_all_constants(
    const ASTVec& children) const
{
  for (unsigned i = 0; i < children.size(); i++)
  {
    if (!children[i].isConstant())
    {
      return false;
    }
  }

  return true;
}

ASTNode SimplifyingNodeFactory::get_smallest_number(const unsigned width)
{
  // 1000000000 (most negative number.)
  stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Bit_On(max, width - 1);
  return bm.CreateBVConst(max, width);
}

ASTNode SimplifyingNodeFactory::get_largest_number(const unsigned width)
{
  // 011111111 (most positive number.)
  stp::CBV max = CONSTANTBV::BitVector_Create(width, false);
  CONSTANTBV::BitVector_Fill(max);
  CONSTANTBV::BitVector_Bit_Off(max, width - 1);
  return bm.CreateBVConst(max, width);
}

ASTNode SimplifyingNodeFactory::create_gt_node(const ASTVec& children)
{
  if (children[0] == children[1])
  {
    return ASTFalse;
  }

  if (children[0].isConstant() &&
      CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
  {
    return ASTFalse;
  }

  if (children[1].isConstant() &&
      CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
  {
    return ASTFalse;
  }

  if (children[0].GetKind() == BVRIGHTSHIFT && children[0][0] == children[1])
  {
    return ASTFalse;
  }

  ASTNode result;

  //2nd part is the same ->only care about 1st part
  if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT &&
      children[0][1] == children[1][1])
  {
    result = NodeFactory::CreateNode(stp::BVGT, children[0][0], children[1][0]);
  }

  //1st part is the same ->only care about 2nd part
  if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT &&
      children[0][0] == children[1][0])
  {
    result = NodeFactory::CreateNode(stp::BVGT, children[0][1], children[1][1]);
  }

  // 1 > x -> (x ==0)
  if (children[0].isConstant() && CreateOneConst(children[0].GetValueWidth())== children[0])
  {
    result = NodeFactory::CreateNode(stp::EQ, NodeFactory::CreateZeroConst(children[0].GetValueWidth()), children[1] );
  }


  //If child 1 is constant, GT == NOT EQ
  if (children[1].isConstant() &&
      CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
  {
    result = NodeFactory::CreateNode(
        stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
  }

  //If child 0 is constant, GT == NOT EQ
  if (children[0].isConstant() &&
      CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
  {
    result = NodeFactory::CreateNode(
        stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
  }

  if (children[0].GetKind() == stp::BVAND && children[0].Degree() > 1 &&
      ((children[0][0] == children[1]) || children[0][1] == children[1]))
  {
    return ASTFalse;
  }

  return result;
}

ASTNode SimplifyingNodeFactory::CreateNode(Kind kind, const ASTVec& children)
{
  assert(kind != SYMBOL);
  // These are created specially.

  // If all the parameters are constant, return the constant value.
  // The bitblaster calls CreateNode with a boolean vector. We don't try to
  // simplify those.
  if (kind != stp::UNDEFINED && kind != stp::BOOLEAN &&
      kind != stp::BITVECTOR && kind != stp::ARRAY &&
      children_all_constants(children))
  {
    const ASTNode& hash = hashing.CreateNode(kind, children);
    const ASTNode& c = NonMemberBVConstEvaluator(&bm, hash);
    assert(c.isConstant());
    return c;
  }

  ASTNode result;
  switch (kind)
  {
    // convert the Less thans to greater thans.
    case stp::BVLT:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVGT, children[1], children[0]);
      break;

    case stp::BVLE:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVGE, children[1], children[0]);
      break;

    case stp::BVSLT:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVSGT, children[1], children[0]);
      break;

    case stp::BVSLE:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVSGE, children[1], children[0]);
      break;

    case stp::BVSGT:
      assert(children.size() == 2);
      if (children[0] == children[1])
        result = ASTFalse;

      if (children[1].GetKind() == stp::BVCONST)
      {
        const unsigned width = children[0].GetValueWidth();
        if (children[1] == get_largest_number(width))
          result = ASTFalse;
      }

      if (children[0].GetKind() == stp::BVCONST)
      {
        const unsigned width = children[0].GetValueWidth();
        if (children[0] == get_smallest_number(width))
          result = ASTFalse;
      }

      //2nd part is the same -> only care about 1st part
      if (children[0].GetKind() == BVCONCAT &&
          children[1].GetKind() == BVCONCAT && children[0][1] == children[1][1])
      {
        result =
            NodeFactory::CreateNode(stp::BVSGT, children[0][0], children[1][0]);
      }

      break;

    case stp::BVGT:
      assert(children.size() == 2);
      result = create_gt_node(children);
      break;

    case stp::BVGE:
    {
      assert(children.size() == 2);
      ASTNode a = NodeFactory::CreateNode(stp::BVGT, children[1], children[0]);
      result = NodeFactory::CreateNode(stp::NOT, a);
    }
    break;

    case stp::BVSGE:
    {
      assert(children.size() == 2);
      ASTNode a = NodeFactory::CreateNode(stp::BVSGT, children[1], children[0]);
      result = NodeFactory::CreateNode(stp::NOT, a);
    }
    break;

    case stp::NOT:
      result = CreateSimpleNot(children);
      break;
    case stp::AND:
      result = CreateSimpleAndOr(1, children);
      break;
    case stp::OR:
      result = CreateSimpleAndOr(0, children);
      break;
    case stp::NAND:
      result = CreateSimpleNot(CreateSimpleAndOr(1, children));
      break;
    case stp::NOR:
      result = CreateSimpleNot(CreateSimpleAndOr(0, children));
      break;
    case stp::XOR:
      result = CreateSimpleXor(children);
      break;
    case ITE:
      result = CreateSimpleFormITE(children);
      break;
    case EQ:
      result = CreateSimpleEQ(children);
      break;
    case stp::IFF:
    {
      assert(children.size() == 2);
      ASTVec newCh;
      newCh.reserve(2);
      result = CreateSimpleXor(children);
      result = CreateSimpleNot(result);
      break;
    }
    case stp::IMPLIES:
    {
      assert(children.size() == 2);
      if (children[0] == children[1])
      {
        result = bm.ASTTrue;
      }
      else
      {
        ASTVec newCh;
        newCh.reserve(2);
        newCh.push_back(CreateSimpleNot(children[0]));
        newCh.push_back(children[1]);
        result = CreateSimpleAndOr(0, newCh);
      }
      break;
    }

    default:
      result = hashing.CreateNode(kind, children);
  }

  if (result.IsNull())
    result = hashing.CreateNode(kind, children);

  return result;
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTNode& form)
{
  const Kind k = form.GetKind();
  switch (k)
  {
    case stp::FALSE:
    {
      return ASTTrue;
    }
    case stp::TRUE:
    {
      return ASTFalse;
    }
    case stp::NOT:
    {
      // NOT NOT cancellation
      return form[0];
    }
    default:
    {
      ASTVec children;
      children.push_back(form);
      return hashing.CreateNode(stp::NOT, children);
    }
  }
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTVec& children)
{
  assert(children.size() == 1);
  const Kind k = children[0].GetKind();
  switch (k)
  {
    case stp::FALSE:
    {
      return ASTTrue;
    }
    case stp::TRUE:
    {
      return ASTFalse;
    }
    case stp::NOT:
    {
      // NOT NOT cancellation
      return children[0][0];
    }
    default:
    {
      return hashing.CreateNode(stp::NOT, children);
    }
  }
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
                                                  const ASTNode& form1,
                                                  const ASTNode& form2)
{
  ASTVec children;
  children.push_back(form1);
  children.push_back(form2);
  return CreateSimpleAndOr(IsAnd, children);
}

ASTNode SimplifyingNodeFactory::handle_2_children(bool IsAnd,
                                                  const ASTVec& children)
{
  if (children.size() == 2)
  {
    const Kind k = IsAnd ? stp::AND : stp::OR;
    const ASTNode& c0 = children[0];
    const ASTNode& c1 = children[1];

    if (k == stp::OR)
    {
      //case of a || ~a which is constant TRUE

      if (c0.GetKind() == stp::NOT && c0[0] == c1)
        return ASTTrue;
      if (c1.GetKind() == stp::NOT && c1[0] == c0)
        return ASTTrue;
    }
    else
    {
      assert(k == stp::AND);
      //case of a && ~a which is constant FALSE

      if (c0.GetKind() == stp::NOT && c0[0] == c1)
        return ASTFalse;
      if (c1.GetKind() == stp::NOT && c1[0] == c0)
        return ASTFalse;
    }
  }
  return ASTUndefined;
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
                                                  const ASTVec& c)
{
  ASTNode retval = handle_2_children(IsAnd, c);
  if (retval != ASTUndefined)
    return retval;

  const ASTNode& annihilator = (IsAnd ? ASTFalse : ASTTrue);
  const ASTNode& identity = (IsAnd ? ASTTrue : ASTFalse);

  // Sorting these can be expensive, so we only sort it if it's not already sorted.
  bool isSorted =  std::is_sorted(c.begin(),c.end(),stp::exprless);
  ASTVec sorted_children;
  const ASTVec& children = isSorted ? c: sorted_children;
  if (!isSorted)
  {
    sorted_children = c;
    SortByExprNum(sorted_children);  
  }

  //TODO this would be better as copy on write.
  ASTVec new_children;
  new_children.reserve(children.size());

  for (ASTVec::const_iterator it = children.begin(), it_end = children.end();
       it != it_end; it++)
  {
    ASTVec::const_iterator next_it;

    const bool nextexists = (it + 1 < it_end);
    if (nextexists)
      next_it = it + 1;
    else
      next_it = it_end;

    if (nextexists)
      if (next_it->GetKind() == stp::NOT && (*next_it)[0] == *it)
        return annihilator;

    if (*it == annihilator)
    {
      return annihilator;
    }
    else if (*it == identity || (nextexists && (*next_it == *it)))
    {
      // just drop it
    }
    else
    {
      new_children.push_back(*it);
    }
  }

  // If we get here, we saw no annihilators, and children should
  // be only the non-True nodes.
  switch (new_children.size())
  {
    case 0:
      return identity;
      break;

    case 1:
      return new_children[0];
      break;

    default:
      // 2 or more children.  Create a new node.
      return hashing.CreateNode(IsAnd ? stp::AND : stp::OR, new_children);
      break;
  }
  assert(false);
  exit(-1);
}

// Tries to simplify the input to TRUE/FALSE. if it fails, then
// return the constructed equality
ASTNode SimplifyingNodeFactory::CreateSimpleEQ(const ASTVec& children)
{
  assert(children.size() == 2);

  // SYMBOL = something, if not that, then CONSTANT =
  const bool swap = (children[1].GetKind() == stp::SYMBOL ||
                     ((children[0].GetKind() != stp::SYMBOL) &&
                      children[1].GetKind() == stp::BVCONST));
  const ASTNode& in1 = swap ? children[1] : children[0];
  const ASTNode& in2 = swap ? children[0] : children[1];
  const Kind k1 = in1.GetKind();
  const Kind k2 = in2.GetKind();
  const int width = in1.GetValueWidth();

  if (in1 == in2)
    // terms are syntactically the same
    return ASTTrue;

  // here the terms are definitely not syntactically equal but may be
  // semantically equal.
  if (stp::BVCONST == k1 && stp::BVCONST == k2)
    return ASTFalse;

  if ((k1 == BVNOT && k2 == BVNOT) || (k1 == BVUMINUS && k2 == BVUMINUS))
    return NodeFactory::CreateNode(EQ, in1[0], in2[0]);

  if ((k1 == BVUMINUS && k2 == stp::BVCONST) ||
      (k1 == BVNOT && k2 == stp::BVCONST))
    return NodeFactory::CreateNode(EQ, in1[0],
                                   NodeFactory::CreateTerm(k1, width, in2));

  if ((k2 == BVUMINUS && k1 == stp::BVCONST) ||
      (k2 == BVNOT && k1 == stp::BVCONST))
    return NodeFactory::CreateNode(EQ, in2[0],
                                   NodeFactory::CreateTerm(k2, width, in1));

  if ((k1 == BVNOT && in1[0] == in2) || (k2 == BVNOT && in2[0] == in1))
    return ASTFalse;

  if (k2 == stp::BVDIV && k1 == stp::BVCONST &&
      (in1 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(stp::BVGT, in2[1], in2[0]);

  if (k1 == stp::BVDIV && k2 == stp::BVCONST &&
      (in2 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(stp::BVGT, in1[1], in1[0]);

  // split the constant to equal each part of the concat.
  if (BVCONCAT == k2 && stp::BVCONST == k1)
  {
    int low_b = 0;
    int high_b = (int)in2[1].GetValueWidth() - 1;
    int low_t = in2[1].GetValueWidth();
    int high_t = width - 1;

    ASTNode c0 = NodeFactory::CreateTerm(BVEXTRACT, in2[1].GetValueWidth(), in1,
                                         bm.CreateBVConst(32, high_b),
                                         bm.CreateBVConst(32, low_b));
    ASTNode c1 = NodeFactory::CreateTerm(BVEXTRACT, in2[0].GetValueWidth(), in1,
                                         bm.CreateBVConst(32, high_t),
                                         bm.CreateBVConst(32, low_t));

    ASTNode a = NodeFactory::CreateNode(EQ, in2[1], c0);
    ASTNode b = NodeFactory::CreateNode(EQ, in2[0], c1);
    return NodeFactory::CreateNode(stp::AND, a, b);
  }

  // This increases the number of nodes. So disable for now.
  if (false && BVCONCAT == k1 && BVCONCAT == k2 &&
      in1[0].GetValueWidth() == in2[0].GetValueWidth())
  {
    ASTNode a = NodeFactory::CreateNode(EQ, in1[0], in2[0]);
    ASTNode b = NodeFactory::CreateNode(EQ, in1[1], in2[1]);
    return NodeFactory::CreateNode(stp::AND, a, b);
  }

  if (k1 == stp::BVCONST && k2 == ITE && in2[1].GetKind() == stp::BVCONST &&
      in2[2].GetKind() == stp::BVCONST)
  {

    ASTNode result = NodeFactory::CreateNode(
        ITE, in2[0], NodeFactory::CreateNode(EQ, in1, in2[1]),
        NodeFactory::CreateNode(EQ, in1, in2[2]));

    return result;
  }

  // Don't create a PLUS with the same operand on both sides.
  // We don't do big pluses, because 1) this algorithm isn't good enough
  // 2) it might split nodes (a lot).
  if ((k1 == BVPLUS && in1.Degree() <= 2) ||
      (k2 == BVPLUS && in2.Degree() <= 2))
  {
    const ASTVec& c1 = (k1 == BVPLUS) ? in1.GetChildren() : ASTVec(1, in1);
    const ASTVec& c2 = (k2 == BVPLUS) ? in2.GetChildren() : ASTVec(1, in2);

    if (c1.size() <= 2 && c2.size() <= 2)
    {
      int match1 = -1, match2 = -1;

      for (size_t i = 0, c1Size = c1.size(); i < c1Size; ++i)
      {
        for (size_t j = 0, c2Size = c2.size(); j < c2Size; ++j)
        {
          if (c1[i] == c2[j])
          {
            match1 = i;
            match2 = j;
          }
        }
      }

      if (match1 != -1)
      {
        assert(match2 != -1);
        assert(match1 == 0 || match1 == 1);
        assert(match2 == 0 || match2 == 1);
        // If it was 1 element before, it's zero now.
        ASTNode n1 = c1.size() == 1 ? bm.CreateZeroConst(width)
                                    : c1[match1 == 0 ? 1 : 0];
        ASTNode n2 = c2.size() == 1 ? bm.CreateZeroConst(width)
                                    : c2[match2 == 0 ? 1 : 0];
        return NodeFactory::CreateNode(EQ, n1, n2);
      }
    }
  }

  if (k2 == BVPLUS && in2.Degree() == 2 && (in2[1] == in1 || in2[0] == in1))
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width),
                                   in2[1] == in1 ? in2[0] : in2[1]);
  }

  if (k1 == BVPLUS && in1.Degree() == 2 && (in1[1] == in2 || in1[0] == in2))
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width),
                                   in1[1] == in2 ? in1[0] : in1[1]);
  }

  if (k1 == stp::BVCONST && k2 == stp::BVXOR && in2.Degree() == 2 &&
      in2[0].GetKind() == stp::BVCONST)
  {
    return NodeFactory::CreateNode(
        EQ, NodeFactory::CreateTerm(stp::BVXOR, width, in1, in2[0]), in2[1]);
  }

  if (k2 == stp::BVCONST && k1 == stp::BVXOR && in1.Degree() == 2 &&
      in1[0].GetKind() == stp::BVCONST)
  {
    return NodeFactory::CreateNode(
        EQ, NodeFactory::CreateTerm(stp::BVXOR, width, in2, in1[0]), in1[1]);
  }

  if (k2 == stp::BVXOR && in2.Degree() == 2 && in1 == in2[0])
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in2[1]);
  }

  if (k1 == stp::BVXOR && in1.Degree() == 2 && in2 == in1[0])
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in1[1]);
  }

  if (k1 == stp::BVCONST && k2 == stp::BVSX &&
      (in2[0].GetValueWidth() != (unsigned)width))
  {
    // Each of the bits in the extended part, and one into the un-extended part
    // must be the same.
    bool foundZero = false, foundOne = false;
    const int original_width = in2[0].GetValueWidth();
    const int new_width = in2.GetValueWidth();

    for (int i = original_width - 1; i < new_width; i++)
    {
      if (CONSTANTBV::BitVector_bit_test(in1.GetBVConst(), i))
        foundOne = true;
      else
        foundZero = true;
    }

    if (foundZero && foundOne)
      return ASTFalse;

    ASTNode lhs = NodeFactory::CreateTerm(
        BVEXTRACT, original_width, in1,
        bm.CreateBVConst(32, original_width - 1), bm.CreateZeroConst(32));
    ASTNode rhs = NodeFactory::CreateTerm(
        BVEXTRACT, original_width, in2,
        bm.CreateBVConst(32, original_width - 1), bm.CreateZeroConst(32));

    return NodeFactory::CreateNode(EQ, lhs, rhs);
  }

  // Simplifiy (5 = 4/x) to FALSE.
  if (k1 == stp::BVCONST && k2 == stp::BVDIV &&
      in2[0].GetKind() == stp::BVCONST)
  {
    ASTNode maxV = bm.CreateMaxConst(width);
    if (CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(),
                                          maxV.GetBVConst()) != 0 &&
        CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(),
                                          in2[0].GetBVConst()) > 0)
    {
      return ASTFalse;
    }
  }

  if (k1 == BVNOT && k2 == BVUMINUS && in1[0] == in2[0])
    return ASTFalse;

  if (k1 == BVUMINUS && k2 == BVNOT && in1[0] == in2[0])
    return ASTFalse;

  // last resort is to CreateNode
  return hashing.CreateNode(EQ, children);
}

// Constant children are accumulated in "accumconst".
ASTNode SimplifyingNodeFactory::CreateSimpleXor(const ASTVec& children)
{
  if (debug_simplifyingNodeFactory)
  {
    cout << "========" << endl << "CreateSimpXor ";

    lpvec(children);
    cout << endl;
  }

  ASTVec flat_children; // empty vector
  flat_children = children;

  // sort so that identical nodes occur in sequential runs, followed by
  // their negations.
  SortByExprNum(flat_children);

  // This is the C Boolean value of all constant args seen.  It is initially
  // 0.  TRUE children cause it to change value.
  bool accumconst = 0;

  ASTVec new_children;
  new_children.reserve(children.size());

  const ASTVec::const_iterator it_end = flat_children.end();
  ASTVec::iterator next_it;
  for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
  {
    next_it = it + 1;
    bool nextexists = (next_it < it_end);

    if (ASTTrue == *it)
    {
      accumconst = !accumconst;
    }
    else if (ASTFalse == *it)
    {
      // Ignore it
    }
    else if (nextexists && (*next_it == *it))
    {
      // x XOR x = FALSE.  Skip current, write "false" into next_it
      // so that it gets tossed, too.
      *next_it = ASTFalse;
    }
    else if (nextexists && (next_it->GetKind() == stp::NOT) &&
             ((*next_it)[0] == *it))
    {
      // x XOR NOT x = TRUE.  Skip current, write "true" into next_it
      // so that it gets tossed, too.
      *next_it = ASTTrue;
    }
    else if (stp::NOT == it->GetKind())
    {
      // If child is (NOT alpha), we can flip accumconst and use alpha.
      // This is ok because (NOT alpha) == TRUE XOR alpha
      accumconst = !accumconst;
      // CreateSimpNot just takes child of not.
      new_children.push_back(CreateSimpleNot(*it));
    }
    else
    {
      new_children.push_back(*it);
    }
  }

  ASTNode retval;

  // Children should be non-constant.
  if (new_children.size() < 2)
  {
    if (0 == new_children.size())
    {
      // XOR(TRUE, FALSE) -- accumconst will be 1.
      if (accumconst)
      {
        retval = ASTTrue;
      }
      else
      {
        retval = ASTFalse;
      }
    }
    else
    {
      // there is just one child
      // XOR(x, TRUE) -- accumconst will be 1.
      if (accumconst)
      {
        retval = CreateSimpleNot(new_children[0]);
      }
      else
      {
        retval = new_children[0];
      }
    }
  }
  else
  {
    retval = hashing.CreateNode(stp::XOR, new_children);

    // negate the result if accumulated negation
    if (accumconst)
    {
      retval = CreateSimpleNot(retval);
    }
  }

  if (debug_simplifyingNodeFactory)
  {
    cout << "returns " << retval << endl;
  }
  return retval;
}

ASTNode SimplifyingNodeFactory::CreateSimpleFormITE(const ASTVec& children)
{
  const ASTNode& child0 = children[0];
  const ASTNode& child1 = children[1];
  const ASTNode& child2 = children[2];

  ASTNode retval;

  if (debug_simplifyingNodeFactory)
  {
    cout << "========" << endl
         << "CreateSimpleFormITE " << child0 << child1 << child2 << endl;
  }

  if (ASTTrue == child0)
  {
    retval = child1;
  }
  else if (ASTFalse == child0)
  {
    retval = child2;
  }
  else if (child1 == child2)
  {
    retval = child1;
  }
  // ITE(x, TRUE, y ) == x OR y
  else if (ASTTrue == child1)
  {
    retval = CreateSimpleAndOr(0, child0, child2);
  }
  // ITE(x, FALSE, y ) == (!x AND y)
  else if (ASTFalse == child1)
  {
    retval = CreateSimpleAndOr(1, CreateSimpleNot(child0), child2);
  }
  // ITE(x, y, TRUE ) == (!x OR y)
  else if (ASTTrue == child2)
  {
    retval = CreateSimpleAndOr(0, CreateSimpleNot(child0), child1);
  }
  // ITE(x, y, FALSE ) == (x AND y)
  else if (ASTFalse == child2)
  {
    retval = CreateSimpleAndOr(1, child0, child1);
  }
  else if (child0 == child1)
  {
    retval = CreateSimpleAndOr(0, child0, child2);
  }
  else if (child0 == child2)
  {
    retval = CreateSimpleAndOr(1, child0, child1);
  }
  else
  {
    retval = hashing.CreateNode(ITE, children);
  }

  if (debug_simplifyingNodeFactory)
  {
    cout << "returns " << retval << endl;
  }

  return retval;
}

// Move reads down through writes until, either we hit a write to an identical
// (syntactically) index,
// or we hit a write to an index that might be the same. This is intended to
// simplify things like:
// read(write(write(A,1,2),2,3),4) cheaply.
// The "children" that are passed should be the children of a READ.
ASTNode SimplifyingNodeFactory::chaseRead(const ASTVec& children,
                                          unsigned int width)
{
  assert(children[0].GetKind() == stp::WRITE);
  const ASTNode& readIndex = children[1];
  ASTNode write = children[0];

  const bool read_is_const = (stp::BVCONST == readIndex.GetKind());
  ASTVec c(2);

  while (write.GetKind() == stp::WRITE)
  {
    const ASTNode& write_index = write[1];

    if (readIndex == write_index)
    {
      // The are definately the same.
      // cerr << "-";
      return write[2];
    }
    else if (read_is_const && stp::BVCONST == write_index.GetKind())
    {
      // They are definately different. Ignore this.
      // cerr << "+";
    }
    else
    {
      // They may be the same. Exit.
      // We've finished the cheap tests, now do the expensive one.
      // I don't know if the cost of this justifies the benefit.
      // cerr << "#";
      c[0] = write_index;
      c[1] = readIndex;
      ASTNode n = CreateSimpleEQ(c);
      if (n == ASTTrue)
      {
        // cerr << "#";
        return write[2];
      }
      else if (n == ASTFalse)
      {
        // cerr << "!";
      }
      else
      {
        // cerr << "."
        // Perhaps they are the same, perhaps not.
        break;
      }
    }
    write = write[0];
  }
  return hashing.CreateTerm(stp::READ, width, write, readIndex);
}

// This gets called with the arguments swapped as well. So the rules don't need
// to know about commutivity.
ASTNode SimplifyingNodeFactory::plusRules(const ASTNode& n0, const ASTNode& n1)
{
  ASTNode result;
  const int width = n0.GetValueWidth();

  if (n0.isConstant() && CONSTANTBV::BitVector_is_empty(n0.GetBVConst()))
    result = n1;
  else if (width == 1 && n0 == n1)
    result = bm.CreateZeroConst(1);
  else if (n0 == n1)
    result = NodeFactory::CreateTerm(
        stp::BVMULT, width, bm.CreateBVConst(std::string("2"), 10, width), n0);
  else if (n0.GetKind() == BVUMINUS && n1 == n0[0])
    result = bm.CreateZeroConst(width);
  else if (n1.GetKind() == BVPLUS && n1[1].GetKind() == BVUMINUS &&
           n0 == n1[1][0] && n1.Degree() == 2)
    result = n1[0];
  else if (n1.GetKind() == BVPLUS && n1[0].GetKind() == BVUMINUS &&
           n0 == n1[0][0] && n1.Degree() == 2)
    result = n1[1];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS &&
           n0.Degree() == 2 && n1[0] == n0[1])
    result = n0[0];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS &&
           n0.Degree() == 2 && n1[0] == n0[0])
    result = n0[1];
  else if (n1.GetKind() == BVNOT && n1[0] == n0)
    result = bm.CreateMaxConst(width);
  else if (n0.GetKind() == stp::BVCONST && n1.GetKind() == BVPLUS &&
           n1.Degree() == 2 && n1[0].GetKind() == stp::BVCONST)
  {
    ASTVec ch;
    ch.push_back(n0);
    ch.push_back(n1[0]);
    ASTNode constant = NonMemberBVConstEvaluator(&bm, BVPLUS, ch, width);
    result = NodeFactory::CreateTerm(BVPLUS, width, constant, n1[1]);
  }
  else if (false && n1.GetKind() == BVUMINUS &&
           (n0.isConstant() && CONSTANTBV::BitVector_is_full(n0.GetBVConst())))
  {
    result = NodeFactory::CreateTerm(BVNOT, width, n1[0]);
  }
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVUMINUS)
  {
    ASTNode r = NodeFactory::CreateTerm(BVPLUS, width, n0[0], n1[0]);
    result = NodeFactory::CreateTerm(BVUMINUS, width, r);
  }

  return result;
}

ASTNode SimplifyingNodeFactory::handle_bvxor(unsigned int width, const ASTVec& input_children) 
{
  bool accum = false;

  const ASTNode zero = bm.CreateZeroConst(width);

  ASTVec flat_children(input_children);

  // Expression numbers don't place BVNOT(t) next to (t), so strip BVNOTS first..
  for (size_t i = 0; i < flat_children.size();i++)
  {
  
    if (BVNOT == flat_children[i].GetKind())
    {
      accum = !accum;
      flat_children[i] = flat_children[i][0]; // remove the BVNOT
    }
  }

  // sort so that identical nodes occur in sequential runs
  SortByExprNum(flat_children);

  ASTVec new_children;
  new_children.reserve(flat_children.size());

  ASTNode accumulate= bm.CreateZeroConst(width);

  const ASTVec::iterator it_end = flat_children.end();
  ASTVec::iterator next_it;

  for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
  {
    next_it = it + 1;
    bool nextexists = (next_it < it_end);

    if (it->isConstant())
    {
        accumulate= bm.CreateTerm(BVXOR, width, accumulate, *it);
    }
    else if (nextexists && (*next_it == *it))
    {
      // x XOR x = FALSE.  Skip current, write "false" into next_it
      // so that it gets tossed, too.
      *next_it = zero;
    } 
    else
    {
      new_children.push_back(*it);
    }
  }

  if (CONSTANTBV::BitVector_bit_test(accumulate.GetBVConst(),0))
  {
    // Aribtrarily we make constants even.
    accumulate= bm.CreateTerm(BVNOT, width, accumulate);
    accum = !accum;
  }

  if (!CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
  {
    new_children.push_back(accumulate);
  }

  ASTNode retval;

  if (0 == new_children.size())
  {
      retval = zero;
  }
  else if (new_children.size() ==1)
  {
      retval = new_children[0];
  }
  else 
  {
      retval = hashing.CreateTerm(BVXOR, width, new_children);
  }

  // negate the result if accumulated negation
  if (accum)
  {
      retval = NodeFactory::CreateTerm(BVNOT,width,retval);
  }

  return retval;
}



ASTNode SimplifyingNodeFactory::handle_bvand(unsigned int width, const ASTVec& new_children) 
{

  ASTVec flat_children(new_children);
  SortByExprNum(flat_children); // We want duplicates to be adjacent.

  const ASTNode annihilator = bm.CreateZeroConst(width);
  const ASTNode identity = bm.CreateMaxConst(width);
  ASTNode accumulator = bm.CreateMaxConst(width);

  ASTVec children;
  children.reserve(flat_children.size());

  stp::ASTNodeSet found;

  for (ASTVec::const_iterator it = flat_children.begin(), it_end = flat_children.end(); it != it_end; it++)
  {
    ASTVec::const_iterator next_it;

    const bool nextexists = (it + 1 < it_end);
    if (nextexists)
      next_it = it + 1;
    else
      next_it = it_end;

    if (it->isConstant())
    {
      accumulator = NodeFactory::CreateTerm(stp::BVAND, width, *it, accumulator);
    }
    else if (nextexists && (*next_it == *it))
    {
      // just drop it
    }
    else if (it->GetKind()== stp::BVNOT && (found.find((*it)[0]) != found.end()))
    {
       return annihilator;
    }
    else
    {
       found.insert(*it);
       children.push_back(*it);
    }
  }

  if (accumulator == identity)
  {
    // discard
  } 
  else  if (accumulator == annihilator)
  {
    return annihilator;
  } 
  else
  {
       children.push_back(accumulator);
  }

  // If we get here, we saw no annihilators, and children should
  // be only the non-True nodes.
  switch(children.size()) {
    case 0:
      return identity;
      break;

    case 1:
      return children[0];
      break;
  }


  // ites with same
  if (children.size() ==2 && children[0].GetKind() == stp::ITE && children[1].GetKind() == stp::ITE && children[0][0] == children[1][0])
    if (NodeFactory::CreateTerm(stp::BVAND,width, children[0][1],children[1][1]).isConstant() || NodeFactory::CreateTerm(stp::BVAND,width, children[0][2],children[1][2]).isConstant())
      {
      return NodeFactory::CreateTerm(stp::ITE,width,children[0][0], 
        NodeFactory::CreateTerm(stp::BVAND,width, children[0][1],children[1][1]), 
        NodeFactory::CreateTerm(stp::BVAND,width, children[0][2],children[1][2]));
      }


  // If there is just one run of 1 bits, replace by an extract and a concat.
  // i.e. 00011111111000000 & x , will be replaced by an extract of x just
  // where
  // there are one bits.
  if (false && children.size() == 2 &&
      (children[0].isConstant() || children[1].isConstant()))
  {
    ASTNode c0 = children[0];
    ASTNode c1 = children[1];
    if (c1.isConstant())
    {
      ASTNode t = c0;
      c0 = c1;
      c1 = t;
    }

    int start = -1;
    int end = -1;
    stp::CBV c = c0.GetBVConst();
    bool bad = false;
    for (int i = 0; i < (int)width; i++)
    {
      if (CONSTANTBV::BitVector_bit_test(c, i))
      {
        if (start == -1)
          start = i; // first one bit.
        else if (end != -1)
          bad = true;
      }

      if (!CONSTANTBV::BitVector_bit_test(c, i))
      {
        if (start != -1 && end == -1)
          end = i - 1; // end of run.
      }
    }
    if (start != -1 && end == -1)
      end = (int)width - 1;

    if (!bad && start != -1)
    {
      assert(end != -1);

      ASTNode result = NodeFactory::CreateTerm(BVEXTRACT, end - start + 1, c1,
                                       bm.CreateBVConst(32, end),
                                       bm.CreateBVConst(32, start));

      if (start > 0)
      {
        ASTNode z = bm.CreateZeroConst(start);
        result = NodeFactory::CreateTerm(BVCONCAT, end + 1, result, z);
      }
      if (end < (int)width - 1)
      {
        ASTNode z = bm.CreateZeroConst((int)width - end - 1);
        result =  NodeFactory::CreateTerm(BVCONCAT, width, z, result);
      }
      return result;
    }
  }

  if (children.size() ==2 && children[1].GetKind() == stp::BVAND && children[0] == children[1][0])
  {
    return children[1];
  }

  //(bvand (bvnot |w|) (bvnot (bvand |v| |w|)))) )  
  // -> (bvnot |w|)
  if (children.size() ==2 && 
      children[0].GetKind() == stp::BVNOT && 
      children[1].GetKind() == stp::BVNOT && 
      children[1][0].GetKind() == stp::BVAND &&
      children[1][0].Degree() ==2 &&
      children[1][0][1] == children[0][0] 
    )
  {
    return children[0];
  }

  return hashing.CreateTerm(stp::BVAND,width,children);
}

ASTNode SimplifyingNodeFactory::plusRules(const ASTVec& oldChildren)
{
  assert(oldChildren.size() > 2);
  const unsigned width = oldChildren[0].GetValueWidth();

  ASTNode accumulate= bm.CreateZeroConst(width);

  stp::ASTNodeMultiSet bvnot, bvneg, other;

  int constantsFound = 0;
  
  // create multi-sets of relevant kinds.
  for (const auto & n : oldChildren)
  {
      if (n.GetKind() == BVNOT)
        bvnot.insert(n);
      else if (n.GetKind() == BVUMINUS)
        bvneg.insert(n);
      else if (n.GetKind() == stp::BVCONST)
        {
          accumulate = NodeFactory::CreateTerm(BVPLUS, width, accumulate, n);
          constantsFound++;
        }
      else
        other.insert(n);
  }

  bool changed = (constantsFound > 1);

  // negation cancels out.
  for (const auto& n : bvneg)
  {
    if (other.find(n[0]) != other.end())
      {
        other.erase(other.find(n[0]));
        changed = true;
      }
    else
      other.insert(n); 
  }

  // "not" reduces to -1.
  for (const auto& n : bvnot)
  {
    if (other.find(n[0]) != other.end())
    {
      other.erase(other.find(n[0]));
      accumulate = NodeFactory::CreateTerm(BVPLUS, width, accumulate, bm.CreateMaxConst(width));
      changed = true;
    }  
    else
      other.insert(n);   
  }

  // If a zero constant was initially present, it has changed.
  if (constantsFound > 0 && CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
    changed = true;

  if (!changed)
    return hashing.CreateTerm(BVPLUS, width, oldChildren); 

  if (!CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
     other.insert(accumulate);

  ASTVec newChildren(other.begin(), other.end());

  ASTNode result;
  if (newChildren.size() >2)
    result = hashing.CreateTerm(BVPLUS, width, newChildren);
  else if (newChildren.size() ==2)
    result = CreateTerm(BVPLUS, width, newChildren); // has been modified. Call more comprehensive.
  else if (newChildren.size() ==1)
    result = newChildren[0];
  else if (newChildren.size() ==0)
    result = bm.CreateZeroConst(width);

  return result;
}


// If the shift is bigger than the bitwidth, replace by an extract.
ASTNode convertArithmeticKnownShiftAmount(const Kind k,
                                                      const ASTVec& children,
                                                      STPMgr& bm,
                                                      NodeFactory* nf)
{
  const ASTNode a = children[0];
  const ASTNode b = children[1];
  const unsigned width = children[0].GetValueWidth();
  ASTNode output;

  assert(b.isConstant());
  assert(k == BVSRSHIFT);

  if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + std::log2(width))
  {
    ASTNode top = bm.CreateBVConst(32, width - 1);
    return nf->CreateTerm(stp::BVSX, width,
                          nf->CreateTerm(stp::BVEXTRACT, 1, children[0], top, top),
                          bm.CreateBVConst(32, width));
  }
  else
  {
    if (b.GetUnsignedConst() >= width)
    {
      ASTNode top = bm.CreateBVConst(32, width - 1);
      return nf->CreateTerm(stp::BVSX, width,
                            nf->CreateTerm(BVEXTRACT, 1, children[0], top, top),
                            bm.CreateBVConst(32, width));
    }
    else
    {
      ASTNode top = bm.CreateBVConst(32, width - 1);
      ASTNode bottom = bm.CreateBVConst(32, b.GetUnsignedConst());

      return nf->CreateTerm(stp::BVSX, width,
                            nf->CreateTerm(stp::BVEXTRACT,
                                           width - b.GetUnsignedConst(),
                                           children[0], top, bottom),
                            bm.CreateBVConst(32, width));
    }
  }

  return ASTNode();
}

// If the rhs of a left or right shift is known.
ASTNode SimplifyingNodeFactory::convertKnownShiftAmount(const Kind k,
                                            const ASTVec& children, STPMgr& bm,
                                            NodeFactory* nf)
{
  const ASTNode a = children[0];
  const ASTNode b = children[1];
  const unsigned width = children[0].GetValueWidth();
  ASTNode output;

  assert(b.isConstant());
  assert(stp::BVLEFTSHIFT== k || BVRIGHTSHIFT == k);

  if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + std::log2(width))
  {
    // Intended to remove shifts by very large amounts
    // that don't fit into the unsigned.  at thhe start
    // of the "else" branch.
    output = bm.CreateZeroConst(width);
  }
  else
  {
    const unsigned int shift = b.GetUnsignedConst();
    if (shift >= width)
    {
      output = bm.CreateZeroConst(width);
    }
    else if (shift == 0)
    {
      output = a; // unchanged.
    }
    else
    {
      if (stp::BVLEFTSHIFT == k)
      {
        stp::CBV cbv = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Bit_On(cbv, shift);
        ASTNode c = bm.CreateBVConst(cbv, width);

        output = nf->CreateTerm(BVMULT, width, a, c);
        BVTypeCheck(output);
        // cout << output;
        // cout << a << b << endl;
      }
      else 
      {
        assert(k == BVRIGHTSHIFT);
        ASTNode zero = bm.CreateZeroConst(shift);
        ASTNode hi = bm.CreateBVConst(32, width - 1);
        ASTNode low = bm.CreateBVConst(32, shift);
        ASTNode extract = nf->CreateTerm(BVEXTRACT, width - shift, a, hi, low);
        BVTypeCheck(extract);
        output = nf->CreateTerm(BVCONCAT, width, zero, extract);
        BVTypeCheck(output);
      }
    }
  }
  return output;
}

ASTNode SimplifyingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                           const ASTVec& children)
{
  if (!is_Term_kind(kind))
    FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);

  assert(kind != stp::BVCONST);
  // These are created specially.
  assert(kind != stp::SYMBOL);
  // so are these.

  assert(bm.hashingNodeFactory == &hashing);

  // If all the parameters are constant, return the constant value.
  if (children_all_constants(children))
  {
    const ASTNode& hash = hashing.CreateTerm(kind, width, children);
    const ASTNode& c = NonMemberBVConstEvaluator(&bm, hash);
    assert(c.isConstant());
    return c;
  }

  ASTNode result;
  switch (kind)
  {
    case stp::BVZX:
    {
      if (width - children[0].GetValueWidth() > 0)
      {
        ASTNode zero = bm.CreateZeroConst(width - children[0].GetValueWidth());
        result = NodeFactory::CreateTerm(BVCONCAT, width, zero, children[0]);
      }
      else if (width == children[0].GetValueWidth())
      {
        result = children[0];
      }
      else
      {
        FatalError("Negative zero extend", children[0]);
      }
      break;
    }

    case ITE:
    {
      if (children[0] == ASTTrue)
        result = children[1];
      else if (children[0] == ASTFalse)
        result = children[2];
      else if (children[1] == children[2])
        result = children[1];
      else if (children[2].GetKind() == ITE && (children[2][0] == children[0]))
      {
        if (stp::ARRAY_TYPE == children[2].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[2].GetIndexWidth(), children[2].GetValueWidth(),
              children[0], children[1], children[2][2]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0], children[1],
                                           children[2][2]);
      }
      else if (children[1].GetKind() == ITE && (children[1][0] == children[0]))
      {
        if (stp::ARRAY_TYPE == children[1].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[1].GetIndexWidth(), children[1].GetValueWidth(),
              children[0], children[1][1], children[2]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0],
                                           children[1][1], children[2]);
      }
      else if (children[0].GetKind() == stp::NOT)
      {
        if (stp::ARRAY_TYPE == children[1].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[1].GetIndexWidth(), children[1].GetValueWidth(),
              children[0][0], children[2], children[1]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0][0],
                                           children[2], children[1]);
      }
      else if (children[0].GetKind() == EQ && children[0][1] == children[1] &&
               children[0][0].GetKind() == stp::BVCONST &&
               children[0][1].GetKind() != stp::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0],
                                         children[0][0], children[2]);
      else if (children[0].GetKind() == EQ && children[0][0] == children[1] &&
               children[0][1].GetKind() == stp::BVCONST &&
               children[0][0].GetKind() != stp::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0],
                                         children[0][1], children[2]);
      break;
    }

    case stp::BVMULT:
    {
      if (children.size() == 2)
      {
        if (children[0].isConstant() &&
            CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
          result = bm.CreateZeroConst(width);

        else if (children[1].isConstant() &&
                 CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
          result = bm.CreateZeroConst(width);

        else if (children[1].isConstant() &&
                 children[1] == bm.CreateOneConst(width))
          result = children[0];

        else if (children[0].isConstant() &&
                 children[0] == bm.CreateOneConst(width))
          result = children[1];

        else if (children[0].isConstant() &&
                 CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
          result = NodeFactory::CreateTerm(BVUMINUS, width, children[1]);

        else if (width == 1 && children[0] == children[1])
          result = children[0];

        else if (children[0].GetKind() == BVUMINUS &&
                 children[1].GetKind() == BVUMINUS)
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[0][0],
                                           children[1][0]);
        else if (children[0].GetKind() == BVUMINUS)
        {
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[0][0],
                                           children[1]);
          result = NodeFactory::CreateTerm(BVUMINUS, width, result);
        }
        else if (children[1].GetKind() == BVUMINUS)
        {
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[1][0],
                                           children[0]);
          result = NodeFactory::CreateTerm(BVUMINUS, width, result);
        }
      }
      else if (children.size() > 2)
      {
        // Never create multiplications with arity > 2.

        std::deque<ASTNode> names;

        for (unsigned i = 0; i < children.size(); i++)
          names.push_back(children[i]);

        sort(names.begin(), names.end(), stp::exprless);

        while (names.size() > 1)
        {
          ASTNode a = names.front();
          names.pop_front();

          ASTNode b = names.front();
          names.pop_front();

          ASTNode n = NodeFactory::CreateTerm(BVMULT, a.GetValueWidth(), a, b);
          names.push_back(n);
        }
        result = names.front();
      }
    }
    break;

    case stp::BVLEFTSHIFT:
    {
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = convertKnownShiftAmount(kind, children, bm,
                                                          &hashing);
      else if (width == 1 && children[0] == children[1])
        result = bm.CreateZeroConst(1);
      else if (children[0].GetKind() == BVUMINUS)
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(stp::BVLEFTSHIFT, width, children[0][0],
                                    children[1]));
    }
    break;

    case BVRIGHTSHIFT:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = convertKnownShiftAmount(kind, children, bm,
                                                          &hashing);
      else if (children[0].isConstant() &&
               children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            children[0], bm.CreateZeroConst(width));
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1] == children[0][0])
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width,
                                         bm.CreateMaxConst(width),
                                         children[0][0]); // 320 -> 170
      else if (width >= 3 && children[1].GetKind() == BVNOT &&
               children[1][0] == children[0])
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width,
                                         bm.CreateMaxConst(width),
                                         children[1]); // 320 -> 170
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                ITE, width, NodeFactory::CreateNode(
                                EQ, bm.CreateZeroConst(width), children[0][0]),
                bm.CreateOneConst(width),
                bm.CreateZeroConst(width))); // 391 -> 70
    }
    break;

    case stp::BVSRSHIFT:
    {
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (width > 1 && children[0].isConstant() &&
               children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            children[0], bm.CreateZeroConst(width));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
        result = bm.CreateMaxConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (width == 1 && children[0] == children[1])
        result = children[0];
      else if ((children[0] == children[1]) ||
               (children[0].GetKind() == BVUMINUS &&
                children[0][0] == children[1]))
      {
        assert(width > 1);
        ASTNode extract = NodeFactory::CreateTerm(
            BVEXTRACT, 1, children[0], bm.CreateBVConst(32, width - 1),
            bm.CreateBVConst(32, width - 1));
        result = NodeFactory::CreateTerm(stp::BVSX, width, extract,
                                         bm.CreateBVConst(32, width));
      }
      else if (width == 1 && children[1].isConstant() &&
               children[1] == bm.CreateOneConst(1))
        result = children[0];
      else if (children[1].isConstant())
        result = convertArithmeticKnownShiftAmount(
            kind, children, bm, &hashing);
      else if (children[1].GetKind() == BVUMINUS &&
               children[0] == children[1][0])
        result = NodeFactory::CreateTerm(stp::BVSRSHIFT, width, children[0],
                                         children[1][0]);
      else if (children[0].isConstant() &&
               !CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(),
                                               width - 1))
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width, children[0],
                                         children[1]);
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(BVSRSHIFT, width, children[0],
                                         children[0][0]); // 414 -> 361
      else if (children[0].GetKind() == BVNOT)
        result = NodeFactory::CreateTerm(
            BVNOT, width, NodeFactory::CreateTerm(BVSRSHIFT, width,
                                                  children[0][0], children[1]));
    }
    break;

    case stp::BVSUB:
      if (children.size() == 2)
      {
        if (children.size() == 2 && children[0] == children[1])
        {
          result = bm.CreateZeroConst(width);
        }
        else if (children.size() == 2 &&
                 children[1] == bm.CreateZeroConst(width))
        {
          result = children[0];
        }
        else
        {
          result = NodeFactory::CreateTerm(
              BVPLUS, width, children[0],
              NodeFactory::CreateTerm(BVUMINUS, width, children[1]));
        }
      }
      break;

    case stp::BVOR:
    {
     ASTVec new_children;
     new_children.reserve(children.size());
     for (size_t i = 0; i < children.size(); i++)
     {
         new_children.push_back(NodeFactory::CreateTerm(BVNOT, width, children[i]));
     }
     result = NodeFactory::CreateTerm(BVNOT, width, NodeFactory::CreateTerm(stp::BVAND,width,new_children));
    }
    break;

    case stp::BVXOR:
    {
      result = handle_bvxor(width, children);
      break;
    }

    case stp::BVAND:
    {
      result = handle_bvand(width, children);
      break;
    }

    case stp::BVSX:
    {
      if (width == children[0].GetValueWidth())
      {
        result = children[0];
      }
      break;
    }

    case BVNOT:
      if (children[0].GetKind() == BVNOT)
        result = children[0][0];
      if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
          children[0][0].GetKind() == stp::BVCONST &&
          children[0][0] == bm.CreateMaxConst(width))
        result = NodeFactory::CreateTerm(BVUMINUS, width, children[0][1]);
      if (children[0].GetKind() == BVUMINUS)
        result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0],
                                         bm.CreateMaxConst(width));
      if (children[0].GetKind() == BVMOD && children[0][0].GetKind() == BVNOT &&
          children[0][1].GetKind() == BVUMINUS &&
          children[0][1][0] == children[0][0][0])
        result = children[0][0][0];

      break;

    case BVUMINUS:
      if (children[0].GetKind() == BVUMINUS)
        result = children[0][0];
      else if (width == 1)
        result = children[0];
      else if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
               children[0][0].GetKind() == stp::BVCONST &&
               children[0][0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(BVNOT, width, children[0][1]);
      else if (children[0].GetKind() == BVNOT)
        result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0],
                                         bm.CreateOneConst(width));
      else if (children[0].GetKind() == stp::BVSX &&
               children[0][0].GetValueWidth() == 1)
        result = NodeFactory::CreateTerm(
            BVCONCAT, width, bm.CreateZeroConst(width - 1), children[0][0]);
      else if (children[0].GetKind() == BVMULT && children[0].Degree() == 2 &&
               children[0][0] == bm.CreateMaxConst(width))
        result = children[0][1];
      break;

    case BVEXTRACT:
      if (width == children[0].GetValueWidth())
        result = children[0];
      else if (BVEXTRACT ==
               children[0].GetKind()) // reduce an extract over an extract.
      {
        const unsigned outerLow = children[2].GetUnsignedConst();
        const unsigned outerHigh = children[1].GetUnsignedConst();

        const unsigned innerLow = children[0][2].GetUnsignedConst();
        // const unsigned innerHigh = children[0][1].GetUnsignedConst();
        result =
            NodeFactory::CreateTerm(BVEXTRACT, width, children[0][0],
                                    bm.CreateBVConst(32, outerHigh + innerLow),
                                    bm.CreateBVConst(32, outerLow + innerLow));
      }
      else if (BVCONCAT == children[0].GetKind())
      {
        // If the extract doesn't cross the concat, then remove the concat.
        const ASTNode& a = children[0][0];
        const ASTNode& b = children[0][1];

        const unsigned low = children[2].GetUnsignedConst();
        const unsigned high = children[1].GetUnsignedConst();

        if (high <
            b.GetValueWidth()) // Extract entirely from the lower value (b).
        {
          result = NodeFactory::CreateTerm(BVEXTRACT, width, b, children[1],
                                           children[2]);
        }
        if (low >=
            b.GetValueWidth()) // Extract entirely from the upper value (a).
        {
          ASTNode i = bm.CreateBVConst(32, high - b.GetValueWidth());
          ASTNode j = bm.CreateBVConst(32, low - b.GetValueWidth());
          result = NodeFactory::CreateTerm(BVEXTRACT, width, a, i, j);
        }
      }
      else if (BVUMINUS == children[0].GetKind() &&
               children[1] == bm.CreateZeroConst(children[1].GetValueWidth()) &&
               children[2] == bm.CreateZeroConst(children[2].GetValueWidth()))
      {
        result = NodeFactory::CreateTerm(BVEXTRACT, width, children[0][0],
                                         children[1], children[2]);
      }
      break;

    case BVPLUS:
      if (1 == width)
        result = handle_bvxor(width, children);
      else if (children.size() == 2)
      {
        result = plusRules(children[0], children[1]);
        if (result.IsNull())
          result = plusRules(children[1], children[0]);
      }
     else
          result = plusRules(children);
      break;

    case SBVMOD:
    {
      const ASTNode max = bm.CreateMaxConst(width);

      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               children[1] == bm.CreateOneConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               children[1] == bm.CreateMaxConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[0].isConstant() &&
               children[0] == bm.CreateZeroConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[0].GetKind() == BVUMINUS &&
               children[0][0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0])
        result = bm.CreateZeroConst(width);
#if 0
    else if ( width >= 4 && children[0].GetKind() == BVNOT && children[1] == children[0][0] )
      result = bm.CreateTerm(SBVMOD,width,max,children[0][0]);//9759 -> 542 | 4842 ms
    else if ( width >= 4 && children[1].GetKind() == BVNOT && children[1][0] == children[0] )
      result =  bm.CreateTerm(SBVMOD,width,max,children[1]);//9759 -> 542 | 4005 ms
    else if ( width >= 4 &&  children[0].GetKind() == BVNOT && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0] )
      result =  bm.CreateTerm(SBVMOD,width,max,children[1]);//9807 -> 674 | 2962 ms
#endif
    }

    break;

    case stp::BVDIV:
      if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
        result = children[0];
      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_bit_test(children[1].GetBVConst(), width - 1))
      {
        // We are dividing by something that has a one in the MSB. It's either 1
        // or zero.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(stp::BVGE, children[0], children[1]),
            bm.CreateOneConst(width), bm.CreateZeroConst(width));
      }
      else if (children[1].isConstant() &&
               children[1] == bm.CreateZeroConst(width))
        result = bm.CreateMaxConst(width);
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            bm.CreateMaxConst(width), bm.CreateZeroConst(width));

      break;

    case SBVDIV:
      if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
        result = children[0];
      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
        result = NodeFactory::CreateTerm(BVUMINUS, width, children[0]);
      break;

    case SBVREM:
    {
      const ASTNode one = bm.CreateOneConst(width);
      const ASTNode zero = bm.CreateZeroConst(width);
      const ASTNode max = bm.CreateMaxConst(width);

      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (children[1].isConstant() &&
               bm.CreateOneConst(width) == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].GetKind() == BVUMINUS)
        result =
            NodeFactory::CreateTerm(SBVREM, width, children[0], children[1][0]);
      else if (children[0].GetKind() == BVUMINUS &&
               children[0][0] == children[1])
        result = bm.CreateZeroConst(width);
#if 0
    else if ( width >= 4 &&  children[0].GetKind() == BVNOT && children[1] == children[0][0] )
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVMOD,width,one,children[0][0]));//9350 -> 624 | 3072 ms
    else if ( width >= 4 &&  children[1].GetKind() == BVNOT && children[1][0] == children[0] )
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVMOD,width,one,children[1]));//9350 -> 624 | 2402 ms
    else if ( width >= 4 &&  children[0].GetKind() == BVUMINUS && children[1] == max)
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVREM,width,children[0][0],children[1]));//123 -> 83 | 1600 ms
#endif
    }

    break;

    case BVMOD:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);

      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);

      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];

      if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
          children[0][0] == bm.CreateMaxConst(width) &&
          children[1] == children[0][1])
        result = children[0];

      const ASTNode one = bm.CreateOneConst(width);

      if (children[0].GetKind() == BVNOT && children[1].GetKind() == BVUMINUS &&
          children[1][0] == children[0][0])
        result = children[0];

      if (children[1].isConstant() && children[1] == one)
        result = bm.CreateZeroConst(width);

      if (children[0].isConstant() && children[0] == one)
        result = NodeFactory::CreateTerm(
            ITE, width, NodeFactory::CreateNode(EQ, children[1], one),
            bm.CreateZeroConst(width), one);
#if 0
      if ( width >= 3 && children[0].GetKind() == BVNOT && children[1] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVMOD,width,bm.CreateMaxConst(width),children[0][0]);//3285 -> 3113

      if ( width >= 3 && children[1].GetKind() == BVNOT && children[1][0] == children[0] )
        result =  NodeFactory::CreateTerm(BVMOD,width,bm.CreateMaxConst(width),children[1]);//3285 -> 3113

      if ( width >= 4 && children[0].GetKind() == BVUMINUS && children[1].GetKind() == BVNOT && children[1][0] == children[0][0] )
        result  =   NodeFactory::CreateTerm(SBVREM,width,one,children[1]); //8883 -> 206 | 1566 ms
#endif
    }

    break;

    case stp::WRITE:
      if (children[0].GetKind() == stp::WRITE && children[1] == children[0][1])
      {
        // If the indexes of two writes are the same, then discard the inner
        // write.
        result = NodeFactory::CreateArrayTerm(
            stp::WRITE, children[0].GetIndexWidth(),
            children[0].GetValueWidth(), children[0][0], children[1],
            children[2]);
      }
      else if (children[2].GetKind() == stp::READ &&
               children[0] == children[2][0] && children[1] == children[2][1])
      {
        // Its writing into the array what's already there. i.e.  a[i] = a[i]
        result = children[0];
      }
      break;

    case stp::READ:
      if (children[0].GetKind() == stp::WRITE)
      {
        result = chaseRead(children, width);
      }
      break;

    default: // quieten compiler.
      break;
  }

  if (result.IsNull())
    result = hashing.CreateTerm(kind, width, children);

  return result;
}


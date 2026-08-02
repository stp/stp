/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
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

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include <sstream>

namespace stp
{

uint8_t ASTNode::getIteration() const
{
  return _int_node_ptr->iteration;
}

void ASTNode::setIteration(uint8_t v) const
{
  _int_node_ptr->iteration = v;
}

STPMgr* ASTNode::GetSTPMgr() const
{
  return _int_node_ptr->nodeManager;
}

// GetKind, GetChildren and GetNodeNum are now inlined in ASTNode.h (possible
// since ASTInternal.h no longer includes ASTNode.h, breaking the old cycle).
// The ref-counting special members are inlined there too.

void ASTNode::SetIndexWidth(unsigned int _iw) const
{
  _int_node_ptr->setIndexWidth(_iw);
}

void ASTNode::SetValueWidth(unsigned int vw) const
{
  _int_node_ptr->setValueWidth(vw);
}

// Work out an interior node's floating-point format from its kind and its
// children, returning false when the node does not denote a float.
//
// The format used to be pure per-node state that whoever built the node was
// expected to stamp on afterwards. That does not survive contact with the
// preprocessing pipeline: dozens of places rebuild nodes, and any that
// forgets leaves a float claiming a format of (0, 0), which the blaster does
// not reject -- it computes the wrong bits, or underflows a width. Deriving
// the format instead means a rebuilt node cannot lose it, because there is
// nothing to lose.
//
// Leaves still have to store it: a symbol's format is declared, and a
// constant's is fixed when it is made (see STPMgr::CreateFPConst). Interior
// nodes are all covered here.
static bool deriveFPFormat(const ASTNode& n, unsigned int& e, unsigned int& s)
{
  switch (n.GetKind())
  {
    // to_fp names its target format in its first two children, rather than
    // inheriting one from an operand. So does the C API's floating-point
    // *type* node (vc_fpType) -- covering it here is what makes
    // vc_getExpWidth/vc_getSigWidth work on a type, as documented.
    case FP_TOFP:
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    case FLOATINGPOINT:
    {
      if (n.Degree() < 2 || !n[0].isConstant() || !n[1].isConstant())
        return false;

      e = n[0].GetUnsignedConst();
      s = n[1].GetUnsignedConst();
      return e != 0 && s != 0;
    }

    // A read from an array of floats yields a float in the element's format,
    // which the array node carries.
    case READ:
    {
      if (n.Degree() < 1)
        return false;

      e = n[0].GetExpWidth();
      s = n[0].GetSigWidth();
      return e != 0 && s != 0;
    }

    // A store to an array of floats is itself an array of floats: carry the
    // element format from the array child, so a read over a store chain can
    // derive its format (the recursion bottoms out at the array symbol,
    // whose declaration set it).
    case WRITE:
    {
      if (n.Degree() < 1)
        return false;

      e = n[0].GetExpWidth();
      s = n[0].GetSigWidth();
      return e != 0 && s != 0;
    }

    // A float-valued ITE takes the format of its branches (children 1 and 2,
    // which share it). Checked first and cheaply because bitvector ITEs are
    // everywhere: for those the branch carries no format and this returns at
    // once.
    case ITE:
    {
      if (n.Degree() != 3)
        return false;

      e = n[1].GetExpWidth();
      s = n[1].GetSigWidth();
      if (e == 0)
      {
        e = n[2].GetExpWidth();
        s = n[2].GetSigWidth();
      }
      return e != 0 && s != 0;
    }

    // The rest produce a float in the format of their float operand. Which
    // child that is varies -- the arithmetic operations lead with a rounding
    // mode -- and an operand that was folded to a constant may have lost its
    // own format, so take the first child that has one.
    case FP_ABS:
    case FP_NEG:
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    {
      for (size_t i = 0; i < n.Degree(); i++)
      {
        const unsigned int child_exp = n[i].GetExpWidth();
        if (child_exp != 0)
        {
          e = child_exp;
          s = n[i].GetSigWidth();
          return true;
        }
      }
      return false;
    }

    default:
      return false;
  }
}

// Sentinel cached in _exp_width once derivation has concluded "not a
// float". Without it every format query on a formatless node re-walks its
// children -- quadratic on store chains and ITE spines, since WRITE and ITE
// derive through their children. A later SetExpWidth (from a declaration or
// the blaster stamping its output) simply overwrites it.
static const uint32_t FP_NOT_A_FLOAT = 0xFFFFFFFFu;

// Derive once and keep the answer -- positive or negative. The fields are
// already mutable, and an interior node can hold them, so this costs one
// walk per node rather than one per query.
void ASTNode::cacheFPFormat() const
{
  unsigned int e = 0;
  unsigned int s = 0;

  const bool is_float = deriveFPFormat(*this, e, s);

  // A BVCONST has nowhere to put either answer (its setters reject it);
  // float constants are made as ASTFPConst instead, and re-deriving on a
  // childless node is cheap.
  if (GetKind() == BVCONST ||
      (Degree() == 0 &&
       _int_node_ptr->getDeclaredSourceSort().isKnown()))
    return;

  if (!is_float)
  {
    _int_node_ptr->setExpWidth(FP_NOT_A_FLOAT);
    return;
  }

  _int_node_ptr->setExpWidth(e);
  _int_node_ptr->setSigWidth(s);
}

unsigned int ASTNode::GetExpWidth() const
{
  unsigned int stored = _int_node_ptr->getExpWidth();
  if (stored == FP_NOT_A_FLOAT)
    return 0;
  if (stored != 0)
    return stored;

  cacheFPFormat();
  stored = _int_node_ptr->getExpWidth();
  return stored == FP_NOT_A_FLOAT ? 0 : stored;
}

// A float's format may be stored only where it cannot be shared with a plain
// bitvector use of the same node:
//
//  - on a leaf, whose sort is declared (a symbol) or fixed when it is made
//    (an ASTFPConst, which interns apart from the plain constant holding the
//    same bits);
//  - on an interior node whose *kind* says it is a float, where it is derived
//    from the kind and children rather than assigned (see deriveFPFormat) and
//    so cannot disagree with anything;
//  - on an array, where it describes the elements rather than the node.
//
// Never on a bitvector-kind interior node. Nodes are hash-consed and the
// format is per-node state, so a format stamped on the bits a float lowers to
// retypes everything else that denotes those bits: the input's own bitvectors
// start reporting FLOATINGPOINT_TYPE solver-wide, bitvector operations over
// them stop type checking, and to_fp reads an integer as a float. Lowering
// therefore hands its format to the blaster as an argument instead (see
// FloatBlaster::operandFormat and FloatBlast).
bool ASTNode::canStoreFPFormat() const
{
  return Degree() == 0 || is_FP_kind(GetKind()) || GetKind() == FLOATINGPOINT ||
         GetIndexWidth() > 0;
}

void ASTNode::SetExpWidth(unsigned int _ew) const
{
  // A format may be set, re-set to the same value, or cleared -- never
  // changed. Two contexts disagreeing about a shared node's format is the
  // hash-consing corruption this trips on.
  assert(_int_node_ptr->getExpWidth() == 0 ||
         _int_node_ptr->getExpWidth() == 0xFFFFFFFFu /* not-a-float cache */ ||
         _ew == 0 || _int_node_ptr->getExpWidth() == _ew);

  // Callers stamp only what can hold a stamp; withFormat is where that is
  // decided, for the callers that do not already know.
  assert(_ew == 0 || canStoreFPFormat());
  // One of the funnels through which a float's format arrives, so this is
  // where the manager learns that floats are in play. Not the only one:
  // a node that derives its format needs no stamp and never reaches here,
  // which is why withFormat -- the entry point that decides whether the
  // stamp is needed -- notes it too.
  if (_ew != 0)
    _int_node_ptr->nodeManager->noteFloatingPoint();
  _int_node_ptr->setExpWidth(_ew);
}

unsigned int ASTNode::GetSigWidth() const
{
  if (_int_node_ptr->getExpWidth() == FP_NOT_A_FLOAT)
    return 0;

  const unsigned int stored = _int_node_ptr->getSigWidth();
  if (stored != 0)
    return stored;

  cacheFPFormat();
  return _int_node_ptr->getSigWidth();
}

void ASTNode::SetSigWidth(unsigned int _sw) const
{
  assert(_int_node_ptr->getSigWidth() == 0 || _sw == 0 ||
         _int_node_ptr->getSigWidth() == _sw);
  _int_node_ptr->setSigWidth(_sw);
}

// return the type of the ASTNode:
//
// 0 iff BOOLEAN; 1 iff BITVECTOR; 2 iff ARRAY; 3 iff UNKNOWN;
// Print the node
void ASTNode::nodeprint(ostream& os, bool c_friendly) const
{
  _int_node_ptr->nodeprint(os, c_friendly);
}

// Get the name from a symbol (char *).  It's an error if kind !=
// SYMBOL
const char* ASTNode::GetName() const
{
  if (GetKind() != SYMBOL)
    FatalError("GetName: Called GetName on a non-symbol: ", *this);

  return ((ASTSymbol*)_int_node_ptr)->GetName();
}

SourceSort ASTNode::GetSourceSort() const
{
  if (IsNull())
    return SourceSort::unknown();
  if (GetKind() == UNDEFINED)
    return SourceSort::unknown();

  // API type nodes denote the corresponding source sort even though they
  // are not themselves value-bearing terms.
  switch (GetKind())
  {
    case BOOLEAN:
      return SourceSort::boolean();
    case BITVECTOR:
      if (Degree() == 1 && (*this)[0].GetKind() == BVCONST)
        return SourceSort::bitVector((*this)[0].GetUnsignedConst());
      break;
    case FLOATINGPOINT:
      if (Degree() == 2 && (*this)[0].GetKind() == BVCONST &&
          (*this)[1].GetKind() == BVCONST)
        return SourceSort::floatingPoint((*this)[0].GetUnsignedConst(),
                                         (*this)[1].GetUnsignedConst());
      break;
    case ROUNDINGMODE:
      return SourceSort::roundingMode();
    case ARRAY:
      if (Degree() == 2)
      {
        const SourceSort index = (*this)[0].GetSourceSort();
        const SourceSort element = (*this)[1].GetSourceSort();
        if (index.isScalar() && element.isScalar())
          return SourceSort::array(index, element);
      }
      break;
    default:
      break;
  }

  // Typed constants and symbols carry their sort as immutable identity.
  const SourceSort declared = _int_node_ptr->getDeclaredSourceSort();
  if (declared.isKnown())
    return declared;

  // The only source expressions whose carrier does not identify the result
  // sort are the structural ones below. Derive them from their children.
  if (GetKind() == READ && Degree() >= 1)
  {
    const SourceSort array = (*this)[0].GetSourceSort();
    return array.kind() == SourceSort::Kind::Array
               ? array.element()
               : SourceSort::unknown();
  }

  if (GetKind() == WRITE && Degree() >= 1)
    return (*this)[0].GetSourceSort();

  if (GetKind() == ITE && Degree() == 3)
  {
    const SourceSort then_sort = (*this)[1].GetSourceSort();
    const SourceSort else_sort = (*this)[2].GetSourceSort();
    return then_sort == else_sort ? then_sort : SourceSort::unknown();
  }

  // Compatibility for internal and legacy leaves that predate typed source
  // symbols. New public declarations do not take this path.
  switch (GetType())
  {
    case BOOLEAN_TYPE:
      return SourceSort::boolean();
    case BITVECTOR_TYPE:
      return GetValueWidth() == 0 ? SourceSort::unknown()
                                  : SourceSort::bitVector(GetValueWidth());
    case FLOATINGPOINT_TYPE:
      return SourceSort::floatingPoint(GetExpWidth(), GetSigWidth());
    case ARRAY_TYPE:
    {
      const SourceSort index = SourceSort::bitVector(GetIndexWidth());
      const SourceSort element =
          GetExpWidth() == 0
              ? SourceSort::bitVector(GetValueWidth())
              : SourceSort::floatingPoint(GetExpWidth(), GetSigWidth());
      return SourceSort::array(index, element);
    }
    default:
      return SourceSort::unknown();
  }
}

// Get the value of bvconst from a bvconst.  It's an error if kind
// != BVCONST Treat the result as const (the compiler can't enforce
// it).
CBV ASTNode::GetBVConst() const
{
  if (GetKind() != BVCONST)
    FatalError("GetBVConst: non bitvector-constant: ", *this);

  return ((ASTBVConst*)_int_node_ptr)->GetBVConst();
}

unsigned int ASTNode::GetUnsignedConst() const
{
  const ASTNode& n = *this;
  assert(BVCONST == n.GetKind());

  if (sizeof(unsigned int) * 8 < n.GetValueWidth())
  {
    // It may only contain a small value in a bit type,
    // which fits nicely into an unsigned int.  This is
    // common for functions like: bvshl(bv1[128],
    // bv1[128]) where both operands have the same type.
    signed long maxBit = CONSTANTBV::Set_Max(n.GetBVConst());
    if (maxBit >= ((signed long)sizeof(unsigned int)) * 8)
    {
      n.LispPrint(std::cerr); // print the node so they can find it.
      FatalError("GetUnsignedConst: cannot convert bvconst "
                 "of length greater than 32 to unsigned int");
    }
  }
  return (unsigned int)*((unsigned int*)n.GetBVConst());
}

// Hash() is now inlined in ASTNode.h.

void ASTNode::NFASTPrint(int l, int max, int prefix) const
{
  //****************************************
  // stop
  //****************************************
  if (l > max)
  {
    return;
  }

  //****************************************
  // print
  //****************************************
  printf("[%10d]", 0);
  for (int i = 0; i < prefix; i++)
  {
    printf("    ");
  }
  std::cout << GetKind();
  printf("\n");

  //****************************************
  // recurse
  //****************************************

  const ASTChildren children = GetChildren();
  auto it = children.begin();
  for (; it != children.end(); it++)
  {
    it->NFASTPrint(l + 1, max, prefix + 1);
  }
}

bool ASTNode::isSimplfied() const
{
  return _int_node_ptr->isSimplified();
}

void ASTNode::hasBeenSimplfied() const
{
  _int_node_ptr->hasBeenSimplified();
}

} //end of namespace

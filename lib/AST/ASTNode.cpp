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
#include "stp/Util/DagWalk.h"
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

    // An application of an uninterpreted function whose codomain is a float
    // yields a float in the codomain's format. That format is not carried by
    // any operand -- the declaration identity in child 0 names it, in the
    // same immutable source sort deriveSourceSort reads for the node's sort.
    // Without this the application would be an FP-sorted node of no format,
    // which types as a plain bit-vector: fp.add would refuse it as having a
    // different format from its other operand, and fp.abs would build a
    // (0, 0)-format result that blasts to the wrong bits.
    case UF_APPLY:
    {
      if (n.Degree() < 1)
        return false;

      const SourceSort codomain = n[0].GetSourceSort();
      if (codomain.kind() != SourceSort::Kind::FloatingPoint)
        return false;

      e = codomain.exponentWidth();
      s = codomain.significandWidth();
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

// Which children a node's format derivation reads, as a half-open range of
// child positions.
//
// This says what the switch above consults and has to keep agreeing with it:
// the read and store arms take the format of the array under them, the
// if-then-else arm takes a branch's, and the arithmetic arms take whichever
// operand carries one. Every other kind decides from its own kind, or from
// children it reads as constants rather than as floats, so an empty range is
// also "the walk below stops here".
//
// The if-then-else and arithmetic arms stop at the first operand that answers,
// where this names them all. Naming more than is read costs a derivation that
// would have happened the moment anything asked that node its type, and can
// cost nothing else: neither derivation builds a node, calls a factory or
// reads anything but its subject's kind, children and widths.
static void fpFormatOperands(const ASTNode& n, size_t& from, size_t& to)
{
  from = 0;
  to = 0;

  switch (n.GetKind())
  {
    case READ:
    case WRITE:
      to = (n.Degree() >= 1) ? 1 : 0;
      break;

    case UF_APPLY:
      // The declaration identity's immutable source sort is the codomain.
      to = (n.Degree() >= 1) ? 1 : 0;
      break;

    case ITE:
      if (n.Degree() == 3)
      {
        from = 1;
        to = 3;
      }
      break;

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
      to = n.Degree();
      break;

    default:
      break;
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
//
// The derivation reads its operands' formats, and reading one derives it --
// which was this function again, one call frame per level of a store chain or
// an if-then-else spine. Nothing bounds those: they are as deep as the input
// nests, and 20,000 is fatal. It is worse than a pass dying on its own input,
// because this is not a pass. GetType asks for the format and everything asks
// GetType, so a query deep enough could not be asked its type at all, from
// anywhere.
//
// So primeMemo fills the dependency suffix bottom up, and the derivation then
// finds every operand it reads already answered and stops one level down. See
// DagWalk.h, and DeepDag_Test.cpp for the depths.
void ASTNode::cacheFPFormat() const
{
#ifndef NDEBUG
  static thread_local PrimeAudit audit{"ASTNode::cacheFPFormat", 8};
  PrimeAudit::Running running(audit, *this);
#endif

  // One node, with its operands already answered.
  auto store = [](const ASTNode& n) {
    unsigned int e = 0;
    unsigned int s = 0;

    const bool is_float = deriveFPFormat(n, e, s);

    // A BVCONST has nowhere to put either answer (its setters reject it);
    // float constants are made as ASTFPConst instead, and re-deriving on a
    // childless node is cheap.
    if (n.GetKind() == BVCONST ||
        (n.Degree() == 0 &&
         n._int_node_ptr->getDeclaredSourceSort().isKnown()))
      return;

    if (!is_float)
    {
      n._int_node_ptr->setExpWidth(FP_NOT_A_FLOAT);
      return;
    }

    n._int_node_ptr->setExpWidth(e);
    n._int_node_ptr->setSigWidth(s);
  };

  // Nothing below `n` needs filling: either its own derivation reads no
  // operands, so asking it is already one level, or it has been asked
  // before. The first case is why a node that cannot hold an answer -- a
  // constant, a declared leaf -- never sends this walk into a loop over it.
  auto settled = [](const ASTNode& n) {
    size_t from, to;
    fpFormatOperands(n, from, to);
    return from == to || n._int_node_ptr->getExpWidth() != 0;
  };

  size_t from, to;
  fpFormatOperands(*this, from, to);
  bool fill = false;
  for (size_t i = from; i < to && !fill; i++)
    fill = !settled((*this)[i]);

  if (!fill)
  {
    store(*this);
    return;
  }

  primeMemoInlineParent(
      *this, [&](const ASTNode& child)
      { return settled(child) ? Walk::Skip : Walk::Descend; },
      [](const ASTNode& n)
      {
        size_t f, t;
        fpFormatOperands(n, f, t);
        return WalkOperands::range(f, t);
      },
      [&](const ASTNode& n, PrimeMemoReady) { store(n); });
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

// Memoised wrapper over deriveSourceSort.
//
// The derivation walks children for READ, WRITE and ITE -- and for ITE it
// walks *both* branches -- so recomputing it costs Theta(2^depth) on a
// shared-branch ITE DAG and Theta(depth) on a store chain, on a graph of
// linear size. That is not a cost paid once: the front ends ask for every
// node they build, and containsFloatingPointTheory asks for every node of
// every query, including queries with no floating point in them.
//
// Memoising is sound for the same reason the floating-point format's memo is
// (see cacheFPFormat): the derivation reads only the node's kind, children
// and widths, and the first two are the hash-cons key. The widths are not, so
// the setters drop the memo.
// Which children a node's source-sort derivation reads, as a half-open range
// of child positions, and the same bargain as fpFormatOperands above: it has
// to keep agreeing with deriveSourceSort, and naming more than is read can
// only cost a derivation that the next question would have caused anyway.
//
// Every other kind answers from its own kind, its declared sort, or its
// widths -- and the widths route through GetType, which is the format
// derivation and stops on its own.
static void sourceSortOperands(const ASTNode& n, size_t& from, size_t& to)
{
  from = 0;
  to = 0;

  switch (n.GetKind())
  {
    case ARRAY:
      if (n.Degree() == 2)
        to = 2;
      break;

    case READ:
    case WRITE:
      to = (n.Degree() >= 1) ? 1 : 0;
      break;

    case ITE:
      if (n.Degree() == 3)
      {
        from = 1;
        to = 3;
      }
      break;

    default:
      break;
  }
}

SourceSort ASTNode::GetSourceSort() const
{
  if (IsNull())
    return SourceSort::unknown();

  if (const SourceSort* cached = _int_node_ptr->cachedSourceSort())
    return *cached;

#ifndef NDEBUG
  static thread_local PrimeAudit audit{"ASTNode::GetSourceSort", 8};
  PrimeAudit::Running running(audit, *this);
#endif

  // One node, with its operands already answered. The answer goes on the node
  // where a node can hold one -- a leaf cannot, only an interior node holds
  // the memo -- and into `answer` either way, which is how the node this
  // started from returns its own: the walk finishes with it, so the last
  // answer recorded is that one.
  SourceSort answer = SourceSort::unknown();
  auto store = [&](const ASTNode& n) {
    n._int_node_ptr->nodeManager->source_sort_derivations++;
    answer = n.deriveSourceSort();
    n._int_node_ptr->setCachedSourceSort(
        n._int_node_ptr->nodeManager->internSourceSort(answer));
  };

  // As in cacheFPFormat, and for the same reason -- the derivation reads a
  // child's sort by asking for it, which derived the child the same way, one
  // call frame per level of a store chain or an if-then-else spine.
  //
  // A leaf is settled by having nothing to read, never by its memo: only an
  // interior node can hold one. So the walk stops above every leaf and leaves
  // it to be derived by whichever parent reads it, which is what kept the
  // derivation count what it was.
  auto settled = [](const ASTNode& n) {
    size_t from, to;
    sourceSortOperands(n, from, to);
    return from == to || n._int_node_ptr->cachedSourceSort() != NULL;
  };

  size_t from, to;
  sourceSortOperands(*this, from, to);
  bool fill = false;
  for (size_t i = from; i < to && !fill; i++)
    fill = !settled((*this)[i]);

  if (fill)
    primeMemoInlineParent(
        *this, [&](const ASTNode& child)
        { return settled(child) ? Walk::Skip : Walk::Descend; },
        [](const ASTNode& n)
        {
          size_t f, t;
          sourceSortOperands(n, f, t);
          return WalkOperands::range(f, t);
        },
        [&](const ASTNode& n, PrimeMemoReady) { store(n); });
  else
    store(*this);

  return answer;
}

SourceSort ASTNode::deriveSourceSort() const
{
  if (GetKind() == UNDEFINED)
    return SourceSort::unknown();

  if (GetKind() == UF_APPLY && Degree() >= 1)
    return (*this)[0].GetSourceSort();

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
    if (then_sort == else_sort)
      return then_sort;
    // After lowering, a float-valued mux may hold one branch as its packed
    // circuit -- a plain bitvector of the float's packed width -- while the
    // other branch still names the float sort. BVTypeCheck's ITE rule
    // admits exactly this mix (it arises only when lowering replaces a
    // branch with its circuit; public construction requires the branches to
    // share a sort), and deriveFPFormat already reads the format from
    // whichever branch kept it. The array transform builds such muxes when
    // it expands a read over a write of a float array: the stored value is
    // already a circuit, the fresh read variable is float-stamped. The
    // float branch names the sort for both.
    const bool then_is_float =
        then_sort.kind() == SourceSort::Kind::FloatingPoint;
    const bool else_is_float =
        else_sort.kind() == SourceSort::Kind::FloatingPoint;
    if (then_is_float != else_is_float)
    {
      const SourceSort& float_sort = then_is_float ? then_sort : else_sort;
      const SourceSort& other_sort = then_is_float ? else_sort : then_sort;
      if (other_sort.kind() == SourceSort::Kind::BitVector &&
          other_sort.bitVectorWidth() == float_sort.packedWidth())
        return float_sort;
    }
    return SourceSort::unknown();
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

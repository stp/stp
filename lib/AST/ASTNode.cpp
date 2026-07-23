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

// Constructor;
//
// creates a new pointer, increments refcount of pointed-to object.
ASTNode::ASTNode(ASTInternal* in) : _int_node_ptr(in)
{
  if (in)
  {
    in->IncRef();
  }
}

//#define ASTNODE_COUNT_OPS

#ifdef ASTNODE_COUNT_OPS
THREAD_LOCAL int ASTNode::copy = 0;
THREAD_LOCAL int ASTNode::move = 0;
THREAD_LOCAL int ASTNode::assign = 0;
THREAD_LOCAL int ASTNode::destroy = 0;
THREAD_LOCAL int ASTNode::assign_move = 0;
#endif

//Maintain _ref_count
ASTNode::ASTNode(const ASTNode& n) : _int_node_ptr(n._int_node_ptr)
{
#ifdef ASTNODE_COUNT_OPS
  if (++copy % 1000000 == 0)
    std::cerr << "copy" << copy << std::endl;
#endif

  if (n._int_node_ptr)
  {
    n._int_node_ptr->IncRef();
  }
}

ASTNode::ASTNode(ASTNode&& other) noexcept : _int_node_ptr(other._int_node_ptr)
{
#ifdef ASTNODE_COUNT_OPS
  if (++move % 1000000 == 0)
    std::cerr << "move" << move << std::endl;
#endif

  other._int_node_ptr = 0;
}

ASTNode& ASTNode::operator=(ASTNode&& n)
{
#ifdef ASTNODE_COUNT_OPS
  if (++assign_move % 1000000 == 0)
    std::cerr << "assign_move" << assign_move << std::endl;
#endif

  if (_int_node_ptr)
    _int_node_ptr->DecRef();

  _int_node_ptr = n._int_node_ptr;

  n._int_node_ptr = 0;
  return *this;
}

// GetKind, GetChildren and GetNodeNum are now inlined in ASTNode.h (possible
// since ASTInternal.h no longer includes ASTNode.h, breaking the old cycle).

unsigned int ASTNode::GetIndexWidth() const
{
  return _int_node_ptr->getIndexWidth();
}

void ASTNode::SetIndexWidth(unsigned int _iw) const
{
  _int_node_ptr->setIndexWidth(_iw);
}

unsigned int ASTNode::GetValueWidth() const
{
  // TODO: FIXME: this is *horrible*
  if (_int_node_ptr->getSigWidth() > 0)
  {
    return _int_node_ptr->getSigWidth() + _int_node_ptr->getExpWidth();
  }
  return _int_node_ptr->getValueWidth();
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
    // inheriting one from an operand.
    case FP_TOFP:
    case FP_TOFP_UNSIGNED:
    {
      if (n.Degree() < 2 || !n[0].isConstant() || !n[1].isConstant())
        return false;

      e = n[0].GetUnsignedConst();
      s = n[1].GetUnsignedConst();
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

// Derive once and keep the answer. The fields are already mutable, and an
// interior node can hold them, so this costs one walk per node rather than
// one per query.
void ASTNode::cacheFPFormat() const
{
  unsigned int e = 0;
  unsigned int s = 0;

  if (!deriveFPFormat(*this, e, s))
    return;

  // A BVCONST has nowhere to put it; those are made as ASTFPConst instead.
  if (GetKind() == BVCONST)
    return;

  _int_node_ptr->setExpWidth(e);
  _int_node_ptr->setSigWidth(s);
}

unsigned int ASTNode::GetExpWidth() const
{
  const unsigned int stored = _int_node_ptr->getExpWidth();
  if (stored != 0)
    return stored;

  cacheFPFormat();
  return _int_node_ptr->getExpWidth();
}

void ASTNode::SetExpWidth(unsigned int _ew) const
{
  _int_node_ptr->setExpWidth(_ew);
}

unsigned int ASTNode::GetSigWidth() const
{
  const unsigned int stored = _int_node_ptr->getSigWidth();
  if (stored != 0)
    return stored;

  cacheFPFormat();
  return _int_node_ptr->getSigWidth();
}

void ASTNode::SetSigWidth(unsigned int _sw) const
{
  _int_node_ptr->setSigWidth(_sw);
}

// return the type of the ASTNode:
//
// 0 iff BOOLEAN; 1 iff BITVECTOR; 2 iff ARRAY; 3 iff UNKNOWN;
types ASTNode::GetType() const
{
  if (GetSigWidth() != 0 && GetExpWidth() != 0)
    return FLOATINGPOINT_TYPE;

  if ((GetIndexWidth() == 0) && (GetValueWidth() == 0))
    return BOOLEAN_TYPE;

  if ((GetIndexWidth() == 0) && (GetValueWidth() > 0))
    return BITVECTOR_TYPE;

  if ((GetIndexWidth() > 0) && (GetValueWidth() > 0))
    return ARRAY_TYPE;

  return UNKNOWN_TYPE;
}

ASTNode& ASTNode::operator=(const ASTNode& n)
{
#ifdef ASTNODE_COUNT_OPS
  if (++assign % 1000000 == 0)
    std::cerr << "assign" << assign << std::endl;
#endif

  if (n._int_node_ptr)
    n._int_node_ptr->IncRef();

  if (_int_node_ptr)
    _int_node_ptr->DecRef();

  _int_node_ptr = n._int_node_ptr;
  return *this;
}

ASTNode::~ASTNode()
{
#ifdef ASTNODE_COUNT_OPS
  if (destroy++ % 1000000 == 0)
    std::cerr << "destroy" << destroy << std::endl;
#endif

  if (_int_node_ptr)
  {
    _int_node_ptr->DecRef();
  }
}

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

// traverse "*this", and construct "let variables" for terms that
// occur more than once in "*this".
void ASTNode::LetizeNode(STPMgr* bm) const
{
  if (isAtom())
    return;

  const ASTChildren c = this->GetChildren();
  for (auto it = c.begin(), itend = c.end(); it != itend;
       it++)
  {
    ASTNode ccc = *it;
    if (bm->PLPrintNodeSet.find(ccc) == bm->PLPrintNodeSet.end())
    {
      // If branch: if *it is not in NodeSet then,
      //
      // 1. add it to NodeSet
      //
      // 2. Letize its childNodes

      bm->PLPrintNodeSet.insert(ccc);
      // debugging
      // cerr << ccc;
      ccc.LetizeNode(bm);
    }
    else
    {
      if (ccc.isAtom())
        continue;

      // 0. Else branch: Node has been seen before
      //
      // 1. Check if the node has a corresponding letvar in the
      // 1. NodeLetVarMap.
      //
      // 2. if no, then create a new var and add it to the
      // 2. NodeLetVarMap
      if (bm->NodeLetVarMap.find(ccc) == bm->NodeLetVarMap.end())
      {
        // Create a new symbol. Get some name. if it conflicts with a
        // declared name, too bad.
        int sz = bm->NodeLetVarMap.size();
        std::ostringstream oss;
        oss << "let_k_" << sz;

        ASTNode CurrentSymbol = bm->CreateSymbol(
            oss.str().c_str(), this->GetIndexWidth(), this->GetValueWidth());
        /* If for some reason the variable being created here is
         * already declared by the user then the printed output will
         * not be a legal input to the system. too bad. I refuse to
         * check for this.
         */
        bm->NodeLetVarMap[ccc] = CurrentSymbol;
        std::pair<ASTNode, ASTNode> node_letvar_pair(CurrentSymbol, ccc);
        bm->NodeLetVarVec.push_back(node_letvar_pair);
      }
    }
  }
}

} //end of namespace

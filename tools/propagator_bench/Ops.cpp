/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

// The operations under test, how their nodes are shaped, and the reference
// semantics that the precision phases compare against.

#include "PropagatorBench.h"

#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/ValueSetAnalysis.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"

#include <algorithm>
#include <sstream>

using namespace stp;
using namespace simplifier::constantBitP;

namespace propbench
{

const char* name(Domain d)
{
  switch (d)
  {
    case Domain::Cbitp: return "cbitp";
    case Domain::Interval: return "interval";
    case Domain::ValueSet: return "valueset";
  }
  return "?";
}

const char* name(Direction d)
{
  switch (d)
  {
    case Direction::BottomUp: return "bottom-up";
    case Direction::TopDown: return "top-down";
    case Direction::BothWays: return "both-ways";
  }
  return "?";
}

bool parseDomain(const string& s, Domain& out)
{
  if (s == "cbitp") { out = Domain::Cbitp; return true; }
  if (s == "interval") { out = Domain::Interval; return true; }
  if (s == "valueset") { out = Domain::ValueSet; return true; }
  return false;
}

bool parseDirection(const string& s, Direction& out)
{
  if (s == "bottom-up" || s == "bottomup" || s == "up")
  { out = Direction::BottomUp; return true; }
  if (s == "top-down" || s == "topdown" || s == "down")
  { out = Direction::TopDown; return true; }
  if (s == "both-ways" || s == "bothways" || s == "both")
  { out = Direction::BothWays; return true; }
  return false;
}

// ---------------------------------------------------------------------------

const vector<OpSpec>& allOps()
{
  static const vector<OpSpec> ops = {
      // kind, name, shape, n-ary, SAT checkable
      {BVAND, "bvand", Shape::Nary, true, true},
      {BVOR, "bvor", Shape::Nary, true, true},
      {BVXOR, "bvxor", Shape::Nary, true, true},
      {BVNOT, "bvnot", Shape::Unary, false, true},
      {BVPLUS, "bvadd", Shape::Nary, true, true},
      {BVSUB, "bvsub", Shape::Nary, false, true},
      {BVUMINUS, "bvneg", Shape::Unary, false, true},
      // bvmul stays two-operand here: the cbitp transfer function bails
      // out (NO_CHANGE) on wider multiplies.
      {BVMULT, "bvmul", Shape::Nary, false, true},
      {BVDIV, "bvudiv", Shape::Nary, false, true},
      {BVMOD, "bvurem", Shape::Nary, false, true},
      {SBVDIV, "bvsdiv", Shape::Nary, false, true},
      {SBVREM, "bvsrem", Shape::Nary, false, true},
      {SBVMOD, "bvsmod", Shape::Nary, false, true},
      {BVLEFTSHIFT, "bvshl", Shape::Nary, false, true},
      {BVRIGHTSHIFT, "bvlshr", Shape::Nary, false, true},
      {BVSRSHIFT, "bvashr", Shape::Nary, false, true},
      {BVLT, "bvult", Shape::Predicate, false, true},
      {BVLE, "bvule", Shape::Predicate, false, true},
      {BVGT, "bvugt", Shape::Predicate, false, true},
      {BVGE, "bvuge", Shape::Predicate, false, true},
      {BVSLT, "bvslt", Shape::Predicate, false, true},
      {BVSLE, "bvsle", Shape::Predicate, false, true},
      {BVSGT, "bvsgt", Shape::Predicate, false, true},
      {BVSGE, "bvsge", Shape::Predicate, false, true},
      {EQ, "eq", Shape::Predicate, false, true},
      {ITE, "ite", Shape::Ite, false, true},
      {BVCONCAT, "concat", Shape::Concat, false, true},
      {BVEXTRACT, "extract", Shape::Extract, false, false},
      {BVZX, "zero_extend", Shape::Extend, false, false},
      {BVSX, "sign_extend", Shape::Extend, false, false},
      {AND, "and", Shape::BoolNary, true, true},
      {OR, "or", Shape::BoolNary, true, true},
      {XOR, "xor", Shape::BoolNary, false, true},
      {NOT, "not", Shape::BoolUnary, false, true},
      {IMPLIES, "implies", Shape::BoolNary, false, true},
      {IFF, "iff", Shape::BoolNary, false, true},
  };
  return ops;
}

const OpSpec* findOp(const string& n)
{
  for (const OpSpec& o : allOps())
    if (n == o.name)
      return &o;
  return NULL;
}

// The kinds each analysis has a transfer function for. cbitp's list is the
// switch in ConstantBitPropagation::dispatchToTransferFunctions, the
// interval list is the switch in
// UnsignedIntervalAnalysis::dispatchToTransferFunctions, and the value set
// analysis evaluates over the cartesian product of anything the constant
// evaluator handles.
bool supports(Domain d, const OpSpec& op)
{
  switch (d)
  {
    case Domain::Cbitp:
      return true; // every operation in the table is dispatched to.

    case Domain::Interval:
      switch (op.kind)
      {
        case NOT:
        case AND:
        case OR:
        case XOR:
        case EQ:
        case BVGT:
        case BVSGT:
        case BVAND:
        case BVOR:
        case BVXOR:
        case BVNOT:
        case BVPLUS:
        case BVMULT:
        case BVDIV:
        case BVMOD:
        case SBVDIV:
        case SBVREM:
        case SBVMOD:
        case BVLEFTSHIFT:
        case BVRIGHTSHIFT:
        case BVSRSHIFT:
        case BVSX:
        case BVUMINUS:
        case BVCONCAT:
        case BVEXTRACT:
        case ITE:
          return true;
        default:
          return false;
      }

    case Domain::ValueSet:
      return ValueSetAnalysis::constEvaluable(op.kind);
  }
  return false;
}

// ---------------------------------------------------------------------------

vector<unsigned> Layout::varying() const
{
  vector<unsigned> result;
  for (unsigned i = 0; i < children.size(); i++)
    if (!children[i].isConstant)
      result.push_back(i);
  return result;
}

unsigned Layout::packedBits() const
{
  unsigned total = 0;
  for (const ChildSpec& c : children)
    if (!c.isConstant)
      total += c.width;
  return total;
}

static ChildSpec value(unsigned width)
{
  ChildSpec c;
  c.width = width;
  return c;
}

static ChildSpec boolean()
{
  ChildSpec c;
  c.width = 1;
  c.isBoolean = true;
  return c;
}

static ChildSpec constant(uint64_t v)
{
  ChildSpec c;
  c.width = 32;
  c.isConstant = true;
  c.value = v;
  return c;
}

Layout layoutFor(const OpSpec& op, unsigned width, unsigned arity)
{
  Layout l;
  if (width == 0)
    return l;
  const unsigned n = op.nary ? std::max(2u, arity) : 2;

  switch (op.shape)
  {
    case Shape::Nary:
      for (unsigned i = 0; i < n; i++)
        l.children.push_back(value(width));
      l.outWidth = width;
      break;

    case Shape::Predicate:
      l.children.push_back(value(width));
      l.children.push_back(value(width));
      l.outIsBoolean = true;
      l.outWidth = 1;
      break;

    case Shape::Unary:
      l.children.push_back(value(width));
      l.outWidth = width;
      break;

    case Shape::BoolNary:
      // The boolean operations don't have a width; they are only run once.
      if (width != 1)
        return l;
      for (unsigned i = 0; i < n; i++)
        l.children.push_back(boolean());
      l.outIsBoolean = true;
      l.outWidth = 1;
      break;

    case Shape::BoolUnary:
      if (width != 1)
        return l;
      l.children.push_back(boolean());
      l.outIsBoolean = true;
      l.outWidth = 1;
      break;

    case Shape::Ite:
      l.children.push_back(boolean());
      l.children.push_back(value(width));
      l.children.push_back(value(width));
      l.outWidth = width;
      break;

    case Shape::Concat:
      if (width < 2 || width % 2 != 0)
        return l;
      l.children.push_back(value(width / 2));
      l.children.push_back(value(width / 2));
      l.outWidth = width;
      break;

    case Shape::Extract:
      // The bottom half of the input.
      if (width < 2)
        return l;
      l.children.push_back(value(width));
      l.children.push_back(constant(width / 2 - 1));
      l.children.push_back(constant(0));
      l.outWidth = width / 2;
      break;

    case Shape::Extend:
      if (width < 2 || width % 2 != 0)
        return l;
      l.children.push_back(value(width / 2));
      l.children.push_back(constant(width));
      l.outWidth = width;
      break;
  }

  l.ok = true;
  return l;
}

// ---------------------------------------------------------------------------

ASTNode buildNode(STPMgr* mgr, const OpSpec& op, const Layout& l)
{
  ASTVec children;
  for (unsigned i = 0; i < l.children.size(); i++)
  {
    const ChildSpec& c = l.children[i];
    if (c.isConstant)
    {
      children.push_back(mgr->CreateBVConst(c.width, c.value));
      continue;
    }
    std::stringstream n;
    n << "pb_" << op.name << "_" << l.outWidth << "_" << l.children.size()
      << "_" << i;
    children.push_back(
        mgr->CreateSymbol(n.str().c_str(), 0, c.isBoolean ? 0 : c.width));
  }

  ASTNode n;
  if (l.outIsBoolean)
    n = mgr->CreateNode(op.kind, children);
  else
    n = mgr->CreateTerm(op.kind, l.outWidth, children);
  BVTypeCheck(n);
  return n;
}

// ---------------------------------------------------------------------------

ASTNode evaluateNodes(STPMgr* mgr, const OpSpec& op, const Layout& l,
                      const ASTVec& children)
{
  return NonMemberBVConstEvaluator(mgr, op.kind, children,
                                   l.outIsBoolean ? 0 : l.outWidth);
}

uint64_t evaluate(STPMgr* mgr, const OpSpec& op, const Layout& l,
                  const vector<uint64_t>& values)
{
  ASTVec children;
  for (unsigned i = 0; i < l.children.size(); i++)
  {
    const ChildSpec& c = l.children[i];
    const uint64_t v = c.isConstant ? c.value : values[i];
    if (c.isBoolean)
      children.push_back(v ? mgr->ASTTrue : mgr->ASTFalse);
    else
      children.push_back(mgr->CreateBVConst(c.width, v));
  }

  const ASTNode result = evaluateNodes(mgr, op, l, children);
  if (l.outIsBoolean)
    return result == mgr->ASTTrue ? 1 : 0;
  return result.GetUnsignedConst();
}

vector<uint64_t> semanticsTable(STPMgr* mgr, const OpSpec& op, const Layout& l)
{
  const vector<unsigned> varying = l.varying();
  const unsigned bits = l.packedBits();
  vector<uint64_t> table((size_t)1 << bits);

  vector<uint64_t> values(l.children.size(), 0);
  for (uint64_t packed = 0; packed < table.size(); packed++)
  {
    uint64_t rest = packed;
    for (unsigned i : varying)
    {
      const unsigned w = l.children[i].width;
      values[i] = rest & ((w == 64) ? ~0ull : ((1ull << w) - 1));
      rest >>= w;
    }
    table[packed] = evaluate(mgr, op, l, values);
  }
  return table;
}

// ---------------------------------------------------------------------------

FixedBits concreteOf(const ChildSpec& spec, uint64_t v)
{
  FixedBits bits(spec.width, spec.isBoolean);
  for (unsigned i = 0; i < spec.width; i++)
  {
    bits.setFixed(i, true);
    bits.setValue(i, ((v >> i) & 1) != 0);
  }
  return bits;
}

FixedBits randomConcrete(const ChildSpec& spec, std::mt19937& rand)
{
  FixedBits bits(spec.width, spec.isBoolean);
  for (unsigned i = 0; i < spec.width; i++)
  {
    bits.setFixed(i, true);
    bits.setValue(i, (rand() % 2) == 1);
  }
  return bits;
}

void unfixTo(FixedBits& bits, unsigned percent, std::mt19937& rand)
{
  for (unsigned i = 0; i < bits.getWidth(); i++)
    if (rand() % 100 >= percent)
      bits.setFixed(i, false);
}

uint64_t unsignedValue(const FixedBits& bits)
{
  uint64_t v = 0;
  for (unsigned i = 0; i < bits.getWidth() && i < 64; i++)
    if (bits.isFixed(i) && bits.getValue(i))
      v |= (1ull << i);
  return v;
}

double median(vector<double>& v)
{
  if (v.empty())
    return 0;
  std::sort(v.begin(), v.end());
  return v[v.size() / 2];
}

// ---------------------------------------------------------------------------
// The constant-bit transfer functions, mapped exactly as
// ConstantBitPropagation::dispatchToTransferFunctions maps them.

Result cbitpTransfer(STPMgr* mgr, Kind k, vector<FixedBits*>& children,
                     FixedBits& output)
{
  switch (k)
  {
    case BVLEFTSHIFT: return bvLeftShiftBothWays(children, output);
    case BVRIGHTSHIFT: return bvRightShiftBothWays(children, output);
    case BVSRSHIFT: return bvArithmeticRightShiftBothWays(children, output);

    case BVLT: return bvLessThanBothWays(children, output);
    case BVLE: return bvLessThanEqualsBothWays(children, output);
    case BVGT: return bvGreaterThanBothWays(children, output);
    case BVGE: return bvGreaterThanEqualsBothWays(children, output);

    case BVSLT: return bvSignedLessThanBothWays(children, output);
    case BVSGT: return bvSignedGreaterThanBothWays(children, output);
    case BVSLE: return bvSignedLessThanEqualsBothWays(children, output);
    case BVSGE: return bvSignedGreaterThanEqualsBothWays(children, output);

    case XOR:
    case BVXOR: return bvXorBothWays(children, output);
    case OR:
    case BVOR: return bvOrBothWays(children, output);
    case AND:
    case BVAND: return bvAndBothWays(children, output);
    case IFF:
    case EQ: return bvEqualsBothWays(children, output);
    case IMPLIES: return bvImpliesBothWays(children, output);
    case NOT:
    case BVNOT: return bvNotBothWays(children, output);

    case BVZX: return bvZeroExtendBothWays(children, output);
    case BVSX: return bvSignExtendBothWays(children, output);
    case BVUMINUS: return bvUnaryMinusBothWays(children, output);
    case BVEXTRACT: return bvExtractBothWays(children, output);
    case BVPLUS: return bvAddBothWays(children, output);
    case BVSUB: return bvSubtractBothWays(children, output);
    case ITE: return bvITEBothWays(children, output);
    case BVCONCAT: return bvConcatBothWays(children, output);

    case BVMULT: return bvMultiplyBothWays(children, output, mgr, NULL);
    case BVDIV: return bvUnsignedDivisionBothWays(children, output, mgr);
    case BVMOD: return bvUnsignedModulusBothWays(children, output, mgr);
    case SBVDIV: return bvSignedDivisionBothWays(children, output, mgr);
    case SBVREM: return bvSignedRemainderBothWays(children, output, mgr);
    case SBVMOD: return bvSignedModulusBothWays(children, output, mgr);

    default:
      return NO_CHANGE;
  }
}
} // namespace propbench

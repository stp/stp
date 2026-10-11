/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

// Rewrite-rule generator for the SMT-LIB 2.7 overflow predicates (bvuaddo,
// bvsaddo, bvumulo, bvsmulo, bvusubo, bvssubo): a value-vector search, the
// method of tools/fp_rewrite_gen applied to bit-vectors.
//
// Every overflow predicate over two operands drawn from a pool -- the
// variables x and y, the constants {0, 1, ones, smin, smax}, and every
// depth-1 term over those -- is evaluated on every assignment of the
// variables at a small width, giving a vector of truth values. A vector
// equal to that of a strictly smaller form -- true, false, or an
// equality/comparison over pool members -- is a rewrite rule at that width.
// Each rule is then generalised (a depth-1 operand that can be any term is
// replaced by a fresh variable), confirmed exhaustively at the other small
// widths, cross-checked against STP's own constant evaluator (the native
// semantics here are only a fast filter), and finally rebuilt through the
// SimplifyingNodeFactory to see whether it already knows the rule. What
// remains is the list of candidate rules worth adding. The tool can also
// write each missed rule as an SMT-LIB file asserting its negation at a
// larger width, for an independent solver check.
//
// Usage: bv_rewrite_gen [smt2-output-dir]

#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

using namespace stp;

// ---------------------------------------------------------------------------
// Expression trees, evaluated natively at any width up to 32.
enum Op
{
  O_VAR,
  O_CONST,
  O_NOT,
  O_NEG,
  O_ADD,
  O_SUB,
  O_MUL,
  O_UDIV,
  O_UREM,
  O_SDIV,
  O_SREM,
  O_SMOD,
  O_AND,
  O_OR,
  O_XOR,
  O_SHL,
  O_LSHR,
  O_ASHR,
  // Predicates.
  P_TRUE,
  P_FALSE,
  P_EQ,
  P_ULT,
  P_SLT,
  P_UADDO,
  P_SADDO,
  P_UMULO,
  P_SMULO,
  P_USUBO,
  P_SSUBO,
  P_NOT
};
static const Op TERM_UNARY[] = {O_NOT, O_NEG};
static const Op TERM_BINARY[] = {O_ADD,  O_SUB, O_MUL, O_UDIV, O_UREM,
                                 O_SDIV, O_SREM, O_SMOD, O_AND, O_OR,
                                 O_XOR,  O_SHL, O_LSHR, O_ASHR};
static const Op OVERFLOW[] = {P_UADDO, P_SADDO, P_UMULO,
                              P_SMULO, P_USUBO, P_SSUBO};
static const Op TARGET_BINARY[] = {P_EQ, P_ULT, P_SLT};

static bool isPred(Op o)
{
  return o >= P_TRUE;
}

enum Const
{
  C_ZERO,
  C_ONE,
  C_ONES,
  C_SMIN,
  C_SMAX,
  C_COUNT
};
static const char* constName[] = {"0", "1", "ones", "smin", "smax"};

static uint64_t mask(unsigned w)
{
  return (w >= 64) ? ~0ull : ((1ull << w) - 1);
}
static uint64_t constValue(Const c, unsigned w)
{
  switch (c)
  {
    case C_ZERO: return 0;
    case C_ONE: return 1;
    case C_ONES: return mask(w);
    case C_SMIN: return 1ull << (w - 1);
    case C_SMAX: return mask(w) >> 1;
    default: return 0;
  }
}

struct Node
{
  Op op;
  int a = -1, b = -1; // children, indexes into the arena
  int var = 0;        // O_VAR
  Const c = C_ZERO;   // O_CONST
};
static std::vector<Node> arena;

static int mk(Op op, int a = -1, int b = -1)
{
  Node n;
  n.op = op;
  n.a = a;
  n.b = b;
  arena.push_back(n);
  return (int)arena.size() - 1;
}
static int mkVar(int v)
{
  Node n;
  n.op = O_VAR;
  n.var = v;
  arena.push_back(n);
  return (int)arena.size() - 1;
}
static int mkConst(Const c)
{
  Node n;
  n.op = O_CONST;
  n.c = c;
  arena.push_back(n);
  return (int)arena.size() - 1;
}

static int size(int i)
{
  const Node& n = arena[i];
  int s = 1;
  if (n.a >= 0)
    s += size(n.a);
  if (n.b >= 0)
    s += size(n.b);
  return s;
}
static int maxVar(int i)
{
  const Node& n = arena[i];
  if (n.op == O_VAR)
    return n.var;
  int m = -1;
  if (n.a >= 0)
    m = std::max(m, maxVar(n.a));
  if (n.b >= 0)
    m = std::max(m, maxVar(n.b));
  return m;
}
static bool sameTree(int i, int j)
{
  if (i == j)
    return true;
  const Node& p = arena[i];
  const Node& q = arena[j];
  if (p.op != q.op || p.var != q.var || p.c != q.c)
    return false;
  if ((p.a >= 0) != (q.a >= 0) || (p.b >= 0) != (q.b >= 0))
    return false;
  return (p.a < 0 || sameTree(p.a, q.a)) && (p.b < 0 || sameTree(p.b, q.b));
}

// ---------------------------------------------------------------------------
// Native semantics, SMT-LIB's. The constant-evaluator cross-check below is
// what holds these to STP's.
static bool msb(uint64_t v, unsigned w)
{
  return (v >> (w - 1)) & 1;
}
static uint64_t neg(uint64_t v, unsigned w)
{
  return (~v + 1) & mask(w);
}
static uint64_t udiv(uint64_t a, uint64_t b, unsigned w)
{
  return b == 0 ? mask(w) : a / b;
}
static uint64_t urem(uint64_t a, uint64_t b)
{
  return b == 0 ? a : a % b;
}
static uint64_t sdiv(uint64_t a, uint64_t b, unsigned w)
{
  const bool ma = msb(a, w), mb = msb(b, w);
  if (!ma && !mb)
    return udiv(a, b, w);
  if (ma && !mb)
    return neg(udiv(neg(a, w), b, w), w);
  if (!ma && mb)
    return neg(udiv(a, neg(b, w), w), w);
  return udiv(neg(a, w), neg(b, w), w);
}
static uint64_t srem(uint64_t a, uint64_t b, unsigned w)
{
  const bool ma = msb(a, w), mb = msb(b, w);
  if (!ma && !mb)
    return urem(a, b);
  if (ma && !mb)
    return neg(urem(neg(a, w), b), w);
  if (!ma && mb)
    return urem(a, neg(b, w));
  return neg(urem(neg(a, w), neg(b, w)), w);
}
static uint64_t smod(uint64_t a, uint64_t b, unsigned w)
{
  const bool ma = msb(a, w), mb = msb(b, w);
  const uint64_t absA = ma ? neg(a, w) : a;
  const uint64_t absB = mb ? neg(b, w) : b;
  const uint64_t u = urem(absA, absB);
  if (u == 0)
    return u;
  if (!ma && !mb)
    return u;
  if (ma && !mb)
    return (neg(u, w) + b) & mask(w);
  if (!ma && mb)
    return (u + b) & mask(w);
  return neg(u, w);
}
static int64_t toSigned(uint64_t v, unsigned w)
{
  return msb(v, w) ? (int64_t)v - (int64_t)(1ull << w) : (int64_t)v;
}

static uint64_t evalTerm(int i, const uint64_t* vals, unsigned w);

static bool evalPred(int i, const uint64_t* vals, unsigned w)
{
  const Node& n = arena[i];
  switch (n.op)
  {
    case P_TRUE: return true;
    case P_FALSE: return false;
    case P_NOT: return !evalPred(n.a, vals, w);
    default: break;
  }
  const uint64_t a = evalTerm(n.a, vals, w);
  const uint64_t b = evalTerm(n.b, vals, w);
  const int64_t sa = toSigned(a, w), sb = toSigned(b, w);
  const int64_t lo = -(int64_t)(1ull << (w - 1)), hi = (int64_t)(mask(w) >> 1);
  switch (n.op)
  {
    case P_EQ: return a == b;
    case P_ULT: return a < b;
    case P_SLT: return sa < sb;
    case P_UADDO: return a + b > mask(w);
    case P_SADDO: return sa + sb < lo || sa + sb > hi;
    case P_UMULO: return a * b > mask(w);
    case P_SMULO: return sa * sb < lo || sa * sb > hi;
    case P_USUBO: return a < b;
    case P_SSUBO: return sa - sb < lo || sa - sb > hi;
    default: return false;
  }
}

static uint64_t evalTerm(int i, const uint64_t* vals, unsigned w)
{
  const Node& n = arena[i];
  const uint64_t m = mask(w);
  switch (n.op)
  {
    case O_VAR: return vals[n.var];
    case O_CONST: return constValue(n.c, w);
    case O_NOT: return ~evalTerm(n.a, vals, w) & m;
    case O_NEG: return neg(evalTerm(n.a, vals, w), w);
    default: break;
  }
  const uint64_t a = evalTerm(n.a, vals, w);
  const uint64_t b = evalTerm(n.b, vals, w);
  switch (n.op)
  {
    case O_ADD: return (a + b) & m;
    case O_SUB: return (a - b) & m;
    case O_MUL: return (a * b) & m;
    case O_UDIV: return udiv(a, b, w);
    case O_UREM: return urem(a, b);
    case O_SDIV: return sdiv(a, b, w);
    case O_SREM: return srem(a, b, w);
    case O_SMOD: return smod(a, b, w);
    case O_AND: return a & b;
    case O_OR: return a | b;
    case O_XOR: return a ^ b;
    case O_SHL: return b >= w ? 0 : (a << b) & m;
    case O_LSHR: return b >= w ? 0 : a >> b;
    case O_ASHR:
      if (b >= w)
        return msb(a, w) ? m : 0;
      return msb(a, w) ? ((a >> b) | (m & ~(m >> b))) : (a >> b);
    default: return 0;
  }
}

// The value vector of a tree over `nvars` variables at width w: one entry per
// assignment, assignments enumerated with variable 0 fastest.
typedef std::vector<uint64_t> Vec;
static Vec vectorOf(int i, unsigned nvars, unsigned w)
{
  const uint64_t per = 1ull << w;
  uint64_t total = 1;
  for (unsigned v = 0; v < nvars; v++)
    total *= per;
  Vec out(total);
  uint64_t vals[8] = {0};
  const bool pred = isPred(arena[i].op);
  for (uint64_t k = 0; k < total; k++)
  {
    uint64_t rest = k;
    for (unsigned v = 0; v < nvars; v++)
    {
      vals[v] = rest % per;
      rest /= per;
    }
    out[k] = pred ? (evalPred(i, vals, w) ? 1 : 0) : evalTerm(i, vals, w);
  }
  return out;
}

// Whether two trees agree on every assignment at width w.
static bool agree(int i, int j, unsigned nvars, unsigned w)
{
  return vectorOf(i, nvars, w) == vectorOf(j, nvars, w);
}

// ---------------------------------------------------------------------------
// Printing, in SMT-LIB 2 with symbolic constants.
static const char* varName(int v)
{
  static const char* names[] = {"x", "y", "z", "u", "v", "s", "t", "r"};
  return names[v];
}
static std::string print(int i)
{
  const Node& n = arena[i];
  switch (n.op)
  {
    case O_VAR: return varName(n.var);
    case O_CONST: return constName[n.c];
    case P_TRUE: return "true";
    case P_FALSE: return "false";
    default: break;
  }
  const char* name = "?";
  switch (n.op)
  {
    case O_NOT: name = "bvnot"; break;
    case O_NEG: name = "bvneg"; break;
    case O_ADD: name = "bvadd"; break;
    case O_SUB: name = "bvsub"; break;
    case O_MUL: name = "bvmul"; break;
    case O_UDIV: name = "bvudiv"; break;
    case O_UREM: name = "bvurem"; break;
    case O_SDIV: name = "bvsdiv"; break;
    case O_SREM: name = "bvsrem"; break;
    case O_SMOD: name = "bvsmod"; break;
    case O_AND: name = "bvand"; break;
    case O_OR: name = "bvor"; break;
    case O_XOR: name = "bvxor"; break;
    case O_SHL: name = "bvshl"; break;
    case O_LSHR: name = "bvlshr"; break;
    case O_ASHR: name = "bvashr"; break;
    case P_EQ: name = "="; break;
    case P_ULT: name = "bvult"; break;
    case P_SLT: name = "bvslt"; break;
    case P_UADDO: name = "bvuaddo"; break;
    case P_SADDO: name = "bvsaddo"; break;
    case P_UMULO: name = "bvumulo"; break;
    case P_SMULO: name = "bvsmulo"; break;
    case P_USUBO: name = "bvusubo"; break;
    case P_SSUBO: name = "bvssubo"; break;
    case P_NOT: name = "not"; break;
    default: break;
  }
  std::string a = print(n.a);
  if (n.b < 0)
    return std::string("(") + name + " " + a + ")";
  std::string b = print(n.b);
  if (n.op == P_EQ && b < a) // equality is symmetric: one spelling
    std::swap(a, b);
  return std::string("(") + name + " " + a + " " + b + ")";
}

// ---------------------------------------------------------------------------
// Rebuilding a tree as STP nodes, through a given factory, at width w.
struct Stp
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf;
  NodeFactory* hf;
  std::map<std::pair<int, unsigned>, ASTNode> vars;

  Stp() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    CONSTANTBV::BitVector_Boot();
    nf = &snf;
    hf = mgr.hashingNodeFactory;
    // The simplifying factory folds some of its own intermediate constants
    // through the manager's default factory, so that must be it.
    mgr.defaultNodeFactory = nf;
  }

  ASTNode var(int v, unsigned w)
  {
    const auto key = std::make_pair(v, w);
    const auto found = vars.find(key);
    if (found != vars.end())
      return found->second;
    const ASTNode s = mgr.CreateSymbol(
        (std::string(varName(v)) + "_" + std::to_string(w)).c_str(), 0, w);
    vars[key] = s;
    return s;
  }

  ASTNode konst(Const c, unsigned w)
  {
    return mgr.CreateBVConst(w, constValue(c, w));
  }

  ASTNode build(int i, NodeFactory* f, unsigned w)
  {
    const Node& n = arena[i];
    switch (n.op)
    {
      case O_VAR: return var(n.var, w);
      case O_CONST: return konst(n.c, w);
      case P_TRUE: return mgr.ASTTrue;
      case P_FALSE: return mgr.ASTFalse;
      case P_NOT: return f->CreateNode(NOT, build(n.a, f, w));
      default: break;
    }
    const ASTNode a = build(n.a, f, w);
    if (n.op == O_NOT)
      return f->CreateTerm(BVNOT, w, a);
    if (n.op == O_NEG)
      return f->CreateTerm(BVUMINUS, w, a);
    const ASTNode b = build(n.b, f, w);
    Kind k = UNDEFINED;
    switch (n.op)
    {
      case O_ADD: k = BVPLUS; break;
      case O_SUB: k = BVSUB; break;
      case O_MUL: k = BVMULT; break;
      case O_UDIV: k = BVDIV; break;
      case O_UREM: k = BVMOD; break;
      case O_SDIV: k = SBVDIV; break;
      case O_SREM: k = SBVREM; break;
      case O_SMOD: k = SBVMOD; break;
      case O_AND: k = BVAND; break;
      case O_OR: k = BVOR; break;
      case O_XOR: k = BVXOR; break;
      case O_SHL: k = BVLEFTSHIFT; break;
      case O_LSHR: k = BVRIGHTSHIFT; break;
      case O_ASHR: k = BVSRSHIFT; break;
      case P_EQ: k = EQ; break;
      case P_ULT: k = BVLT; break;
      case P_SLT: k = BVSLT; break;
      case P_UADDO: k = BVUADDO; break;
      case P_SADDO: k = BVSADDO; break;
      case P_UMULO: k = BVUMULO; break;
      case P_SMULO: k = BVSMULO; break;
      case P_USUBO: k = BVUSUBO; break;
      case P_SSUBO: k = BVSSUBO; break;
      default: break;
    }
    if (isPred(n.op))
      return f->CreateNode(k, a, b);
    return f->CreateTerm(k, w, a, b);
  }

  // Evaluate a tree of constants bottom-up: the evaluator folds one level.
  ASTNode fold(const ASTNode& n)
  {
    if (n.isConstant())
      return n;
    ASTVec kids;
    kids.reserve(n.Degree());
    for (const ASTNode& ch : n)
      kids.push_back(fold(ch));
    return NonMemberBVConstEvaluator(&mgr, n.GetKind(), kids,
                                     n.GetValueWidth());
  }

  // STP's constant evaluator's verdict on `i` at every assignment, compared
  // with the native one. The tree is built through the hashing factory so
  // nothing rewrites on the way in.
  bool evaluatorAgrees(int i, unsigned nvars, unsigned w)
  {
    const ASTNode n = build(i, hf, w);
    const Vec native = vectorOf(i, nvars, w);
    const uint64_t per = 1ull << w;
    uint64_t vals[8] = {0};
    for (uint64_t k = 0; k < native.size(); k++)
    {
      uint64_t rest = k;
      ASTNodeMap assignment;
      for (unsigned v = 0; v < nvars; v++)
      {
        vals[v] = rest % per;
        rest /= per;
        assignment[var(v, w)] = mgr.CreateBVConst(w, vals[v]);
      }
      ASTNodeMap cache;
      const ASTNode s =
          fold(SubstitutionMap::replace(n, assignment, cache, hf));
      uint64_t got;
      if (s == mgr.ASTTrue)
        got = 1;
      else if (s == mgr.ASTFalse)
        got = 0;
      else
      {
        got = 0;
        for (unsigned bit = 0; bit < w; bit++)
          if (CONSTANTBV::BitVector_bit_test(s.GetBVConst(), bit))
            got |= 1ull << bit;
      }
      if (got != native[k])
        return false;
    }
    return true;
  }
};

// ---------------------------------------------------------------------------
struct Finding
{
  int cand, target;  // trees, over the original variables x, y
  int gcand, gtarget; // the generalised rule, fresh variables included
  unsigned nvars;    // variables of the generalised rule
  std::string key;   // the generalised rule's text, for de-duplication
  bool confirmed = true;  // holds at every width tried
  unsigned failing = 0;   // bit w set: fails at width w
  bool evaluatorAgrees = true;
  bool handled = false;
  std::string snfForm;
};

// Substitute tree `from` by `to` wherever it occurs structurally in `i`.
static int substitute(int i, int from, int to)
{
  if (sameTree(i, from))
    return to;
  const Node n = arena[i]; // a copy: the recursion grows the arena
  if (n.a < 0)
    return i;
  const int a = substitute(n.a, from, to);
  const int b = n.b < 0 ? -1 : substitute(n.b, from, to);
  if (a == n.a && b == n.b)
    return i;
  Node copy = n;
  copy.a = a;
  copy.b = b;
  arena.push_back(copy);
  return (int)arena.size() - 1;
}

// Rename the variables of a rule in order of first occurrence, so that two
// findings differing only in which variable is which de-duplicate.
static void firstOccurrence(int i, std::vector<int>& order)
{
  const Node& n = arena[i];
  if (n.op == O_VAR)
  {
    if (std::find(order.begin(), order.end(), n.var) == order.end())
      order.push_back(n.var);
    return;
  }
  if (n.a >= 0)
    firstOccurrence(n.a, order);
  if (n.b >= 0)
    firstOccurrence(n.b, order);
}
static int rename(int i, const std::vector<int>& order)
{
  const Node n = arena[i]; // a copy: the recursion grows the arena
  if (n.op == O_VAR)
  {
    const int v = (int)(std::find(order.begin(), order.end(), n.var) -
                        order.begin());
    return v == n.var ? i : mkVar(v);
  }
  if (n.a < 0)
    return i;
  const int a = rename(n.a, order);
  const int b = n.b < 0 ? -1 : rename(n.b, order);
  if (a == n.a && b == n.b)
    return i;
  Node copy = n;
  copy.a = a;
  copy.b = b;
  arena.push_back(copy);
  return (int)arena.size() - 1;
}

int main(int argc, char** argv)
{
  setbuf(stdout, nullptr);
  const std::string outDir = argc > 1 ? argv[1] : "";
  const unsigned W = 4; // the search width

  // The pool: leaves, then every depth-1 term, de-duplicated by value vector
  // (keeping the smallest spelling of each).
  std::vector<int> leaves;
  leaves.push_back(mkVar(0));
  leaves.push_back(mkVar(1));
  for (int c = 0; c < C_COUNT; c++)
    leaves.push_back(mkConst((Const)c));

  std::vector<int> pool(leaves);
  for (const int l : leaves)
    for (const Op u : TERM_UNARY)
      pool.push_back(mk(u, l));
  for (const int l : leaves)
    for (const int r : leaves)
      for (const Op b : TERM_BINARY)
        pool.push_back(mk(b, l, r));

  std::map<Vec, int> byVector;
  for (const int t : pool)
  {
    const Vec v = vectorOf(t, 2, W);
    const auto found = byVector.find(v);
    if (found == byVector.end())
      byVector[v] = t;
    else if (size(t) < size(found->second))
      found->second = t;
  }
  pool.clear();
  for (const auto& e : byVector)
    pool.push_back(e.second);
  printf("pool: %zu distinct terms at width %u\n", pool.size(), W);

  const auto isConstTree = [](int t) {
    return maxVar(t) < 0;
  };

  // The targets: true, false, and the comparisons over leaves, negated or
  // not, each vector mapped to its smallest spelling. Comparisons over
  // larger terms are left out deliberately: a predicate that is equivalent
  // to a comparison of the same size is a restatement, not a simplification.
  std::map<Vec, int> targets;
  const auto offer = [&](int t) {
    const Vec v = vectorOf(t, 2, W);
    const auto found = targets.find(v);
    if (found == targets.end())
      targets[v] = t;
    else if (size(t) < size(found->second))
      found->second = t;
  };
  offer(mk(P_TRUE));
  offer(mk(P_FALSE));
  for (const int l : leaves)
    for (const int r : leaves)
    {
      if (isConstTree(l) && isConstTree(r))
        continue;
      for (const Op b : TARGET_BINARY)
      {
        const int p = mk(b, l, r);
        offer(p);
        offer(mk(P_NOT, p));
      }
    }
  printf("targets: %zu distinct vectors\n", targets.size());

  // The search: every overflow predicate over a pool term and a leaf, in
  // either order. Two depth-1 operands are left out: the rules there are
  // in the tens of thousands, and all of the fixed-bits and range kind that
  // constant bit propagation and the interval analyses already express.
  std::vector<Finding> findings;
  std::set<std::string> seen;
  int candidates = 0;
  const auto isLeaf = [](int t) {
    return arena[t].op == O_VAR || arena[t].op == O_CONST;
  };
  for (const Op o : OVERFLOW)
    for (const int l : pool)
      for (const int r : pool)
      {
        if (isConstTree(l) && isConstTree(r))
          continue;
        if (!isLeaf(l) && !isLeaf(r))
          continue;
        const int cand = mk(o, l, r);
        candidates++;
        const auto found = targets.find(vectorOf(cand, 2, W));
        if (found == targets.end())
          continue;
        // An overflow predicate costs an adder or a multiplier; a comparison
        // of the same size is cheaper, so equal sizes count.
        const int target = found->second;
        if (size(target) > size(cand))
          continue;

        // Generalise: a depth-1 operand that could be any term becomes a
        // fresh variable, in the candidate and the target alike. Each of the
        // two operands independently, then both.
        int gc = cand, gt = target;
        int fresh = 2;
        for (int side = 0; side < 2; side++)
        {
          const int operand = side == 0 ? arena[cand].a : arena[cand].b;
          if (arena[operand].op == O_VAR || arena[operand].op == O_CONST)
            continue;
          const int z = mkVar(fresh);
          const int c2 = substitute(gc, operand, z);
          const int t2 = substitute(gt, operand, z);
          if (agree(c2, t2, fresh + 1, W) && agree(c2, t2, fresh + 1, 3))
          {
            gc = c2;
            gt = t2;
            fresh++;
          }
        }
        std::vector<int> order;
        firstOccurrence(gc, order);
        firstOccurrence(gt, order);
        gc = rename(gc, order);
        gt = rename(gt, order);

        Finding f;
        f.cand = cand;
        f.target = target;
        f.gcand = gc;
        f.gtarget = gt;
        f.nvars = (unsigned)order.size();
        f.key = print(gc) + " -> " + print(gt);
        if (!seen.insert(f.key).second)
          continue;
        findings.push_back(f);
      }
  printf("%d candidates, %zu distinct generalised rules\n\n", candidates,
         findings.size());

  // Confirm each rule at the other widths, exhaustively; cross-check the
  // native semantics against STP's evaluator; ask the factory.
  Stp stp;
  for (Finding& f : findings)
  {
    for (unsigned w = 1; w <= 7; w++)
    {
      if (f.nvars * w > 20)
        continue;
      if (!agree(f.gcand, f.gtarget, f.nvars, w))
      {
        f.confirmed = false;
        f.failing |= 1u << w;
      }
    }
    const unsigned cw = (f.nvars <= 2) ? 4 : 3;
    f.evaluatorAgrees = stp.evaluatorAgrees(f.gcand, f.nvars, cw) &&
                        stp.evaluatorAgrees(f.gtarget, f.nvars, cw);

    const ASTNode simp = stp.build(f.gcand, stp.nf, 8);
    const ASTNode want = stp.build(f.gtarget, stp.nf, 8);
    const ASTNode plain = stp.build(f.gcand, stp.hf, 8);
    f.handled = (simp == want);
    if (simp == plain)
      f.snfForm = "unchanged";
    else if (f.handled)
      f.snfForm = "target";
    else
    {
      std::stringstream s;
      printer::SMTLIB2_Print1(s, simp, 0, false);
      f.snfForm = "rewritten to " + s.str();
    }
  }

  std::sort(findings.begin(), findings.end(),
            [](const Finding& a, const Finding& b) {
              return size(a.gcand) != size(b.gcand)
                         ? size(a.gcand) < size(b.gcand)
                         : a.key < b.key;
            });

  // A rule that fails only at width 1 (where 1 = -1 = smin = ones) is still
  // a rule, guarded on the width; it is listed apart. Anything failing at a
  // width above 1 is a fact of the search width alone.
  printf("== Rules the SimplifyingNodeFactory does NOT have ==\n");
  int missed = 0, guarded = 0, unsound = 0;
  for (const Finding& f : findings)
  {
    if (f.handled || !f.evaluatorAgrees || f.failing != 0)
      continue;
    missed++;
    printf("  %s\n", f.key.c_str());
    if (f.snfForm != "unchanged")
      printf("        (factory currently: %s)\n", f.snfForm.c_str());
  }
  printf("\n== Rules that hold at every width above 1 ==\n");
  for (const Finding& f : findings)
  {
    if (f.handled || !f.evaluatorAgrees || f.failing != 2u)
      continue;
    guarded++;
    printf("  %s\n", f.key.c_str());
  }
  printf("\n== Width-4 facts, not rules (failing widths listed) ==\n");
  for (const Finding& f : findings)
  {
    if (f.handled || (f.evaluatorAgrees && (f.failing == 0 || f.failing == 2u)))
      continue;
    unsound++;
    if (!f.evaluatorAgrees)
      printf("  %-60s  ** EVALUATOR DISAGREES with native semantics **\n",
             f.key.c_str());
    else
    {
      printf("  %-60s  fails at w =", f.key.c_str());
      for (unsigned w = 1; w <= 7; w++)
        if (f.failing & (1u << w))
          printf(" %u", w);
      printf("\n");
    }
  }

  printf("\n== Already handled by the factory ==\n");
  for (const Finding& f : findings)
    if (f.handled)
      printf("  %s\n", f.key.c_str());

  printf("\n%zu rules found, %d missed by the factory, %d more needing a "
         "width guard, %d width-4 facts\n",
         findings.size(), missed, guarded, unsound);

  // One SMT-LIB file per missed rule, asserting its negation at 16 bits.
  if (!outDir.empty())
  {
    int n = 0;
    for (const Finding& f : findings)
    {
      if (f.handled || !f.evaluatorAgrees || (f.failing & ~2u) != 0)
        continue;
      const unsigned w = 16;
      std::ofstream out(outDir + "/rule" + std::to_string(n++) + ".smt2");
      out << "; " << f.key << "\n(set-logic QF_BV)\n";
      for (unsigned v = 0; v < f.nvars; v++)
        out << "(declare-fun " << varName(v) << " () (_ BitVec " << w
            << "))\n";
      out << "(define-fun ones () (_ BitVec " << w << ") (_ bv"
          << constValue(C_ONES, w) << " " << w << "))\n";
      out << "(define-fun smin () (_ BitVec " << w << ") (_ bv"
          << constValue(C_SMIN, w) << " " << w << "))\n";
      out << "(define-fun smax () (_ BitVec " << w << ") (_ bv"
          << constValue(C_SMAX, w) << " " << w << "))\n";
      std::string c = print(f.gcand), t = print(f.gtarget);
      // The symbolic 0 and 1 need widths in SMT-LIB.
      for (std::string* s : {&c, &t})
      {
        std::string r;
        for (size_t i = 0; i < s->size(); i++)
        {
          const bool atStart = (i == 0 || (*s)[i - 1] == ' ');
          const bool atEnd = (i + 1 == s->size() || (*s)[i + 1] == ' ' ||
                              (*s)[i + 1] == ')');
          if (atStart && atEnd && ((*s)[i] == '0' || (*s)[i] == '1'))
            r += std::string("(_ bv") + (*s)[i] + " " + std::to_string(w) +
                 ")";
          else
            r += (*s)[i];
        }
        *s = r;
      }
      out << "(assert (not (= " << c << " " << t << ")))\n(check-sat)\n";
    }
    printf("wrote %d files to %s (each must be unsat)\n", n, outDir.c_str());
  }
  return 0;
}

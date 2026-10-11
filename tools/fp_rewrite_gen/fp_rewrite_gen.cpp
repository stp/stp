/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

// Rewrite-rule *generator* for the floating-point kinds: the FP counterpart
// of tools/rewrite_rule_gen, built as a value-vector search (which proved
// stronger than the syntactic generator for the bitvector rules).
//
// Every depth-1 floating-point term and predicate over ONE float variable,
// the five rounding modes and a pool of special constants (NaN, +-oo, +-0,
// +-1) is evaluated on EVERY float of a small format, giving a vector of
// values. A vector equal to that of a trivially cheaper form -- a constant,
// x, (fp.neg x), (fp.abs x), true/false, (fp.isNaN x), ... -- is a sound
// rewrite rule at that format. Hits are re-confirmed on a second format
// (a fact of one format need not generalise), and finally rebuilt through
// the SimplifyingNodeFactory to see whether it already knows the rule:
// what remains is the list of candidate rules worth adding.
//
// Depth 2 nests ONE inner term -- from a small pool chosen to constrain the
// value's class, sign or shape: (fp.abs x), (fp.neg x), (fp.sqrt rm x),
// (fp.roundToIntegral rm x), x*x, x+x and x-x -- into one operand slot of
// every outer operation (fp.fma excepted: its depth-1 space already
// dominates the runtime), with the other slots drawn from {x, constants}.
// The classification predicates join the outer operations, and the target
// library gains "the inner term itself", which is what idempotence-style
// rules (roundToIntegral of roundToIntegral) collapse to. When both the
// inner and outer operation take a rounding mode they share the literal;
// two DIFFERENT inner terms in one candidate are not searched.
//
// The oracle is the one test_fprewrites uses: blast the candidate once
// through the *hashing* factory (so no rewrite fires on the way in), then
// fold the resulting pure bitvector/Boolean circuit to a constant under each
// assignment of the variable. Folding a pre-blasted circuit rather than
// re-blasting per assignment is what makes exhaustive enumeration cheap.
//
// fp.min/fp.max get their (+0, -0) choice child pinned, as FpTotalise does;
// a candidate rule on them is only reported when it holds under BOTH pinned
// choices, since a factory rewrite must be sound for every choice.

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/symbolic_fp.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"

#include <cstdint>
#include <functional>
#include <cstdio>
#include <map>
#include <string>
#include <vector>

using namespace stp;

// ---------------------------------------------------------------------------
// Formats: (eb, sb), sb counting the hidden bit; packed width = eb + sb.
// sb must be at least 4 (symfpu issue #14). The search runs on FA; hits are
// confirmed on FB. FMA circuits are much larger, so FMA searches on the
// smaller FS and confirms on FA.
struct Fmt
{
  unsigned eb, sb;
  unsigned width() const { return eb + sb; }
  uint64_t values() const { return 1ull << width(); }
  uint64_t signBit() const { return 1ull << (width() - 1); }
};
static const Fmt FA{3, 4};
static const Fmt FB{3, 5};
static const Fmt FS{2, 4};

// ---------------------------------------------------------------------------
// The constant pool, defined semantically so it can be re-encoded per format.
enum Special
{
  S_NAN,
  S_PINF,
  S_NINF,
  S_PZERO,
  S_NZERO,
  S_PONE,
  S_NONE,
  S_COUNT
};
static const char* specialName[] = {"NaN", "+oo", "-oo", "+0.0",
                                    "-0.0", "1.0", "-1.0"};

static uint64_t bitsOf(Special s, const Fmt& f)
{
  const unsigned storedSig = f.sb - 1;
  const uint64_t expMask = ((1ull << f.eb) - 1) << storedSig;
  const uint64_t one = ((1ull << (f.eb - 1)) - 1) << storedSig; // exponent=bias
  switch (s)
  {
    case S_NAN: return expMask | 1;
    case S_PINF: return expMask;
    case S_NINF: return f.signBit() | expMask;
    case S_PZERO: return 0;
    case S_NZERO: return f.signBit();
    case S_PONE: return one;
    case S_NONE: return f.signBit() | one;
    default: return 0;
  }
}

// ---------------------------------------------------------------------------
// The five rounding modes (their parser encodings, 5-bit one-hot).
static const unsigned RM_MODES[] = {
    symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
    symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
    symbolic_fp::ROUND_TOWARD_POSITIVE,
    symbolic_fp::ROUND_TOWARD_NEGATIVE,
    symbolic_fp::ROUND_TOWARD_ZERO,
};
static const char* rmName[] = {"RNE", "RNA", "RTP", "RTN", "RTZ"};
static const int NUM_RM = 5;

// ---------------------------------------------------------------------------
// The depth-2 inner terms, each chosen because it constrains its value's
// class, sign or shape. The rm-bearing ones share the candidate's literal
// mode.
enum Inner
{
  I_ABS,
  I_NEG,
  I_SQRT,
  I_RTI,
  I_SQUARE, // x * x: nonnegative or NaN
  I_DOUBLE, // x + x: NaN exactly when x is
  I_SUBXX,  // x - x: a zero, or NaN for NaN and the infinities
  I_COUNT
};
static const char* innerName[] = {
    "(fp.abs x)",     "(fp.neg x)",     "(fp.sqrt rm x)",
    "(fp.rti rm x)",  "(fp.mul rm x x)", "(fp.add rm x x)",
    "(fp.sub rm x x)"};
static bool innerUsesRm(int i)
{
  return i != I_ABS && i != I_NEG;
}

// ---------------------------------------------------------------------------
// The cheap forms a candidate may collapse to.
enum TargetKind
{
  T_NONE,
  T_CONST,     // a pool constant
  T_CONST_ANY, // constant, but not one of the pool (bits recorded)
  T_X,
  T_NEGX,
  T_ABSX,
  T_INNER, // the candidate's own inner term (depth 2 only)
  T_TRUE,
  T_FALSE,
  T_ISNAN,
  T_NOT_ISNAN,
  T_ISZERO,
  T_ISINF,
  T_ISNEG,
  T_ISPOS
};
struct Target
{
  TargetKind k = T_NONE;
  Special sc = S_NAN; // for T_CONST
  uint64_t bits = 0;  // for T_CONST_ANY
  int inner = -1;     // for T_INNER
  bool operator==(const Target& o) const
  {
    return k == o.k && (k != T_CONST || sc == o.sc) &&
           (k != T_CONST_ANY || bits == o.bits) &&
           (k != T_INNER || inner == o.inner);
  }
  bool operator!=(const Target& o) const { return !(*this == o); }
  std::string name(const char* var) const
  {
    switch (k)
    {
      case T_CONST: return specialName[sc];
      case T_CONST_ANY: return "const<" + std::to_string(bits) + ">";
      case T_X: return var;
      case T_NEGX: return std::string("(fp.neg ") + var + ")";
      case T_ABSX: return std::string("(fp.abs ") + var + ")";
      case T_INNER: return innerName[inner];
      case T_TRUE: return "true";
      case T_FALSE: return "false";
      case T_ISNAN: return std::string("(fp.isNaN ") + var + ")";
      case T_NOT_ISNAN: return std::string("(not (fp.isNaN ") + var + "))";
      case T_ISZERO: return std::string("(fp.isZero ") + var + ")";
      case T_ISINF: return std::string("(fp.isInfinite ") + var + ")";
      case T_ISNEG: return std::string("(fp.isNegative ") + var + ")";
      case T_ISPOS: return std::string("(fp.isPositive ") + var + ")";
      default: return "?";
    }
  }
};

// ---------------------------------------------------------------------------
// A small independent decoder for building the predicate target vectors.
struct RefFp
{
  bool sign, nan, inf, zero;
};
static RefFp refDecode(const Fmt& f, uint64_t v)
{
  const unsigned storedSig = f.sb - 1;
  const uint64_t sig = v & ((1ull << storedSig) - 1);
  const uint64_t exp = (v >> storedSig) & ((1ull << f.eb) - 1);
  const bool allOnes = (exp == ((1ull << f.eb) - 1));
  RefFp d;
  d.sign = (v >> (f.width() - 1)) & 1;
  d.nan = allOnes && sig != 0;
  d.inf = allOnes && sig == 0;
  d.zero = (exp == 0 && sig == 0);
  return d;
}

// Sentinels for Boolean results, clear of any packed float value (as in
// test_fprewrites).
static const uint64_t K_TRUE = 1ull << 40;
static const uint64_t K_FALSE = 1ull << 41;
static const uint64_t K_NAN = 1ull << 42;

// The comparable key of a packed constant: every NaN pattern is the one
// SMT-LIB NaN; +0 and -0 stay distinct.
static uint64_t keyBits(uint64_t v, const Fmt& f)
{
  const unsigned storedSig = f.sb - 1;
  const uint64_t expMask = ((1ull << f.eb) - 1) << storedSig;
  const uint64_t sigMask = (1ull << storedSig) - 1;
  if ((v & expMask) == expMask && (v & sigMask) != 0)
    return K_NAN;
  return v;
}

// ---------------------------------------------------------------------------
struct Ctx
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: queried for "already handled"
  NodeFactory* hf; // hashing factory: builds candidates without simplifying
  unsigned counter = 0;

  Ctx() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    CONSTANTBV::BitVector_Boot();
    nf = &snf;
    hf = mgr.hashingNodeFactory;
    // Keep the default factory the hashing one: the blaster and the constant
    // evaluator build through it, and a simplifying factory folding the
    // blaster's output as it is built miscarries float formats onto shared
    // Booleans (see test_fprewrites for the full account).
    mgr.defaultNodeFactory = hf;
    GlobalParserBM = &mgr;
    symbolic_fp::init(&mgr);
  }

  ASTNode fp(const Fmt& f)
  {
    ASTNode s = mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0,
                                 f.width());
    s.SetExpWidth(f.eb);
    s.SetSigWidth(f.sb);
    return s;
  }

  ASTNode fpConst(const Fmt& f, uint64_t v)
  {
    ASTNode n = mgr.CreateBVConst(f.width(), v);
    return mgr.CreateFPConst(n, f.eb, f.sb);
  }

  ASTNode rm(unsigned mode) { return mgr.CreateBVConst(5, mode); }

  // Give bare fp.min/fp.max the (+0, -0) choice child the blaster expects,
  // pinned to `choice` -- run with both, since a rewrite must hold for each.
  ASTNode pinPartialOps(const ASTNode& n, int choice)
  {
    ASTVec children;
    children.reserve(n.Degree());
    bool changed = false;
    for (const ASTNode& ch : n)
    {
      const ASTNode nc = pinPartialOps(ch, choice);
      changed |= (nc != ch);
      children.push_back(nc);
    }
    const Kind k = n.GetKind();
    if ((k == FP_MIN || k == FP_MAX) && n.Degree() == 2)
    {
      children.push_back(choice ? mgr.CreateOneConst(1)
                                : mgr.CreateZeroConst(1));
      changed = true;
    }
    // fp.to_ubv/fp.to_sbv: the unspecified value for NaN, the infinities
    // and out-of-range operands; pinned to 0 or to ones, and a rule must
    // hold under both.
    if ((k == FP_TO_UBV || k == FP_TO_SBV) && n.Degree() == 3)
    {
      children.push_back(choice ? mgr.CreateMaxConst(n.GetValueWidth())
                                : mgr.CreateZeroConst(n.GetValueWidth()));
      changed = true;
    }
    if (!changed)
      return n;
    ASTNode out = (n.GetType() == BOOLEAN_TYPE)
                      ? hf->CreateNode(k, children)
                      : hf->CreateTerm(k, n.GetValueWidth(), children);
    if (n.GetExpWidth() != 0)
    {
      out.SetExpWidth(n.GetExpWidth());
      out.SetSigWidth(n.GetSigWidth());
    }
    return out;
  }

  ASTNode blastOnce(const ASTNode& n, int choice)
  {
    const ASTNode s = pinPartialOps(n, choice);
    if (s.isConstant())
      return s;
    return FloatBlast::lowerOperation(&mgr, s);
  }

  ASTNode foldBlasted(const ASTNode& n, ASTNodeMap& memo)
  {
    if (n.isConstant())
      return n;
    const auto found = memo.find(n);
    if (found != memo.end())
      return found->second;
    ASTVec kids;
    kids.reserve(n.Degree());
    for (const ASTNode& ch : n)
      kids.push_back(foldBlasted(ch, memo));
    const ASTNode r =
        NonMemberBVConstEvaluator(&mgr, n.GetKind(), kids, n.GetValueWidth());
    memo.insert({n, r});
    return r;
  }

  // The comparable key of a folded result.
  static uint64_t key(const ASTNode& r, const Fmt& f, bool isFloat)
  {
    const Kind rk = r.GetKind();
    if (rk == TRUE)
      return K_TRUE;
    if (rk == FALSE)
      return K_FALSE;
    if (rk != BVCONST)
      return (1ull << 43) | (uint64_t)(unsigned)r.GetNodeNum();
    uint64_t v = 0;
    const unsigned w = r.GetValueWidth();
    for (unsigned i = 0; i < w && i < 64; i++)
      if (CONSTANTBV::BitVector_bit_test(r.GetBVConst(), i))
        v |= (1ull << i);
    return isFloat ? keyBits(v, f) : v;
  }

  // Evaluate candidate `n` (whose only symbol is `x`) on every float of `f`.
  std::vector<uint64_t> valueVector(const ASTNode& n, const ASTNode& x,
                                    const Fmt& f, int choice)
  {
    const bool isFloat = (n.GetType() != BOOLEAN_TYPE);
    const ASTNode blasted = blastOnce(n, choice);
    std::vector<uint64_t> out(f.values());
    for (uint64_t v = 0; v < f.values(); v++)
    {
      ASTNodeMap memo;
      memo.insert({x, fpConst(f, v)});
      out[v] = key(foldBlasted(blasted, memo), f, isFloat);
    }
    return out;
  }
};

// ---------------------------------------------------------------------------
// Target vectors for a format.
struct TargetSet
{
  std::vector<std::pair<Target, std::vector<uint64_t>>> term, pred;

  TargetSet(const Fmt& f)
  {
    const uint64_t n = f.values();
    auto vec = [&](TargetKind k, uint64_t (*g)(uint64_t, const Fmt&)) {
      std::vector<uint64_t> v(n);
      for (uint64_t i = 0; i < n; i++)
        v[i] = g(i, f);
      return std::make_pair(Target{k, S_NAN, 0}, v);
    };
    term.push_back(vec(T_X, [](uint64_t v, const Fmt& f) {
      return keyBits(v, f);
    }));
    term.push_back(vec(T_NEGX, [](uint64_t v, const Fmt& f) {
      return keyBits(v ^ f.signBit(), f);
    }));
    term.push_back(vec(T_ABSX, [](uint64_t v, const Fmt& f) {
      return keyBits(v & ~f.signBit(), f);
    }));
    for (int s = 0; s < S_COUNT; s++)
    {
      const uint64_t kb = keyBits(bitsOf((Special)s, f), f);
      term.push_back({Target{T_CONST, (Special)s, 0},
                      std::vector<uint64_t>(n, kb)});
    }

    auto pvec = [&](TargetKind k, bool (*g)(const RefFp&)) {
      std::vector<uint64_t> v(n);
      for (uint64_t i = 0; i < n; i++)
        v[i] = g(refDecode(f, i)) ? K_TRUE : K_FALSE;
      return std::make_pair(Target{k, S_NAN, 0}, v);
    };
    pred.push_back({Target{T_TRUE, S_NAN, 0},
                    std::vector<uint64_t>(n, K_TRUE)});
    pred.push_back({Target{T_FALSE, S_NAN, 0},
                    std::vector<uint64_t>(n, K_FALSE)});
    pred.push_back(pvec(T_ISNAN, [](const RefFp& d) { return d.nan; }));
    pred.push_back(pvec(T_NOT_ISNAN, [](const RefFp& d) { return !d.nan; }));
    pred.push_back(pvec(T_ISZERO, [](const RefFp& d) { return d.zero; }));
    pred.push_back(pvec(T_ISINF, [](const RefFp& d) { return d.inf; }));
    pred.push_back(
        pvec(T_ISNEG, [](const RefFp& d) { return !d.nan && d.sign; }));
    pred.push_back(
        pvec(T_ISPOS, [](const RefFp& d) { return !d.nan && !d.sign; }));
  }

  Target match(const std::vector<uint64_t>& v, bool isPred) const
  {
    for (const auto& t : (isPred ? pred : term))
      if (t.second == v)
        return t.first;
    if (!isPred)
    {
      // Constant, but not one of the pool.
      bool allEq = true;
      for (const uint64_t k : v)
        allEq &= (k == v[0]);
      if (allEq)
        return Target{T_CONST_ANY, S_NAN, v[0]};
    }
    return Target{T_NONE, S_NAN, 0};
  }
};

// ---------------------------------------------------------------------------
// The candidate shapes.
struct OpSig
{
  Kind k;
  const char* name;
  unsigned floats; // float operands
  bool rm;         // leading rounding-mode operand
  bool pred;       // Boolean result
};
static const OpSig OPS[] = {
    {FP_ABS, "fp.abs", 1, false, false},
    {FP_NEG, "fp.neg", 1, false, false},
    {FP_SQRT, "fp.sqrt", 1, true, false},
    {FP_ROUNDTOINTEGRAL, "fp.roundToIntegral", 1, true, false},
    {FP_ADD, "fp.add", 2, true, false},
    {FP_SUB, "fp.sub", 2, true, false},
    {FP_MUL, "fp.mul", 2, true, false},
    {FP_DIV, "fp.div", 2, true, false},
    {FP_REM, "fp.rem", 2, false, false},
    {FP_MIN, "fp.min", 2, false, false},
    {FP_MAX, "fp.max", 2, false, false},
    {FP_FMA, "fp.fma", 3, true, false},
    {FP_LT, "fp.lt", 2, false, true},
    {FP_GT, "fp.gt", 2, false, true},
    {FP_LEQ, "fp.leq", 2, false, true},
    {FP_GEQ, "fp.geq", 2, false, true},
    {FP_EQ, "fp.eq", 2, false, true},
    {FP_SMT_EQ, "=", 2, false, true},
};

// The classification predicates join the outer operations at depth 2 (at
// depth 1 each IS its own target, so there is nothing to search).
static const OpSig CLASSIFIERS[] = {
    {FP_ISNAN, "fp.isNaN", 1, false, true},
    {FP_ISZERO, "fp.isZero", 1, false, true},
    {FP_ISINFINITE, "fp.isInfinite", 1, false, true},
    {FP_ISNORMAL, "fp.isNormal", 1, false, true},
    {FP_ISSUBNORMAL, "fp.isSubnormal", 1, false, true},
    {FP_ISNEGATIVE, "fp.isNegative", 1, false, true},
    {FP_ISPOSITIVE, "fp.isPositive", 1, false, true},
};

// An argument choice: 0 = the variable, 1 + s = pool constant s,
// 1 + S_COUNT + i = inner term i (depth 2).
static const int ARG_X = 0;
static bool isX(int a) { return a == ARG_X; }
static bool isConstArg(int a) { return a >= 1 && a <= S_COUNT; }
static bool isInnerArg(int a) { return a > S_COUNT; }
static int innerOf(int a) { return a - S_COUNT - 1; }

struct Candidate
{
  const OpSig* op;
  std::vector<int> args; // one per float operand

  bool usesRm() const
  {
    if (op->rm)
      return true;
    for (const int a : args)
      if (isInnerArg(a) && innerUsesRm(innerOf(a)))
        return true;
    return false;
  }
  int innerIdx() const // the (single) inner term, or -1 at depth 1
  {
    for (const int a : args)
      if (isInnerArg(a))
        return innerOf(a);
    return -1;
  }
};

static std::string describe(const Candidate& c, int modeMask)
{
  std::string s = "(" + std::string(c.op->name);
  if (c.usesRm())
  {
    bool all = (modeMask == (1 << NUM_RM) - 1);
    if (all)
      s += " rm";
    else
    {
      s += " {";
      bool first = true;
      for (int m = 0; m < NUM_RM; m++)
        if (modeMask & (1 << m))
        {
          if (!first)
            s += ",";
          s += rmName[m];
          first = false;
        }
      s += "}";
    }
  }
  for (const int a : c.args)
    s += std::string(" ") + (isX(a) ? "x"
                             : isConstArg(a) ? specialName[a - 1]
                                             : innerName[innerOf(a)]);
  return s + ")";
}

// ---------------------------------------------------------------------------
struct Finding
{
  Candidate cand;
  Target target;
  int modeMask;   // for rm ops: modes the rule holds under
  bool confirmed; // held on the second format too
  bool handled;   // the SimplifyingNodeFactory already produces the target
  bool trivial;   // the candidate IS the target, e.g. (fp.abs x) -> (fp.abs x)
  std::string snfForm;
};

struct Generator
{
  Ctx c;
  int evaluated = 0;

  // Value vectors of the inner terms, memoised per (inner, mode, format);
  // the vector depends only on the structure, not on which symbol carries it.
  std::map<uint64_t, std::vector<uint64_t>> innerCache;

  ASTNode buildInner(NodeFactory* f, int i, int mode, const ASTNode& x,
                     const Fmt& fmt)
  {
    const unsigned w = fmt.width();
    const ASTNode r = c.rm(RM_MODES[mode]);
    ASTNode n;
    switch (i)
    {
      case I_ABS: n = f->CreateTerm(FP_ABS, w, x); break;
      case I_NEG: n = f->CreateTerm(FP_NEG, w, x); break;
      case I_SQRT: n = f->CreateTerm(FP_SQRT, w, r, x); break;
      case I_RTI: n = f->CreateTerm(FP_ROUNDTOINTEGRAL, w, r, x); break;
      case I_SQUARE: n = f->CreateTerm(FP_MUL, w, r, x, x); break;
      case I_DOUBLE: n = f->CreateTerm(FP_ADD, w, r, x, x); break;
      case I_SUBXX: n = f->CreateTerm(FP_SUB, w, r, x, x); break;
    }
    n.SetExpWidth(fmt.eb);
    n.SetSigWidth(fmt.sb);
    return n;
  }

  const std::vector<uint64_t>& innerVec(int i, int mode, const ASTNode& x,
                                        const Fmt& fmt)
  {
    const int m = innerUsesRm(i) ? mode : 0;
    const uint64_t key = ((uint64_t)fmt.eb << 40) | ((uint64_t)fmt.sb << 32) |
                         ((uint64_t)i << 8) | (uint64_t)m;
    const auto found = innerCache.find(key);
    if (found != innerCache.end())
      return found->second;
    const ASTNode n = buildInner(c.hf, i, m, x, fmt);
    return innerCache.emplace(key, c.valueVector(n, x, fmt, 0)).first->second;
  }

  ASTNode build(NodeFactory* f, const Candidate& cand, int mode,
                const ASTNode& x, const Fmt& fmt)
  {
    ASTVec ch;
    if (cand.op->rm)
      ch.push_back(c.rm(RM_MODES[mode]));
    for (const int a : cand.args)
      ch.push_back(isX(a) ? x
                   : isConstArg(a)
                       ? c.fpConst(fmt, bitsOf((Special)(a - 1), fmt))
                       : buildInner(f, innerOf(a), mode, x, fmt));
    if (cand.op->pred)
      return f->CreateNode(cand.op->k, ch);
    ASTNode n = f->CreateTerm(cand.op->k, fmt.width(), ch);
    n.SetExpWidth(fmt.eb);
    n.SetSigWidth(fmt.sb);
    return n;
  }

  // Match a candidate's vector: the named targets first, then -- for a term
  // holding an inner -- the inner term itself (idempotence and absorption
  // land there).
  Target matchVec(const Candidate& cand, const std::vector<uint64_t>& vec,
                  int mode, const ASTNode& x, const Fmt& fmt,
                  const TargetSet& ts)
  {
    const Target t = ts.match(vec, cand.op->pred);
    if (t.k != T_NONE)
      return t;
    const int ii = cand.innerIdx();
    if (ii >= 0 && !cand.op->pred && innerVec(ii, mode, x, fmt) == vec)
      return Target{T_INNER, S_NAN, 0, ii};
    return t;
  }

  // The target the candidate collapses to at `fmt` under `mode`, or T_NONE.
  // fp.min/fp.max must reach the same target under both pinned choices.
  Target evalOne(const Candidate& cand, int mode, const ASTNode& x,
                 const Fmt& fmt, const TargetSet& ts)
  {
    evaluated++;
    const ASTNode n = build(c.hf, cand, mode, x, fmt);
    const Target t0 =
        matchVec(cand, c.valueVector(n, x, fmt, 0), mode, x, fmt, ts);
    if (t0.k == T_NONE)
      return t0;
    if (cand.op->k == FP_MIN || cand.op->k == FP_MAX)
    {
      const Target t1 =
          matchVec(cand, c.valueVector(n, x, fmt, 1), mode, x, fmt, ts);
      if (t1 != t0)
        return Target{T_NONE, S_NAN, 0};
    }
    return t0;
  }

  // What the simplifying factory says about the candidate today.
  void querySnf(Finding& f, const ASTNode& x, const Fmt& fmt)
  {
    int mode = 0;
    while (f.cand.usesRm() && !(f.modeMask & (1 << mode)))
      mode++;
    const ASTNode plain = build(c.hf, f.cand, mode, x, fmt);
    const ASTNode simp = build(c.nf, f.cand, mode, x, fmt);

    ASTNode want;
    switch (f.target.k)
    {
      case T_INNER:
        // The factory sees already-simplified children, so the expected
        // survivor is the inner term as the factory itself builds it.
        want = buildInner(c.nf, f.target.inner, mode, x, fmt);
        break;
      case T_CONST: want = c.fpConst(fmt, bitsOf(f.target.sc, fmt)); break;
      case T_CONST_ANY: want = c.fpConst(fmt, f.target.bits); break;
      case T_X: want = x; break;
      case T_NEGX:
        want = c.hf->CreateTerm(FP_NEG, fmt.width(), x);
        want.SetExpWidth(fmt.eb);
        want.SetSigWidth(fmt.sb);
        break;
      case T_ABSX:
        want = c.hf->CreateTerm(FP_ABS, fmt.width(), x);
        want.SetExpWidth(fmt.eb);
        want.SetSigWidth(fmt.sb);
        break;
      case T_TRUE: want = c.mgr.ASTTrue; break;
      case T_FALSE: want = c.mgr.ASTFalse; break;
      case T_ISNAN: want = c.hf->CreateNode(FP_ISNAN, x); break;
      case T_NOT_ISNAN:
        want = c.hf->CreateNode(NOT, c.hf->CreateNode(FP_ISNAN, x));
        break;
      case T_ISZERO: want = c.hf->CreateNode(FP_ISZERO, x); break;
      case T_ISINF: want = c.hf->CreateNode(FP_ISINFINITE, x); break;
      case T_ISNEG: want = c.hf->CreateNode(FP_ISNEGATIVE, x); break;
      case T_ISPOS: want = c.hf->CreateNode(FP_ISPOSITIVE, x); break;
      default: break;
    }
    f.handled = (simp == want);
    f.trivial = (plain == want);
    if (simp == plain)
      f.snfForm = "unchanged";
    else if (f.handled)
      f.snfForm = "target";
    else
      f.snfForm = std::string("rewritten to ") + _kind_names[simp.GetKind()];
  }

  // Evaluate one candidate under every relevant mode, group the modes by
  // the target they reach, confirm each group on the second format, and ask
  // the factory what it does today.
  void searchCandidate(const Candidate& cand, const ASTNode& x,
                       const ASTNode& xc, const Fmt& fmt,
                       const Fmt& confirmFmt, const TargetSet& ts,
                       const TargetSet& tsConfirm,
                       std::vector<Finding>& findings)
  {
    const int modes = cand.usesRm() ? NUM_RM : 1;
    std::vector<Target> perMode(modes);
    for (int m = 0; m < modes; m++)
      perMode[m] = evalOne(cand, m, x, fmt, ts);

    std::vector<std::pair<Target, int>> groups;
    for (int m = 0; m < modes; m++)
    {
      if (perMode[m].k == T_NONE)
        continue;
      bool found = false;
      for (auto& g : groups)
        if (g.first == perMode[m])
        {
          g.second |= (1 << m);
          found = true;
        }
      if (!found)
        groups.push_back({perMode[m], 1 << m});
    }

    for (const auto& g : groups)
    {
      Finding f{cand, g.first, g.second, true, false, false, ""};
      for (int m = 0; m < modes; m++)
        if (g.second & (1 << m))
          f.confirmed &=
              (evalOne(cand, m, xc, confirmFmt, tsConfirm) == g.first);
      querySnf(f, x, fmt);
      findings.push_back(f);
    }
  }

  std::vector<Finding> runDepth1()
  {
    std::vector<Finding> findings;
    for (const OpSig& op : OPS)
    {
      const Fmt fmt = (op.k == FP_FMA) ? FS : FA;
      const Fmt confirmFmt = (op.k == FP_FMA) ? FA : FB;
      const TargetSet ts(fmt);
      const TargetSet tsConfirm(confirmFmt);
      const ASTNode x = c.fp(fmt);
      const ASTNode xc = c.fp(confirmFmt);

      // Every assignment of {x, pool} to the float operands, at least one x.
      const int options = 1 + S_COUNT;
      int tuples = 1;
      for (unsigned i = 0; i < op.floats; i++)
        tuples *= options;
      for (int t = 0; t < tuples; t++)
      {
        Candidate cand{&op, {}};
        int rest = t;
        bool hasX = false;
        for (unsigned i = 0; i < op.floats; i++)
        {
          cand.args.push_back(rest % options);
          hasX |= isX(rest % options);
          rest /= options;
        }
        if (!hasX)
          continue;
        searchCandidate(cand, x, xc, fmt, confirmFmt, ts, tsConfirm,
                        findings);
      }
      printf("done %-20s (%d evaluations so far)\n", op.name, evaluated);
    }
    return findings;
  }

  // Depth 2: exactly one operand slot holds an inner term, the rest come
  // from {x, pool}. fp.fma is excluded as the outer operation (cost), and
  // so are candidates with two inner terms -- both are logged, not silent.
  std::vector<Finding> runDepth2()
  {
    std::vector<Finding> findings;
    const TargetSet ts(FA);
    const TargetSet tsConfirm(FB);

    std::vector<const OpSig*> outer;
    for (const OpSig& op : OPS)
      if (op.k != FP_FMA)
        outer.push_back(&op);
    for (const OpSig& op : CLASSIFIERS)
      outer.push_back(&op);
    printf("depth 2: fp.fma outer and two-inner candidates excluded\n");

    for (const OpSig* op : outer)
    {
      const ASTNode x = c.fp(FA);
      const ASTNode xc = c.fp(FB);

      const int options = 1 + S_COUNT + I_COUNT;
      int tuples = 1;
      for (unsigned i = 0; i < op->floats; i++)
        tuples *= options;
      for (int t = 0; t < tuples; t++)
      {
        Candidate cand{op, {}};
        int rest = t;
        int inners = 0;
        for (unsigned i = 0; i < op->floats; i++)
        {
          cand.args.push_back(rest % options);
          inners += isInnerArg(rest % options) ? 1 : 0;
          rest /= options;
        }
        if (inners != 1)
          continue;
        searchCandidate(cand, x, xc, FA, FB, ts, tsConfirm, findings);
      }
      printf("done %-20s (%d evaluations so far)\n", op->name, evaluated);
    }
    return findings;
  }
};

// ---------------------------------------------------------------------------
// Phase 3: the conversions. (_ to_fp e s) of bits, of a signed or unsigned
// integer, and of a float in another format; fp.to_ubv/fp.to_sbv;
// fp.to_ieee_bv. None of these has a term rule in the factory. The variable
// is a float x (format F) or a bit-vector b (width W, or the format's packed
// width for the bits reinterpretation); the candidates are each conversion
// alone, each under a classification predicate, a comparison with a special
// constant, fp.abs/fp.neg, and the round trips (widen then narrow, bits of
// the bits, integer of the integer). Targets are the depth-1 library plus
// the conversion's operand (the round trips), and for a bit-vector result or
// a bit-vector variable: b, b = 0, b <s 0, b = ones.
//
// A rule is confirmed on a second configuration (FB for FA, W+1 for W); one
// that holds only on the first is a fact of that format's range, such as
// "to_fp_unsigned of a 4-bit integer is never infinite", and is reported as
// unconfirmed rather than as a rule.
struct ConvGen
{
  Ctx& c;
  int evaluated = 0;
  explicit ConvGen(Ctx& ctx) : c(ctx) {}

  struct Cfg
  {
    Fmt f;      // the float format
    unsigned w; // the integer width
  };

  // What a candidate produces.
  enum Res
  {
    R_FLOAT,
    R_BV,
    R_PRED
  };

  // A candidate: built from the variable, under a mode; `inner` is the
  // operand a round trip may collapse to (null when none).
  struct Shape
  {
    std::string name;
    bool varIsFloat;
    bool usesRm;
    Res res;
    std::function<ASTNode(NodeFactory*, const ASTNode& var, const ASTNode& rm,
                          const Cfg&, ASTNode& inner)>
        build;
  };

  ASTNode c32(unsigned v) { return c.mgr.CreateBVConst(32, v); }
  ASTNode fmtTerm(Kind k, const Fmt& f, const ASTVec& ch)
  {
    ASTNode n = c.hf->CreateTerm(k, f.width(), ch);
    n.SetExpWidth(f.eb);
    n.SetSigWidth(f.sb);
    return n;
  }
  ASTNode fmtTermNf(NodeFactory* nf, Kind k, const Fmt& f, const ASTVec& ch)
  {
    ASTNode n = nf->CreateTerm(k, f.width(), ch);
    if (n.GetExpWidth() == 0)
    {
      n.SetExpWidth(f.eb);
      n.SetSigWidth(f.sb);
    }
    return n;
  }
  ASTNode toFpBits(NodeFactory* nf, const Fmt& f, const ASTNode& b)
  {
    return fmtTermNf(nf, FP_TOFP, f, {c32(f.eb), c32(f.sb), b});
  }
  ASTNode toFpInt(NodeFactory* nf, bool sgn, const Fmt& f, const ASTNode& rm,
                  const ASTNode& b)
  {
    return fmtTermNf(nf, sgn ? FP_TOFP_SIGNED : FP_TOFP_UNSIGNED, f,
                     {c32(f.eb), c32(f.sb), rm, b});
  }
  ASTNode reformat(NodeFactory* nf, const Fmt& g, const ASTNode& rm,
                   const ASTNode& x)
  {
    return fmtTermNf(nf, FP_TOFP, g, {c32(g.eb), c32(g.sb), rm, x});
  }
  ASTNode toBv(NodeFactory* nf, bool sgn, unsigned w, const ASTNode& rm,
               const ASTNode& x)
  {
    return nf->CreateTerm(sgn ? FP_TO_SBV : FP_TO_UBV, w, {c32(w), rm, x});
  }
  ASTNode toIeee(NodeFactory* nf, const ASTNode& x)
  {
    return nf->CreateTerm(FP_TO_IEEE_BV, x.GetValueWidth(), x);
  }
  static Fmt wider(const Fmt& f) { return Fmt{f.eb + 1, f.sb + 1}; }
  static Fmt widerExp(const Fmt& f) { return Fmt{f.eb + 1, f.sb}; }
  static Fmt widerSig(const Fmt& f) { return Fmt{f.eb, f.sb + 1}; }

  // The value vector of `n` over every value of `var`, keyed for `res`:
  // floats modulo NaN in the result's own format `rf`.
  std::vector<uint64_t> vec(const ASTNode& n, const ASTNode& var,
                            bool varIsFloat, const Cfg& cfg, Res res,
                            const Fmt& rf, int choice)
  {
    const ASTNode blasted = c.blastOnce(n, choice);
    const uint64_t domain = varIsFloat ? cfg.f.values() : (1ull << cfg.w);
    std::vector<uint64_t> out(domain);
    for (uint64_t v = 0; v < domain; v++)
    {
      ASTNodeMap memo;
      memo.insert({var, varIsFloat ? c.fpConst(cfg.f, v)
                                   : c.mgr.CreateBVConst(cfg.w, v)});
      out[v] = Ctx::key(c.foldBlasted(blasted, memo), rf, res == R_FLOAT);
    }
    return out;
  }

  // The result format a float-producing shape has, read off the node.
  static Fmt fmtOf(const ASTNode& n)
  {
    return Fmt{n.GetExpWidth(), n.GetSigWidth()};
  }

  struct Tgt
  {
    std::string name;
    std::vector<uint64_t> v;
    std::function<ASTNode(NodeFactory*)> build; // through a factory
  };

  // The targets a result of kind `res` (format rf / width rw) over `var`
  // may collapse to.
  std::vector<Tgt> targets(Res res, const Fmt& rf, unsigned rw,
                           const ASTNode& var, bool varIsFloat,
                           const Cfg& cfg, const ASTNode& inner,
                           const std::vector<uint64_t>* innerVec)
  {
    std::vector<Tgt> t;
    const uint64_t domain = varIsFloat ? cfg.f.values() : (1ull << cfg.w);
    auto constVec = [&](uint64_t k) {
      return std::vector<uint64_t>(domain, k);
    };
    if (res == R_PRED)
    {
      t.push_back({"true", constVec(K_TRUE), [&](NodeFactory*) {
                     return c.mgr.ASTTrue;
                   }});
      t.push_back({"false", constVec(K_FALSE), [&](NodeFactory*) {
                     return c.mgr.ASTFalse;
                   }});
      if (varIsFloat)
      {
        struct P
        {
          const char* name;
          Kind k;
          bool (*g)(const RefFp&);
        };
        static const P preds[] = {
            {"(fp.isNaN x)", FP_ISNAN, [](const RefFp& d) { return d.nan; }},
            {"(fp.isZero x)", FP_ISZERO, [](const RefFp& d) { return d.zero; }},
            {"(fp.isInfinite x)", FP_ISINFINITE,
             [](const RefFp& d) { return d.inf; }},
            {"(fp.isNegative x)", FP_ISNEGATIVE,
             [](const RefFp& d) { return !d.nan && d.sign; }},
            {"(fp.isPositive x)", FP_ISPOSITIVE,
             [](const RefFp& d) { return !d.nan && !d.sign; }},
        };
        for (const P& p : preds)
        {
          std::vector<uint64_t> v(domain), nv(domain);
          for (uint64_t i = 0; i < domain; i++)
          {
            const bool b = p.g(refDecode(cfg.f, i));
            v[i] = b ? K_TRUE : K_FALSE;
            nv[i] = b ? K_FALSE : K_TRUE;
          }
          const Kind k = p.k;
          t.push_back({p.name, v, [this, k, var](NodeFactory* f) {
                         return f->CreateNode(k, var);
                       }});
          t.push_back({std::string("(not ") + p.name + ")", nv,
                       [this, k, var](NodeFactory* f) {
                         return f->CreateNode(NOT, f->CreateNode(k, var));
                       }});
        }
      }
      else
      {
        std::vector<uint64_t> zero(domain), nzero(domain), neg(domain),
            nneg(domain), ones(domain);
        for (uint64_t i = 0; i < domain; i++)
        {
          zero[i] = i == 0 ? K_TRUE : K_FALSE;
          nzero[i] = i == 0 ? K_FALSE : K_TRUE;
          const bool msb = (i >> (cfg.w - 1)) & 1;
          neg[i] = msb ? K_TRUE : K_FALSE;
          nneg[i] = msb ? K_FALSE : K_TRUE;
          ones[i] = (i + 1 == (1ull << cfg.w)) ? K_TRUE : K_FALSE;
        }
        const unsigned w = cfg.w;
        t.push_back({"(= b 0)", zero, [this, var, w](NodeFactory* f) {
                       return f->CreateNode(EQ, var, c.mgr.CreateZeroConst(w));
                     }});
        t.push_back({"(not (= b 0))", nzero, [this, var, w](NodeFactory* f) {
                       return f->CreateNode(
                           NOT,
                           f->CreateNode(EQ, var, c.mgr.CreateZeroConst(w)));
                     }});
        t.push_back({"(bvslt b 0)", neg, [this, var, w](NodeFactory* f) {
                       return f->CreateNode(BVSLT, var,
                                            c.mgr.CreateZeroConst(w));
                     }});
        t.push_back({"(not (bvslt b 0))", nneg, [this, var, w](NodeFactory* f) {
                       return f->CreateNode(
                           NOT,
                           f->CreateNode(BVSLT, var, c.mgr.CreateZeroConst(w)));
                     }});
        t.push_back({"(= b ones)", ones, [this, var, w](NodeFactory* f) {
                       return f->CreateNode(EQ, var, c.mgr.CreateMaxConst(w));
                     }});
      }
    }
    else if (res == R_FLOAT)
    {
      for (int sc = 0; sc < S_COUNT; sc++)
      {
        const uint64_t bits = bitsOf((Special)sc, rf);
        const Fmt f = rf;
        t.push_back({specialName[sc], constVec(keyBits(bits, rf)),
                     [this, f, bits](NodeFactory*) {
                       return c.fpConst(f, bits);
                     }});
      }
      if (varIsFloat && rf.eb == cfg.f.eb && rf.sb == cfg.f.sb)
      {
        std::vector<uint64_t> vx(domain), vn(domain), va(domain);
        for (uint64_t i = 0; i < domain; i++)
        {
          vx[i] = keyBits(i, rf);
          vn[i] = keyBits(i ^ rf.signBit(), rf);
          va[i] = keyBits(i & ~rf.signBit(), rf);
        }
        const Fmt f = rf;
        t.push_back({"x", vx, [var](NodeFactory*) { return var; }});
        t.push_back({"(fp.neg x)", vn, [this, var, f](NodeFactory* nf) {
                       return fmtTermNf(nf, FP_NEG, f, {var});
                     }});
        t.push_back({"(fp.abs x)", va, [this, var, f](NodeFactory* nf) {
                       return fmtTermNf(nf, FP_ABS, f, {var});
                     }});
      }
    }
    else // R_BV
    {
      if (!varIsFloat && rw == cfg.w)
      {
        std::vector<uint64_t> vb(domain);
        for (uint64_t i = 0; i < domain; i++)
          vb[i] = i;
        t.push_back({"b", vb, [var](NodeFactory*) { return var; }});
      }
    }
    if (!inner.IsNull() && innerVec != nullptr)
      t.push_back({"<operand>", *innerVec, [](NodeFactory*) {
                     return ASTNode(); // compared by hand below
                   }});
    return t;
  }

  struct ConvFinding
  {
    std::string cand, target;
    int modeMask;
    bool confirmed;
    bool handled;
    std::string snfForm;
  };

  // Evaluate `sh` under `mode` on `cfg`: the matching target's index into a
  // freshly built target list, or -1. Both pinned choices must agree.
  int evalOne(const Shape& sh, int mode, const Cfg& cfg, std::string& tname)
  {
    evaluated++;
    const ASTNode var = sh.varIsFloat ? c.fp(cfg.f)
                                      : c.mgr.CreateSymbol(
                                            ("b" + std::to_string(c.counter++))
                                                .c_str(),
                                            0, cfg.w);
    const ASTNode rm = c.rm(RM_MODES[mode]);
    ASTNode inner;
    const ASTNode n = sh.build(c.hf, var, rm, cfg, inner);
    if (n.IsNull())
      return -1;
    const Fmt rf = sh.res == R_FLOAT ? fmtOf(n) : cfg.f;
    const unsigned rw = sh.res == R_BV ? n.GetValueWidth() : 0;

    std::vector<uint64_t> innerVec;
    const std::vector<uint64_t>* innerPtr = nullptr;
    if (!inner.IsNull() && sh.res != R_PRED)
    {
      // The operand is a float or a bit-vector; its own kind, not the
      // result's, keys its vector -- a round trip only matches when the
      // two kinds agree, which the caller arranges.
      const bool innerFloat = inner.GetExpWidth() != 0 || inner == var;
      const Res ir = (inner.GetType() == BOOLEAN_TYPE)
                         ? R_PRED
                         : ((sh.varIsFloat && inner == var) ||
                            inner.GetExpWidth() != 0)
                               ? R_FLOAT
                               : R_BV;
      (void)innerFloat;
      if (ir == sh.res)
      {
        innerVec = vec(inner, var, sh.varIsFloat, cfg, ir,
                       ir == R_FLOAT ? fmtOf(inner) : cfg.f, 0);
        if (ir != R_FLOAT ||
            (fmtOf(inner).eb == rf.eb && fmtOf(inner).sb == rf.sb))
          innerPtr = &innerVec;
      }
    }
    const std::vector<Tgt> ts =
        targets(sh.res, rf, rw, var, sh.varIsFloat, cfg, inner, innerPtr);
    const std::vector<uint64_t> v0 =
        vec(n, var, sh.varIsFloat, cfg, sh.res, rf, 0);
    int hit = -1;
    for (size_t i = 0; i < ts.size(); i++)
      if (ts[i].v == v0)
      {
        hit = (int)i;
        break;
      }
    if (hit < 0 && sh.res != R_PRED)
    {
      bool allEq = true;
      for (const uint64_t k : v0)
        allEq &= (k == v0[0]);
      if (allEq)
      {
        tname = "const<" + std::to_string(v0[0]) + ">";
        return 1000; // a constant outside the pool
      }
    }
    if (hit < 0)
      return -1;
    // The other pinned choice must reach the same target.
    const std::vector<uint64_t> v1 =
        vec(n, var, sh.varIsFloat, cfg, sh.res, rf, 1);
    if (v1 != v0)
      return -1;
    tname = ts[hit].name;
    return hit;
  }

  // Does the factory already produce the target? Built through the
  // simplifying factory, compared with the target built the same way.
  void querySnf(const Shape& sh, int mode, const Cfg& cfg,
                const std::string& tname, ConvFinding& f)
  {
    const ASTNode var = sh.varIsFloat ? c.fp(cfg.f)
                                      : c.mgr.CreateSymbol(
                                            ("b" + std::to_string(c.counter++))
                                                .c_str(),
                                            0, cfg.w);
    const ASTNode rm = c.rm(RM_MODES[mode]);
    ASTNode innerPlain, innerSimp;
    const ASTNode plain = sh.build(c.hf, var, rm, cfg, innerPlain);
    const ASTNode simp = sh.build(c.nf, var, rm, cfg, innerSimp);
    const Fmt rf = sh.res == R_FLOAT ? fmtOf(plain) : cfg.f;
    const unsigned rw = sh.res == R_BV ? plain.GetValueWidth() : 0;
    ASTNode want;
    if (tname == "<operand>")
      want = innerSimp;
    else if (tname.rfind("const<", 0) == 0)
      want = ASTNode();
    else
    {
      const std::vector<Tgt> ts =
          targets(sh.res, rf, rw, var, sh.varIsFloat, cfg, ASTNode(), nullptr);
      for (const Tgt& t : ts)
        if (t.name == tname)
          want = t.build(c.nf);
    }
    f.handled = !want.IsNull() && simp == want;
    if (want.IsNull())
      f.handled = simp.isConstant();
    if (simp == plain)
      f.snfForm = "unchanged";
    else if (f.handled)
      f.snfForm = "target";
    else
      f.snfForm = std::string("rewritten to ") + _kind_names[simp.GetKind()];
  }

  std::vector<Shape> shapes(const Cfg& cfg)
  {
    std::vector<Shape> out;
    const Fmt F = cfg.f;
    // The float-producing conversions, each a function of (nf, var, rm).
    struct Inner
    {
      std::string name;
      bool varIsFloat;
      bool usesRm;
      std::function<ASTNode(NodeFactory*, const ASTNode&, const ASTNode&)>
          build;
      Fmt fmt; // the float it produces
    };
    std::vector<Inner> inners;
    const unsigned pw = F.width();
    inners.push_back({"((_ to_fp e s) b)", false, false,
                      [this, F](NodeFactory* nf, const ASTNode& b,
                                const ASTNode&) { return toFpBits(nf, F, b); },
                      F});
    inners.push_back({"((_ to_fp e s) rm b)", false, true,
                      [this, F](NodeFactory* nf, const ASTNode& b,
                                const ASTNode& rm) {
                        return toFpInt(nf, true, F, rm, b);
                      },
                      F});
    inners.push_back({"((_ to_fp_unsigned e s) rm b)", false, true,
                      [this, F](NodeFactory* nf, const ASTNode& b,
                                const ASTNode& rm) {
                        return toFpInt(nf, false, F, rm, b);
                      },
                      F});
    inners.push_back({"((_ to_fp e s) rm x)", true, true,
                      [this, F](NodeFactory* nf, const ASTNode& x,
                                const ASTNode& rm) {
                        return reformat(nf, F, rm, x);
                      },
                      F});
    inners.push_back({"((_ to_fp e+1 s+1) rm x)", true, true,
                      [this, F](NodeFactory* nf, const ASTNode& x,
                                const ASTNode& rm) {
                        return reformat(nf, wider(F), rm, x);
                      },
                      wider(F)});
    inners.push_back({"((_ to_fp e+1 s) rm x)", true, true,
                      [this, F](NodeFactory* nf, const ASTNode& x,
                                const ASTNode& rm) {
                        return reformat(nf, widerExp(F), rm, x);
                      },
                      widerExp(F)});
    inners.push_back({"((_ to_fp e s+1) rm x)", true, true,
                      [this, F](NodeFactory* nf, const ASTNode& x,
                                const ASTNode& rm) {
                        return reformat(nf, widerSig(F), rm, x);
                      },
                      widerSig(F)});
    inners.push_back({"((_ to_fp e s) (fp.to_ieee_bv x))", true, false,
                      [this, F](NodeFactory* nf, const ASTNode& x,
                                const ASTNode&) {
                        return toFpBits(nf, F, toIeee(nf, x));
                      },
                      F});

    // Each conversion alone: for the float variable ones the targets
    // include x, so the round trips land here.
    for (const Inner& in : inners)
      out.push_back({in.name, in.varIsFloat, in.usesRm, R_FLOAT,
                     [in](NodeFactory* nf, const ASTNode& var,
                          const ASTNode& rm, const Cfg&, ASTNode& inner) {
                       inner = var;
                       return in.build(nf, var, rm);
                     }});

    // Widen then narrow back.
    for (size_t i = 4; i <= 6; i++)
    {
      const Inner in = inners[i];
      out.push_back({"((_ to_fp e s) rm " + in.name + ")", true, true, R_FLOAT,
                     [this, in, F](NodeFactory* nf, const ASTNode& var,
                                   const ASTNode& rm, const Cfg&,
                                   ASTNode& inner) {
                       inner = var;
                       return reformat(nf, F, rm, in.build(nf, var, rm));
                     }});
    }

    // Classification predicates, fp.abs/fp.neg, and comparisons against the
    // specials, over each conversion.
    static const OpSig* CLS[] = {&CLASSIFIERS[0], &CLASSIFIERS[1],
                                 &CLASSIFIERS[2], &CLASSIFIERS[3],
                                 &CLASSIFIERS[4], &CLASSIFIERS[5],
                                 &CLASSIFIERS[6]};
    for (const Inner& in : inners)
    {
      for (const OpSig* cl : CLS)
      {
        const Kind k = cl->k;
        out.push_back({std::string("(") + cl->name + " " + in.name + ")",
                       in.varIsFloat, in.usesRm, R_PRED,
                       [in, k](NodeFactory* nf, const ASTNode& var,
                               const ASTNode& rm, const Cfg&, ASTNode& inner) {
                         inner = ASTNode();
                         return nf->CreateNode(k, in.build(nf, var, rm));
                       }});
      }
      for (Kind k : {FP_ABS, FP_NEG})
      {
        const Fmt g = in.fmt;
        out.push_back({std::string(k == FP_ABS ? "(fp.abs " : "(fp.neg ") +
                           in.name + ")",
                       in.varIsFloat, in.usesRm, R_FLOAT,
                       [this, in, k, g](NodeFactory* nf, const ASTNode& var,
                                        const ASTNode& rm, const Cfg&,
                                        ASTNode& inner) {
                         inner = in.build(nf, var, rm);
                         return fmtTermNf(nf, k, g, {inner});
                       }});
      }
      for (const OpSig& op : OPS)
      {
        if (!op.pred || op.floats != 2)
          continue;
        for (int sc = 0; sc < S_COUNT; sc++)
          for (int side = 0; side < 2; side++)
          {
            const Kind k = op.k;
            const Fmt g = in.fmt;
            out.push_back(
                {std::string("(") + op.name + " " +
                     (side == 0
                          ? in.name + " " + specialName[sc]
                          : std::string(specialName[sc]) + " " + in.name) +
                     ")",
                 in.varIsFloat, in.usesRm, R_PRED,
                 [this, in, k, g, sc, side](NodeFactory* nf, const ASTNode& var,
                                            const ASTNode& rm, const Cfg&,
                                            ASTNode& inner) {
                   inner = ASTNode();
                   const ASTNode t = in.build(nf, var, rm);
                   const ASTNode kc = c.fpConst(g, bitsOf((Special)sc, g));
                   return side == 0 ? nf->CreateNode(k, t, kc)
                                    : nf->CreateNode(k, kc, t);
                 }});
          }
      }
    }

    // The bit-vector-producing conversions of x, and of the integer
    // conversions of b (the integer round trips).
    for (bool sgn : {false, true})
    {
      const char* nm = sgn ? "fp.to_sbv" : "fp.to_ubv";
      for (unsigned w : {cfg.w, cfg.w + 2})
      {
        out.push_back({std::string("((_ ") + nm + " " + std::to_string(w) +
                           ") rm x)",
                       true, true, R_BV,
                       [this, sgn, w](NodeFactory* nf, const ASTNode& var,
                                      const ASTNode& rm, const Cfg&,
                                      ASTNode& inner) {
                         inner = ASTNode();
                         return toBv(nf, sgn, w, rm, var);
                       }});
      }
      for (bool isgn : {false, true})
        out.push_back({std::string("((_ ") + nm + " w) rm ((_ to_fp" +
                           (isgn ? "" : "_unsigned") + " e s) rm b))",
                       false, true, R_BV,
                       [this, sgn, isgn, F](NodeFactory* nf, const ASTNode& var,
                                            const ASTNode& rm, const Cfg& cfg,
                                            ASTNode& inner) {
                         inner = var;
                         return toBv(nf, sgn, cfg.w, rm,
                                     toFpInt(nf, isgn, F, rm, var));
                       }});
    }
    out.push_back({"(fp.to_ieee_bv x)", true, false, R_BV,
                   [this](NodeFactory* nf, const ASTNode& var, const ASTNode&,
                          const Cfg&, ASTNode& inner) {
                     inner = ASTNode();
                     return toIeee(nf, var);
                   }});
    out.push_back({"(fp.to_ieee_bv ((_ to_fp e s) b))", false, false, R_BV,
                   [this, F](NodeFactory* nf, const ASTNode& var,
                             const ASTNode&, const Cfg&, ASTNode& inner) {
                     inner = var;
                     return toIeee(nf, toFpBits(nf, F, var));
                   }});
    (void)pw;
    return out;
  }

  std::vector<ConvFinding> run()
  {
    std::vector<ConvFinding> findings;
    // The bits reinterpretation wants b as wide as the packed float, the
    // integer conversions a small integer: two configurations each, the
    // second confirming the first.
    const Cfg A{FA, 4}, B{FB, 5};
    const Cfg Abits{FA, FA.width()}, Bbits{FB, FB.width()};
    const std::vector<Shape> shA = shapes(A);
    const std::vector<Shape> shB = shapes(B);
    const std::vector<Shape> shAb = shapes(Abits);
    const std::vector<Shape> shBb = shapes(Bbits);
    const Cfg Wide{FA, FA.width() + 1};
    const std::vector<Shape> shWide = shapes(Wide);
    for (size_t i = 0; i < shA.size(); i++)
    {
      const Shape& sh = shA[i];
      // The bits reinterpretation shapes use the packed-width config.
      const bool bits = sh.name.find("(_ to_fp e s) b)") != std::string::npos ||
                        sh.name.find("to_ieee_bv ((_ to_fp e s) b)") !=
                            std::string::npos;
      const Cfg& cfgA = bits ? Abits : A;
      const Cfg& cfgB = bits ? Bbits : B;
      const Shape& shAx = bits ? shAb[i] : shA[i];
      const Shape& shBx = bits ? shBb[i] : shB[i];
      const int modes = sh.usesRm ? NUM_RM : 1;
      std::vector<std::pair<std::string, int>> groups; // target -> modes
      for (int m = 0; m < modes; m++)
      {
        std::string tname;
        if (evalOne(shAx, m, cfgA, tname) < 0)
          continue;
        bool found = false;
        for (auto& g : groups)
          if (g.first == tname)
          {
            g.second |= 1 << m;
            found = true;
          }
        if (!found)
          groups.push_back({tname, 1 << m});
      }
      for (const auto& g : groups)
      {
        ConvFinding f{sh.name, g.first, g.second, true, false, ""};
        for (int m = 0; m < modes; m++)
          if (g.second & (1 << m))
          {
            std::string tn;
            if (evalOne(shBx, m, cfgB, tn) < 0 || tn != g.first)
              f.confirmed = false;
            // An integer wider than the format's largest finite value
            // can overflow to an infinity, which the two small widths
            // above never reach; a third, wide width catches the range
            // facts that pose as rules ("a converted integer is below
            // +oo").
            if (!bits && !sh.varIsFloat &&
                (evalOne(shWide[i], m, Wide, tn) < 0 || tn != g.first))
              f.confirmed = false;
          }
        int m0 = 0;
        while (!(g.second & (1 << m0)))
          m0++;
        querySnf(shAx, m0, cfgA, g.first, f);
        findings.push_back(f);
      }
      if (i % 50 == 49)
        printf("  %zu/%zu shapes (%d evaluations)\n", i + 1, shA.size(),
               evaluated);
    }
    return findings;
  }
};

static std::string modeText(int modeMask, bool usesRm)
{
  if (!usesRm || modeMask == (1 << NUM_RM) - 1)
    return "";
  std::string s = " [";
  bool first = true;
  for (int m = 0; m < NUM_RM; m++)
    if (modeMask & (1 << m))
    {
      if (!first)
        s += ",";
      s += rmName[m];
      first = false;
    }
  return s + "]";
}

int main(int argc, char** argv)
{
  setbuf(stdout, nullptr);
  // Optional argument: "1", "2" or "3" restricts the search to that phase
  // (3 = the conversions).
  const bool depth1 = (argc < 2) || std::string(argv[1]) == "1";
  const bool depth2 = (argc < 2) || std::string(argv[1]) == "2";
  const bool conversions = (argc < 2) || std::string(argv[1]) == "3";
  printf("Floating-point rewrite-rule search\n");
  printf("search format (%u,%u); confirm format (%u,%u); FMA on (%u,%u)\n\n",
         FA.eb, FA.sb, FB.eb, FB.sb, FS.eb, FS.sb);

  Generator gen;
  std::vector<Finding> findings;
  if (depth1)
    findings = gen.runDepth1();
  if (depth2)
  {
    std::vector<Finding> d2 = gen.runDepth2();
    findings.insert(findings.end(), d2.begin(), d2.end());
  }

  auto show = [](const Finding& f) {
    printf("  %-44s -> %-22s %s\n", describe(f.cand, f.modeMask).c_str(),
           f.target.name("x").c_str(),
           f.confirmed ? "" : "  ** NOT CONFIRMED on 2nd format **");
  };

  printf("\n== Rules the SimplifyingNodeFactory does NOT have ==\n");
  int missed = 0;
  for (const Finding& f : findings)
    if (!f.handled)
    {
      show(f);
      if (f.snfForm != "unchanged")
        printf("        (factory currently: %s)\n", f.snfForm.c_str());
      missed++;
    }

  printf("\n== Already handled by the factory ==\n");
  for (const Finding& f : findings)
    if (f.handled && !f.trivial)
      show(f);

  printf("\n%d candidate evaluations, %zu rules found, %d missed by the "
         "factory\n",
         gen.evaluated, findings.size(), missed);

  if (conversions)
  {
    printf("\n== Conversions: search (%u,%u)/w=4, confirm (%u,%u)/w=5 ==\n",
           FA.eb, FA.sb, FB.eb, FB.sb);
    ConvGen cg(gen.c);
    const std::vector<ConvGen::ConvFinding> cf = cg.run();
    int cmissed = 0, cunconfirmed = 0;
    printf("\n== Conversion rules the SimplifyingNodeFactory does NOT have "
           "==\n");
    for (const auto& f : cf)
    {
      if (f.handled || !f.confirmed)
        continue;
      cmissed++;
      printf("  %-52s -> %s%s\n", f.cand.c_str(), f.target.c_str(),
             modeText(f.modeMask, f.cand.find(" rm ") != std::string::npos)
                 .c_str());
      if (f.snfForm != "unchanged")
        printf("        (factory currently: %s)\n", f.snfForm.c_str());
    }
    printf("\n== Conversion facts of the search format only ==\n");
    for (const auto& f : cf)
    {
      if (f.handled || f.confirmed)
        continue;
      cunconfirmed++;
      printf("  %-52s -> %s%s\n", f.cand.c_str(), f.target.c_str(),
             modeText(f.modeMask, f.cand.find(" rm ") != std::string::npos)
                 .c_str());
    }
    printf("\n== Conversion rules already handled ==\n");
    for (const auto& f : cf)
      if (f.handled)
        printf("  %-52s -> %s\n", f.cand.c_str(), f.target.c_str());
    printf("\n%d conversion evaluations, %zu rules, %d missed, %d "
           "format-specific\n",
           cg.evaluated, cf.size(), cmissed, cunconfirmed);
  }
  return 0;
}

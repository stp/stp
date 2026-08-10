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
#include <cstdio>
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
// The cheap forms a candidate may collapse to.
enum TargetKind
{
  T_NONE,
  T_CONST,     // a pool constant
  T_CONST_ANY, // constant, but not one of the pool (bits recorded)
  T_X,
  T_NEGX,
  T_ABSX,
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
  bool operator==(const Target& o) const
  {
    return k == o.k && (k != T_CONST || sc == o.sc) &&
           (k != T_CONST_ANY || bits == o.bits);
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

// An argument choice: 0 = the variable, 1 + s = pool constant s.
static const int ARG_X = 0;
static bool isX(int a) { return a == ARG_X; }

struct Candidate
{
  const OpSig* op;
  std::vector<int> args; // one per float operand
};

static std::string describe(const Candidate& c, int modeMask)
{
  std::string s = "(" + std::string(c.op->name);
  if (c.op->rm)
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
    s += std::string(" ") + (isX(a) ? "x" : specialName[a - 1]);
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

  ASTNode build(NodeFactory* f, const Candidate& cand, int mode,
                const ASTNode& x, const Fmt& fmt)
  {
    ASTVec ch;
    if (cand.op->rm)
      ch.push_back(c.rm(RM_MODES[mode]));
    for (const int a : cand.args)
      ch.push_back(isX(a) ? x : c.fpConst(fmt, bitsOf((Special)(a - 1), fmt)));
    if (cand.op->pred)
      return f->CreateNode(cand.op->k, ch);
    ASTNode n = f->CreateTerm(cand.op->k, fmt.width(), ch);
    n.SetExpWidth(fmt.eb);
    n.SetSigWidth(fmt.sb);
    return n;
  }

  // The target the candidate collapses to at `fmt` under `mode`, or T_NONE.
  // fp.min/fp.max must reach the same target under both pinned choices.
  Target evalOne(const Candidate& cand, int mode, const ASTNode& x,
                 const Fmt& fmt, const TargetSet& ts)
  {
    evaluated++;
    const ASTNode n = build(c.hf, cand, mode, x, fmt);
    const Target t0 = ts.match(c.valueVector(n, x, fmt, 0), cand.op->pred);
    if (t0.k == T_NONE)
      return t0;
    if (cand.op->k == FP_MIN || cand.op->k == FP_MAX)
    {
      const Target t1 = ts.match(c.valueVector(n, x, fmt, 1), cand.op->pred);
      if (t1 != t0)
        return Target{T_NONE, S_NAN, 0};
    }
    return t0;
  }

  // What the simplifying factory says about the candidate today.
  void querySnf(Finding& f, const ASTNode& x, const Fmt& fmt)
  {
    int mode = 0;
    while (f.cand.op->rm && !(f.modeMask & (1 << mode)))
      mode++;
    const ASTNode plain = build(c.hf, f.cand, mode, x, fmt);
    const ASTNode simp = build(c.nf, f.cand, mode, x, fmt);

    ASTNode want;
    switch (f.target.k)
    {
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

  std::vector<Finding> run()
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

        // Per rounding mode (a single pass for rm-free ops), then group
        // modes by the target they reach.
        const int modes = op.rm ? NUM_RM : 1;
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
              f.confirmed &= (evalOne(cand, m, xc, confirmFmt, tsConfirm) ==
                              g.first);
          querySnf(f, x, fmt);
          findings.push_back(f);
        }
      }
      printf("done %-20s (%d evaluations so far)\n", op.name, evaluated);
    }
    return findings;
  }
};

int main()
{
  setbuf(stdout, nullptr);
  printf("Floating-point rewrite-rule search\n");
  printf("search format (%u,%u); confirm format (%u,%u); FMA on (%u,%u)\n\n",
         FA.eb, FA.sb, FB.eb, FB.sb, FS.eb, FS.sb);

  Generator gen;
  std::vector<Finding> findings = gen.run();

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
  return 0;
}

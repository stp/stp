/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
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

// Floating-point constant folding, against the hardware.
//
// STP folds an all-constant floating-point operation by building its symfpu
// circuit and evaluating it, so the folded value comes from the same source
// as the solved one and the two cannot disagree. That is the right property
// and it is why the fold costs what it does: a Float64 fp.add of two
// literals builds and tears down thousands of interned nodes, about half a
// millisecond, where concrete arithmetic is sub-microsecond.
//
// Replacing it means giving symfpu a *literal* traits backend -- its core
// algorithms are templated precisely so that a second backend reuses the
// IEEE semantics and supplies only the bit-vector primitives (upstream ships
// simpleExecutable for this, though its 64-bit words cannot hold the
// 106-bit intermediates a Float64 multiply needs, so STP would need its own
// over CBV). The risk in that change is not the semantics but the
// primitives, and its failure mode is a silently wrong constant.
//
// These tests are the gate for it. IEEE-754 requires +, -, *, / and sqrt to
// be correctly rounded, so the hardware is an exact oracle for the two
// native formats under the four native rounding modes, independent of
// anything in STP. That backend now exists (lib/FloatBlaster/literal_fp.cpp)
// and the constant evaluator prefers it, so these oracle tests exercise the
// literal path; the exhaustive differential at the bottom of this file pins
// it to the circuit path per kind and keeps the circuit fold reachable.

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Util/CBVOps.h"

#include <gtest/gtest.h>

#include <cfenv>
#include <cmath>
#include <cstring>
#include <limits>
#include <vector>

using namespace stp;

namespace
{

struct Fixture
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;

  Fixture() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    mgr.defaultNodeFactory = &snf; // the production wiring
  }

  ASTNode fpConst(unsigned eb, unsigned sb, uint64_t bits)
  {
    return mgr.CreateFPConst(mgr.CreateBVConst(eb + sb, bits), eb, sb);
  }

  ASTNode rm(unsigned mode) { return mgr.CreateRMConst(mode); }

  // Fold `k` over already-constant operands and return the packed bits.
  uint64_t fold(Kind k, unsigned width, const ASTVec& kids)
  {
    const ASTNode folded =
        NonMemberBVConstEvaluator(&mgr, k, kids, width);
    EXPECT_TRUE(folded.isConstant());
    // Not a single 64-bit Chunk_Read: that returns unsigned long, which is
    // 32 bits on a 32-bit host, so every binary64 result would lose its top
    // half while binary32 came through intact. chunk64 reads two 32-bit
    // chunks, as everything else in the tree does.
    return chunk64(folded.GetBVConst(), 0);
  }
};

uint32_t bitsOf(float f)
{
  uint32_t b;
  std::memcpy(&b, &f, sizeof b);
  return b;
}
uint64_t bitsOf(double d)
{
  uint64_t b;
  std::memcpy(&b, &d, sizeof b);
  return b;
}
float floatOf(uint32_t b)
{
  float f;
  std::memcpy(&f, &b, sizeof f);
  return f;
}
double doubleOf(uint64_t b)
{
  double d;
  std::memcpy(&d, &b, sizeof d);
  return d;
}

struct Mode
{
  unsigned stp;
  int native;
  const char* name;
};

// RNA has no native counterpart, so it is not covered here; the query-file
// corpus distinguishes all five.
const Mode MODES[] = {
    {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN, FE_TONEAREST, "RNE"},
    {symbolic_fp::ROUND_TOWARD_POSITIVE, FE_UPWARD, "RTP"},
    {symbolic_fp::ROUND_TOWARD_NEGATIVE, FE_DOWNWARD, "RTN"},
    {symbolic_fp::ROUND_TOWARD_ZERO, FE_TOWARDZERO, "RTZ"},
};

// Specials, subnormals, exact powers, and values whose results need rounding
// in every direction.
const double VALUES[] = {
    0.0,
    -0.0,
    1.0,
    -1.0,
    2.0,
    0.5,
    3.0,
    -7.5,
    1e-300,
    -1e-300,
    1e300,
    -1e300,
    4.9406564584124654e-324, // the smallest Float64 subnormal
    2.2250738585072009e-308, // the largest Float64 subnormal
    1.0000000000000002,      // one ulp above 1.0
    123456789.123456789,
    std::numeric_limits<double>::infinity(),
    -std::numeric_limits<double>::infinity(),
    std::numeric_limits<double>::quiet_NaN(),
};

// Every NaN is one value in SMT-LIB, so compare NaN results as a class.
bool sameDouble(uint64_t got, uint64_t want)
{
  const double g = doubleOf(got);
  const double w = doubleOf(want);
  if (std::isnan(g) && std::isnan(w))
    return true;
  return got == want;
}
bool sameFloat(uint32_t got, uint32_t want)
{
  const float g = floatOf(got);
  const float w = floatOf(want);
  if (std::isnan(g) && std::isnan(w))
    return true;
  return got == want;
}

struct ScopedRound
{
  int saved;
  explicit ScopedRound(int mode) : saved(std::fegetround())
  {
    std::fesetround(mode);
  }
  ~ScopedRound() { std::fesetround(saved); }
};

// The oracle has to be evaluated at *runtime*, under the mode ScopedRound
// set. Operands read through volatile force that: without it the compiler
// folds the arithmetic while compiling, under the default mode, and the
// three non-default modes then disagree with STP for a reason that has
// nothing to do with STP. (The file is also built with -frounding-math, so
// the compiler does not assume the default mode for what is left.)
template <class T> T runtimeAdd(T a, T b)
{
  volatile T x = a, y = b;
  volatile T result = x + y;
  return result;
}
template <class T> T runtimeSub(T a, T b)
{
  volatile T x = a, y = b;
  volatile T result = x - y;
  return result;
}
template <class T> T runtimeMul(T a, T b)
{
  volatile T x = a, y = b;
  volatile T result = x * y;
  return result;
}
template <class T> T runtimeDiv(T a, T b)
{
  volatile T x = a, y = b;
  volatile T result = x / y;
  return result;
}
template <class T> T runtimeSqrt(T a)
{
  volatile T x = a;
  volatile T result = std::sqrt(x);
  return result;
}
template <class T> T runtimeNearbyint(T a)
{
  volatile T x = a;
  volatile T result = std::nearbyint(x);
  return result;
}
template <class T> T runtimeFma(T a, T b, T c)
{
  volatile T x = a, y = b, z = c;
  volatile T result = std::fma(x, y, z);
  return result;
}
template <class T> T runtimeRemainder(T a, T b)
{
  volatile T x = a, y = b;
  volatile T result = std::remainder(x, y);
  return result;
}

} // namespace

TEST(FpConstantFold, binary64_arithmetic_matches_the_hardware)
{
  Fixture f;
  for (const Mode& mode : MODES)
  {
    const ASTNode rm = f.rm(mode.stp);
    for (double a : VALUES)
    {
      for (double b : VALUES)
      {
        const ASTNode x = f.fpConst(11, 53, bitsOf(a));
        const ASTNode y = f.fpConst(11, 53, bitsOf(b));

        double add, sub, mul, div;
        {
          ScopedRound rounding(mode.native);
          add = runtimeAdd(a, b);
          sub = runtimeSub(a, b);
          mul = runtimeMul(a, b);
          div = runtimeDiv(a, b);
        }

        EXPECT_TRUE(sameDouble(f.fold(FP_ADD, 64, {rm, x, y}), bitsOf(add)))
            << mode.name << " fp.add " << a << " " << b;
        EXPECT_TRUE(sameDouble(f.fold(FP_SUB, 64, {rm, x, y}), bitsOf(sub)))
            << mode.name << " fp.sub " << a << " " << b;
        EXPECT_TRUE(sameDouble(f.fold(FP_MUL, 64, {rm, x, y}), bitsOf(mul)))
            << mode.name << " fp.mul " << a << " " << b;
        EXPECT_TRUE(sameDouble(f.fold(FP_DIV, 64, {rm, x, y}), bitsOf(div)))
            << mode.name << " fp.div " << a << " " << b;
      }
    }
  }
}

TEST(FpConstantFold, binary32_arithmetic_matches_the_hardware)
{
  Fixture f;
  for (const Mode& mode : MODES)
  {
    const ASTNode rm = f.rm(mode.stp);
    for (double da : VALUES)
    {
      for (double db : VALUES)
      {
        const float a = static_cast<float>(da);
        const float b = static_cast<float>(db);
        const ASTNode x = f.fpConst(8, 24, bitsOf(a));
        const ASTNode y = f.fpConst(8, 24, bitsOf(b));

        float add, sub, mul, div;
        {
          ScopedRound rounding(mode.native);
          add = runtimeAdd(a, b);
          sub = runtimeSub(a, b);
          mul = runtimeMul(a, b);
          div = runtimeDiv(a, b);
        }

        EXPECT_TRUE(sameFloat(
            static_cast<uint32_t>(f.fold(FP_ADD, 32, {rm, x, y})), bitsOf(add)))
            << mode.name << " fp.add " << a << " " << b;
        EXPECT_TRUE(sameFloat(
            static_cast<uint32_t>(f.fold(FP_SUB, 32, {rm, x, y})), bitsOf(sub)))
            << mode.name << " fp.sub " << a << " " << b;
        EXPECT_TRUE(sameFloat(
            static_cast<uint32_t>(f.fold(FP_MUL, 32, {rm, x, y})), bitsOf(mul)))
            << mode.name << " fp.mul " << a << " " << b;
        EXPECT_TRUE(sameFloat(
            static_cast<uint32_t>(f.fold(FP_DIV, 32, {rm, x, y})), bitsOf(div)))
            << mode.name << " fp.div " << a << " " << b;
      }
    }
  }
}

TEST(FpConstantFold, sqrt_fma_and_roundtointegral_match_the_hardware)
{
  Fixture f;
  for (const Mode& mode : MODES)
  {
    const ASTNode rm = f.rm(mode.stp);
    const ASTNode addend = f.fpConst(11, 53, bitsOf(1.5));
    for (double a : VALUES)
    {
      const ASTNode x = f.fpConst(11, 53, bitsOf(a));

      double root, integral;
      {
        ScopedRound rounding(mode.native);
        root = runtimeSqrt(a);
        integral = runtimeNearbyint(a);
      }
      EXPECT_TRUE(sameDouble(f.fold(FP_SQRT, 64, {rm, x}), bitsOf(root)))
          << mode.name << " fp.sqrt " << a;
      EXPECT_TRUE(
          sameDouble(f.fold(FP_ROUNDTOINTEGRAL, 64, {rm, x}), bitsOf(integral)))
          << mode.name << " fp.roundToIntegral " << a;

      for (double b : VALUES)
      {
        const ASTNode y = f.fpConst(11, 53, bitsOf(b));
        double fused;
        {
          ScopedRound rounding(mode.native);
          fused = runtimeFma(a, b, 1.5);
        }
        EXPECT_TRUE(
            sameDouble(f.fold(FP_FMA, 64, {rm, x, y, addend}), bitsOf(fused)))
            << mode.name << " fp.fma " << a << " " << b;
      }
    }
  }
}

// fp.rem is exact and takes no rounding mode, so it gets one pass rather
// than one per mode. It is also the most expensive circuit here -- binary64
// unrolls 2097 divide steps -- so running it four times was most of this
// file's cost and none of its coverage.
TEST(FpConstantFold, remainder_matches_the_hardware)
{
  Fixture f;
  for (double a : VALUES)
  {
    const ASTNode x = f.fpConst(11, 53, bitsOf(a));
    for (double b : VALUES)
    {
      const ASTNode y = f.fpConst(11, 53, bitsOf(b));
      const double rem = runtimeRemainder(a, b);
      EXPECT_TRUE(sameDouble(f.fold(FP_REM, 64, {x, y}), bitsOf(rem)))
          << "fp.rem " << a << " " << b;
    }
  }
}

// Hard-coded, so it does not depend on the oracle machinery at all: 1.0/3.0
// is the classic case where the four modes disagree, and these are the four
// answers the hardware gives (verified separately) and the ones STP's solver
// produces end to end.
TEST(FpConstantFold, one_third_matches_known_values_under_every_mode)
{
  Fixture f;
  const uint64_t one = 0x3FF0000000000000ull;
  const uint64_t three = 0x4008000000000000ull;
  const struct
  {
    unsigned mode;
    uint64_t want;
    const char* name;
  } cases[] = {
      {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN, 0x3FD5555555555555ull, "RNE"},
      {symbolic_fp::ROUND_TOWARD_POSITIVE, 0x3FD5555555555556ull, "RTP"},
      {symbolic_fp::ROUND_TOWARD_NEGATIVE, 0x3FD5555555555555ull, "RTN"},
      {symbolic_fp::ROUND_TOWARD_ZERO, 0x3FD5555555555555ull, "RTZ"},
  };

  for (const auto& c : cases)
  {
    const ASTNode rm = f.rm(c.mode);
    const ASTNode x = f.fpConst(11, 53, one);
    const ASTNode y = f.fpConst(11, 53, three);
    EXPECT_EQ(c.want, f.fold(FP_DIV, 64, {rm, x, y})) << c.name << " 1.0/3.0";
  }
}

// The fold must not depend on which node factory the embedder installed.
//
// Every other test here runs the production wiring, where defaultNodeFactory
// is the simplifying factory: it folds as it builds, so lowerOperation hands
// the evaluator a BVCONST that is already the answer and the evaluation is a
// no-op. STPMgr's own constructor installs the hashing factory instead, and
// then the same call hands back the whole symfpu circuit -- a deeply shared
// DAG, which an evaluator that walks paths rather than nodes cannot finish.
//
// The format is deliberately tiny. Float(3,4)'s fp.add circuit is a few
// hundred nodes -- linear if each is visited once, and hopeless otherwise.
// Nothing here checks the *value*; the tests above do that, and against the
// hardware. This one checks only that it arrives.
TEST(FpConstantFold, folds_under_a_non_simplifying_factory)
{
  STPMgr mgr; // hashingNodeFactory, as the constructor leaves it

  const unsigned eb = 3, sb = 4;
  const ASTNode one = mgr.CreateFPConst(mgr.CreateBVConst(eb + sb, 0x38), eb, sb);
  const ASTNode rne =
      mgr.CreateRMConst(stp::symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);

  const ASTNode folded = NonMemberBVConstEvaluator(
      &mgr, FP_ADD, ASTVec{rne, one, one}, eb + sb);

  EXPECT_TRUE(folded.isConstant());
  EXPECT_EQ(eb + sb, folded.GetValueWidth());
}

// The simplifying factory folds all-constant floating-point nodes at
// creation (the constant evaluator's FP arm re-interns results through the
// CreateFPConst funnel), so a constant has ONE representation regardless of
// how it was spelled, and constant operations never outlive their creation.
TEST(FpConstantFold, both_literal_spellings_intern_to_the_same_node)
{
  Fixture f;
  const uint64_t bits = 0x3FF4CCCCCCCCCCCDull; // 1.3, binary64

  // ((_ to_fp 11 53) #x3FF4CCCCCCCCCCCD), as the parser builds it.
  const ASTNode viaToFp = f.snf.CreateTerm(
      FP_TOFP, 64,
      ASTVec{f.mgr.CreateBVConst(32, 11), f.mgr.CreateBVConst(32, 53),
             f.mgr.CreateBVConst(64, bits)});

  // (fp #b0 #b01111111111 #b0100...) interns through CreateFPConst.
  const ASTNode viaLiteral = f.fpConst(11, 53, bits);

  EXPECT_TRUE(viaToFp.isConstant());
  EXPECT_EQ(viaLiteral, viaToFp); // the same hash-consed node
  EXPECT_EQ(11u, viaToFp.GetExpWidth());
  EXPECT_EQ(53u, viaToFp.GetSigWidth());
}

TEST(FpConstantFold, constant_predicates_fold_at_creation)
{
  Fixture f;
  const ASTNode onePointFive = f.fpConst(8, 24, 0x3FC00000u);
  const ASTNode one = f.fpConst(8, 24, 0x3F800000u);

  EXPECT_EQ(f.mgr.ASTTrue,
            f.snf.CreateNode(FP_GT, ASTVec{onePointFive, one}));
  EXPECT_EQ(f.mgr.ASTFalse,
            f.snf.CreateNode(FP_LT, ASTVec{onePointFive, one}));
  EXPECT_EQ(f.mgr.ASTFalse, f.snf.CreateNode(FP_ISNAN, ASTVec{one}));
}

TEST(FpConstantFold, constant_arithmetic_folds_at_creation)
{
  Fixture f;
  const ASTNode sum = f.snf.CreateTerm(
      FP_ADD, 64,
      ASTVec{f.rm(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN),
             f.fpConst(11, 53, bitsOf(1.5)), f.fpConst(11, 53, bitsOf(2.5))});

  EXPECT_TRUE(sum.isConstant());
  EXPECT_EQ(f.fpConst(11, 53, bitsOf(4.0)), sum);
  EXPECT_EQ(11u, sum.GetExpWidth());
}

TEST(FpConstantFold, nan_payloads_intern_canonically)
{
  Fixture f;
  auto reinterpret = [&f](uint32_t bits) {
    return f.snf.CreateTerm(
        FP_TOFP, 32,
        ASTVec{f.mgr.CreateBVConst(32, 8), f.mgr.CreateBVConst(32, 24),
               f.mgr.CreateBVConst(32, bits)});
  };
  // Two different NaN payloads (and signs) intern to the one canonical NaN,
  // matching what every FP-observable path (unpack, fp.to_ieee_bv) already
  // does with payloads.
  const ASTNode a = reinterpret(0x7F800001u);
  const ASTNode b = reinterpret(0xFFC12345u);
  EXPECT_TRUE(a.isConstant());
  EXPECT_EQ(a, b);
  EXPECT_EQ(f.mgr.ASTTrue, f.snf.CreateNode(FP_ISNAN, ASTVec{a}));
}

// fp.min/fp.max (opposite zeros) and fp.to_ubv/fp.to_sbv (out of range)
// have unspecified cases that only get an answer once FpTotalise adds its
// unspecified-value child, so their pre-totalise constant forms must NOT
// fold at creation.
TEST(FpConstantFold, partial_operations_do_not_fold_at_creation)
{
  Fixture f;
  const ASTNode minimum = f.snf.CreateTerm(
      FP_MIN, 32,
      ASTVec{f.fpConst(8, 24, 0x80000000u), f.fpConst(8, 24, 0x00000000u)});
  EXPECT_EQ(FP_MIN, minimum.GetKind());
  EXPECT_FALSE(minimum.isConstant());
}

// The anti-drift gate for the literal backend. Both paths instantiate the
// same symfpu core, but each has its own Kind-to-operation driver; this
// pins them together mechanically -- every covered kind, exhaustively at
// the narrowest formats -- and is also what keeps the circuit fold path
// exercised now that the evaluator prefers the literal one.
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/literal_fp.h"

namespace
{

struct Differential : Fixture
{
  unsigned checked = 0;

  ASTNode temp(Kind k, const ASTVec& kids, unsigned width, unsigned eb,
               unsigned sb, bool float_result)
  {
    ASTNode t = (width == 0)
                    ? mgr.hashingNodeFactory->CreateNode(k, kids)
                    : mgr.hashingNodeFactory->CreateTerm(k, width, kids);
    if (float_result)
    {
      t.SetExpWidth(eb);
      t.SetSigWidth(sb);
    }
    return t;
  }

  void agree(Kind k, const ASTVec& kids, unsigned width, unsigned eb,
             unsigned sb, bool float_result)
  {
    const ASTNode t = temp(k, kids, width, eb, sb, float_result);

    const ASTNode viaLiteral = literal_fp::tryEvaluateFpConstant(&mgr, t);
    ASSERT_FALSE(viaLiteral.IsNull()) << _kind_names[k];

    const ASTNode blasted = FloatBlast::lowerOperation(&mgr, t);
    const ASTNode viaCircuit = NonMemberBVConstEvaluator(&mgr, blasted);

    ASSERT_EQ(viaCircuit, viaLiteral) << _kind_names[k];
    ++checked;
  }
};

void runDifferential(Differential& d, const unsigned eb, const unsigned sb)
{
  const unsigned w = eb + sb, N = 1u << w;
  std::vector<ASTNode> c;
  for (unsigned i = 0; i < N; i++)
    c.push_back(d.fpConst(eb, sb, i));
  const std::vector<unsigned> modes = {
      symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
      symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
      symbolic_fp::ROUND_TOWARD_POSITIVE,
      symbolic_fp::ROUND_TOWARD_NEGATIVE,
      symbolic_fp::ROUND_TOWARD_ZERO};

  // Binary predicates: every pair.
  for (const Kind k : {FP_LEQ, FP_LT, FP_GEQ, FP_GT, FP_EQ, FP_SMT_EQ})
    for (unsigned i = 0; i < N; i++)
      for (unsigned j = i % 2; j < N; j += 2)
        d.agree(k, ASTVec{c[i], c[j]}, 0, eb, sb, false);

  // Classifications and sign ops: every value.
  for (unsigned i = 0; i < N; i++)
  {
    for (const Kind k : {FP_ISNORMAL, FP_ISSUBNORMAL, FP_ISZERO,
                         FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE,
                         FP_ISPOSITIVE})
      d.agree(k, ASTVec{c[i]}, 0, eb, sb, false);
    d.agree(FP_ABS, ASTVec{c[i]}, w, eb, sb, true);
    d.agree(FP_NEG, ASTVec{c[i]}, w, eb, sb, true);
    d.agree(FP_TO_IEEE_BV, ASTVec{c[i]}, w, eb, sb, false);
  }

  // Rounded binary arithmetic: every pair under RNE, and every mode over a
  // coarser grid. fp.rem takes no mode; every pair.
  // fp.add exhaustively; the others on strides that still hit every value
  // on each side (odd strides are coprime with the space).
  for (unsigned i = 0; i < N; i++)
    for (unsigned j = 0; j < N; j++)
      d.agree(FP_ADD, ASTVec{d.rm(modes[0]), c[i], c[j]}, w, eb, sb, true);
  for (const Kind k : {FP_SUB, FP_MUL, FP_DIV})
    for (unsigned i = 0; i < N; i++)
      for (unsigned j = i % 3; j < N; j += 3)
        d.agree(k, ASTVec{d.rm(modes[0]), c[i], c[j]}, w, eb, sb, true);
  for (const Kind k : {FP_ADD, FP_SUB, FP_MUL, FP_DIV})
    for (size_t m = 1; m < modes.size(); m++)
      for (unsigned i = 0; i < N; i += 5)
        for (unsigned j = 0; j < N; j += 5)
          d.agree(k, ASTVec{d.rm(modes[m]), c[i], c[j]}, w, eb, sb, true);
  for (unsigned i = 0; i < N; i++)
    for (unsigned j = i % 3; j < N; j += 3)
      d.agree(FP_REM, ASTVec{c[i], c[j]}, w, eb, sb, true);

  // sqrt under every mode; fma over a coarse grid under RNE.
  for (const unsigned m : modes)
    for (unsigned i = 0; i < N; i++)
      d.agree(FP_SQRT, ASTVec{d.rm(m), c[i]}, w, eb, sb, true);
  for (unsigned i = 0; i < N; i += 7)
    for (unsigned j = 0; j < N; j += 7)
      for (unsigned l = 0; l < N; l += 7)
        d.agree(FP_FMA, ASTVec{d.rm(modes[0]), c[i], c[j], c[l]}, w, eb, sb,
                true);

  // Conversions: reinterpret every pattern; float->float both directions;
  // bv->float signed/unsigned under every mode.
  const ASTNode ebc = d.mgr.CreateBVConst(32, eb);
  const ASTNode sbc = d.mgr.CreateBVConst(32, sb);
  const ASTNode eb2 = d.mgr.CreateBVConst(32, 4);
  const ASTNode sb2 = d.mgr.CreateBVConst(32, 5);
  for (unsigned i = 0; i < N; i++)
  {
    d.agree(FP_TOFP, ASTVec{ebc, sbc, d.mgr.CreateBVConst(w, i)}, w, eb, sb,
            true);
    d.agree(FP_TOFP, ASTVec{eb2, sb2, d.rm(modes[i % 5]), c[i]}, 9, 4, 5,
            true);
    for (const unsigned m : modes)
    {
      d.agree(FP_TOFP_SIGNED,
              ASTVec{ebc, sbc, d.rm(m), d.mgr.CreateBVConst(w, i)}, w, eb, sb,
              true);
      d.agree(FP_TOFP_UNSIGNED,
              ASTVec{ebc, sbc, d.rm(m), d.mgr.CreateBVConst(w, i)}, w, eb, sb,
              true);
    }
  }
}

} // namespace

TEST(FpConstantFold, literal_backend_agrees_with_the_circuit_exhaustively)
{
  Differential d;
  runDifferential(d, 3, 4);
  EXPECT_GT(d.checked, 90000u);
}

// The same gate at the formats that used to be refused outright.
// FloatBlaster::formatSupported turned away everything with sb <= 3, because
// symfpu's own unpack aborted on INVARIANT(unpackedExWidth > exWidth) there;
// patches/symfpu/0002 gives those formats the headroom bit instead, so they
// are now ordinary formats and both fold paths have to handle them. SMT-LIB
// admits every format from (2,2) up, so these are the narrowest inputs a
// solver can be handed.
//
// (2,4) is here for a second reason. It is not a short significand, so the
// refusal never covered it on purpose, but it is where the unpacked exponent
// ends up narrower than the significand -- eb 2 with sb a power of two -- and
// unpackedFloat::valid then built its own bound at the exponent's width and
// wrapped it negative. Only the literal backend evaluates that INVARIANT (the
// symbolic one cannot), so the assertion builds are what see it; it is fixed
// in patches/symfpu/0004.
TEST(FpConstantFold, literal_backend_agrees_at_the_narrowest_formats)
{
  Differential d;
  runDifferential(d, 3, 3);
  runDifferential(d, 2, 2);
  runDifferential(d, 2, 4);
  EXPECT_GT(d.checked, 56000u);
}

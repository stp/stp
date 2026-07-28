/***********
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
**********************/

/*
 * Exhaustive tests for AchievableImage, the under-approximate image
 * engine behind RemoveUnconstrained's ground-path predicate collapse.
 *
 * The engine is validated behaviourally through decide(), against a
 * brute-force oracle (the independent 64-bit constant evaluator):
 *
 *  - Soundness (always): a collapse must be genuine -- both polarities
 *    really achievable -- and the returned witnesses must produce their
 *    polarity when the chain is re-evaluated externally.
 *  - Completeness (only while the image reports isExact()): decide()
 *    must collapse exactly when the brute-force image can produce both
 *    polarities. This checks the interval transfer functions in both
 *    directions, and the inversion rules via the witnesses.
 *
 * When the engine has degraded to samples, false negatives are allowed;
 * a hit-rate is printed for eyeballing coverage.
 */

#include "stp/Simplifier/AchievableImage.h"
#include "stp/Simplifier/Simplifier.h"
#include <algorithm>
#include <gtest/gtest.h>
#include <set>
#include <vector>

using namespace stp;

namespace
{

struct Ctx
{
  STPMgr mgr;

  Ctx()
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;
  }

  ASTNode konst(uint64_t value, unsigned width)
  {
    return mgr.CreateBVConst(width, value);
  }

  GroundStep bin(Kind k, unsigned w, uint64_t c, bool pathFirst)
  {
    GroundStep s;
    s.kind = k;
    s.inWidth = w;
    s.outWidth = w;
    s.pathIndex = pathFirst ? 0 : 1;
    s.constants.push_back(konst(c, w));
    return s;
  }

  GroundStep unary(Kind k, unsigned w)
  {
    GroundStep s;
    s.kind = k;
    s.inWidth = w;
    s.outWidth = w;
    s.pathIndex = 0;
    return s;
  }

  GroundStep extend(Kind k, unsigned w, unsigned W)
  {
    GroundStep s;
    s.kind = k;
    s.inWidth = w;
    s.outWidth = W;
    s.pathIndex = 0;
    return s;
  }

  GroundStep extract(unsigned w, unsigned high, unsigned low)
  {
    GroundStep s;
    s.kind = BVEXTRACT;
    s.inWidth = w;
    s.outWidth = high - low + 1;
    s.pathIndex = 0;
    s.constants.push_back(konst(high, 32));
    s.constants.push_back(konst(low, 32));
    return s;
  }

  GroundStep concat(unsigned w, uint64_t c, unsigned cWidth, bool pathFirst)
  {
    GroundStep s;
    s.kind = BVCONCAT;
    s.inWidth = w;
    s.outWidth = w + cWidth;
    s.pathIndex = pathFirst ? 0 : 1;
    s.constants.push_back(konst(c, cWidth));
    return s;
  }

  // Both operands are the path: (op t t) -- squaring, doubling.
  GroundStep same(Kind k, unsigned w)
  {
    GroundStep s;
    s.kind = k;
    s.inWidth = w;
    s.outWidth = w;
    s.pathIndex = 0;
    s.samePathAllOperands = true;
    return s;
  }
};

// Independent oracle: evaluate one step with the 64-bit evaluator.
uint64_t evalStep64(const GroundStep& s, uint64_t x)
{
  std::vector<uint64_t> args;
  std::vector<unsigned> widths;
  if (s.samePathAllOperands)
  {
    args = {x, x};
    widths = {s.inWidth, s.inWidth};
  }
  else if (s.kind == BVSX || s.kind == BVZX)
  {
    args.push_back(x);
    widths.push_back(s.inWidth);
  }
  else
  {
    const size_t arity = s.constants.size() + 1;
    size_t ci = 0;
    for (size_t i = 0; i < arity; i++)
    {
      if (i == s.pathIndex)
      {
        args.push_back(x);
        widths.push_back(s.inWidth);
      }
      else
      {
        const ASTNode& cn = s.constants[ci++];
        args.push_back(cn.GetUnsignedConst());
        widths.push_back(cn.GetValueWidth());
      }
    }
  }
  return NonMemberBVConstEvaluator64(s.kind, args, widths, s.outWidth);
}

uint64_t evalChain64(const std::vector<GroundStep>& steps, uint64_t x)
{
  for (const GroundStep& s : steps)
    x = evalStep64(s, x);
  return x;
}

bool evalPred64(Kind pred, bool pathFirst, uint64_t v, uint64_t k, unsigned w)
{
  return pathFirst ? NonMemberBVConstPredicateEvaluator64(pred, v, k, w)
                   : NonMemberBVConstPredicateEvaluator64(pred, k, v, w);
}

const Kind COMPARISONS[] = {BVGT, BVGE, BVLT, BVLE, BVSGT, BVSGE, BVSLT, BVSLE};

// Global tally over samples-rep decisions, printed at the end for
// eyeballing how much the fallback misses.
size_t g_samplesBoth = 0, g_samplesHit = 0;

std::string describe(const std::vector<GroundStep>& steps)
{
  std::string out;
  for (const GroundStep& s : steps)
  {
    out += " [" + std::string(_kind_names[s.kind]) + " path@" +
           std::to_string(s.pathIndex) + " " + std::to_string(s.inWidth) +
           "->" + std::to_string(s.outWidth);
    for (const ASTNode& cn : s.constants)
      out += " c=" + std::to_string(cn.GetUnsignedConst());
    out += "]";
  }
  return out;
}

// Run every predicate probe over the chain and compare decide() with
// the brute-force truth. `kValues` limits the constants probed for the
// comparisons (EQ always probes every value of the output domain).
void checkChain(Ctx& c, const std::vector<GroundStep>& steps, unsigned varWidth,
                const std::vector<uint64_t>* kValues = NULL)
{
  AchievableImage img(c.mgr, varWidth);
  for (const GroundStep& s : steps)
    ASSERT_TRUE(img.apply(s));
  const bool exact = img.isExact();
  const unsigned outW = steps.empty() ? varWidth : steps.back().outWidth;

  std::set<uint64_t> image;
  for (uint64_t x = 0; x < (1ull << varWidth); x++)
    image.insert(evalChain64(steps, x));

  const uint64_t domain = 1ull << outW;

  // EQ over the whole output domain.
  for (uint64_t k = 0; k < domain; k++)
  {
    AchievableImage::Decision d = img.decide(EQ, true, c.konst(k, outW));
    const bool bothPossible = image.count(k) > 0 && image.size() >= 2;
    if (exact)
      ASSERT_EQ(d.collapse, bothPossible)
          << "EQ completeness, k=" << k << " outW=" << outW;
    else
    {
      ASSERT_TRUE(!d.collapse || bothPossible) << "EQ soundness, k=" << k;
      g_samplesBoth += bothPossible;
      g_samplesHit += d.collapse;
    }
    if (d.collapse)
    {
      ASSERT_EQ(evalChain64(steps, d.witnessTrue.GetUnsignedConst()), k);
      ASSERT_NE(evalChain64(steps, d.witnessFalse.GetUnsignedConst()), k);
    }
  }

  // The eight comparisons, both operand orders. Probe constants are
  // masked into the output domain (CreateBVConst would truncate them
  // for the engine; the oracle must see the same value).
  std::vector<uint64_t> ks;
  if (kValues != NULL)
  {
    for (const uint64_t k : *kValues)
      if (std::find(ks.begin(), ks.end(), k & (domain - 1)) == ks.end())
        ks.push_back(k & (domain - 1));
  }
  else
    for (uint64_t k = 0; k < domain; k++)
      ks.push_back(k);

  for (const Kind pred : COMPARISONS)
    for (const bool pathFirst : {true, false})
      for (const uint64_t k : ks)
      {
        bool canTrue = false, canFalse = false;
        for (const uint64_t v : image)
        {
          if (evalPred64(pred, pathFirst, v, k, outW))
            canTrue = true;
          else
            canFalse = true;
        }
        const bool bothPossible = canTrue && canFalse;

        AchievableImage::Decision d =
            img.decide(pred, pathFirst, c.konst(k, outW));
        if (exact)
          ASSERT_EQ(d.collapse, bothPossible)
              << "completeness: pred=" << _kind_names[pred]
              << " first=" << pathFirst << " k=" << k << describe(steps);
        else
        {
          ASSERT_TRUE(!d.collapse || bothPossible)
              << "soundness: pred=" << pred << " first=" << pathFirst
              << " k=" << k;
          g_samplesBoth += bothPossible;
          g_samplesHit += d.collapse;
        }
        if (d.collapse)
        {
          const uint64_t vt = evalChain64(steps, d.witnessTrue.GetUnsignedConst());
          const uint64_t vf =
              evalChain64(steps, d.witnessFalse.GetUnsignedConst());
          ASSERT_TRUE(evalPred64(pred, pathFirst, vt, k, outW));
          ASSERT_FALSE(evalPred64(pred, pathFirst, vf, k, outW));
        }
      }
}

// Every single-step configuration at width `w`, over every constant.
std::vector<std::vector<GroundStep>> allSingleSteps(Ctx& c, unsigned w)
{
  std::vector<std::vector<GroundStep>> chains;
  const uint64_t domain = 1ull << w;

  const Kind commutative[] = {BVPLUS, BVMULT, BVAND, BVOR, BVXOR};
  for (const Kind k : commutative)
    for (uint64_t cv = 0; cv < domain; cv++)
      chains.push_back({c.bin(k, w, cv, true)});

  const Kind positional[] = {BVSUB,        BVDIV,        BVMOD,
                             SBVDIV,       SBVREM,       SBVMOD,
                             BVLEFTSHIFT,  BVRIGHTSHIFT, BVSRSHIFT};
  for (const Kind k : positional)
    for (const bool first : {true, false})
      for (uint64_t cv = 0; cv < domain; cv++)
        chains.push_back({c.bin(k, w, cv, first)});

  chains.push_back({c.same(BVMULT, w)});
  chains.push_back({c.same(BVPLUS, w)});
  chains.push_back({c.same(BVAND, w)});
  chains.push_back({c.same(BVXOR, w)});
  chains.push_back({c.unary(BVUMINUS, w)});
  chains.push_back({c.unary(BVNOT, w)});
  chains.push_back({c.extend(BVZX, w, w + 2)});
  chains.push_back({c.extend(BVSX, w, w + 2)});
  chains.push_back({c.extend(BVZX, w, w)});
  chains.push_back({c.extend(BVSX, w, w)});

  for (unsigned low = 0; low < w; low++)
    for (unsigned high = low; high < w; high++)
      chains.push_back({c.extract(w, high, low)});

  for (const bool first : {true, false})
    for (uint64_t cv = 0; cv < 4; cv++)
      chains.push_back({c.concat(w, cv, 2, first)});

  return chains;
}

} // namespace

TEST(AchievableImage_Exhaustive, no_steps)
{
  // The variable directly under the predicate: the full domain.
  Ctx c;
  checkChain(c, {}, 3);
  checkChain(c, {}, 1);
}

TEST(AchievableImage_Exhaustive, single_step_width3)
{
  Ctx c;
  for (const auto& chain : allSingleSteps(c, 3))
    checkChain(c, chain, 3);
}

TEST(AchievableImage_Exhaustive, single_step_width4)
{
  Ctx c;
  const std::vector<uint64_t> ks = {0, 1, 5, 7, 8, 11, 15};
  for (const auto& chain : allSingleSteps(c, 4))
    checkChain(c, chain, 4, &ks);
}

TEST(AchievableImage_Exhaustive, two_step_chains_width3)
{
  Ctx c;
  const unsigned w = 3;

  // A trimmed pool: the interesting constants for each op, rather than
  // the full cross product of the single-step tests.
  auto poolFor = [&](unsigned inW) {
    std::vector<GroundStep> pool;
    const uint64_t m = (1ull << inW) - 1;
    pool.push_back(c.bin(BVPLUS, inW, 3 & m, true));
    pool.push_back(c.bin(BVSUB, inW, 2 & m, true));
    pool.push_back(c.bin(BVSUB, inW, 2 & m, false));
    pool.push_back(c.bin(BVMULT, inW, 2 & m, true));
    pool.push_back(c.bin(BVMULT, inW, 3 & m, true));
    pool.push_back(c.bin(BVDIV, inW, 0, true));
    pool.push_back(c.bin(BVDIV, inW, 2 & m, true));
    pool.push_back(c.bin(BVDIV, inW, 3 & m, false));
    pool.push_back(c.bin(BVMOD, inW, 3 & m, true));
    pool.push_back(c.bin(BVMOD, inW, 0, true));
    pool.push_back(c.bin(BVMOD, inW, 5 & m, false));
    pool.push_back(c.bin(BVRIGHTSHIFT, inW, 1, true));
    pool.push_back(c.bin(BVRIGHTSHIFT, inW, inW, true)); // >= width
    pool.push_back(c.bin(BVLEFTSHIFT, inW, 1, true));
    pool.push_back(c.bin(BVSRSHIFT, inW, 1, true));
    pool.push_back(c.bin(BVAND, inW, 3 & m, true)); // low mask
    pool.push_back(c.bin(BVAND, inW, 5 & m, true)); // not a low mask
    pool.push_back(c.bin(BVOR, inW, 5 & m, true));
    pool.push_back(c.bin(BVXOR, inW, 3 & m, true));
    pool.push_back(c.bin(SBVREM, inW, 3 & m, true));
    pool.push_back(c.same(BVMULT, inW));
    pool.push_back(c.unary(BVUMINUS, inW));
    pool.push_back(c.unary(BVNOT, inW));
    pool.push_back(c.extend(BVZX, inW, inW + 2));
    pool.push_back(c.extend(BVSX, inW, inW + 2));
    if (inW >= 3)
    {
      pool.push_back(c.extract(inW, inW - 2, 1));
      pool.push_back(c.extract(inW, inW - 1, 0));
    }
    pool.push_back(c.concat(inW, 2, 2, true));
    pool.push_back(c.concat(inW, 2, 2, false));
    return pool;
  };

  const std::vector<uint64_t> ks = {0, 1, 2, 5, 8, 20, 40, 100};

  const std::vector<GroundStep> firstPool = poolFor(w);
  for (const GroundStep& s1 : firstPool)
  {
    const std::vector<GroundStep> secondPool = poolFor(s1.outWidth);
    for (const GroundStep& s2 : secondPool)
      checkChain(c, {s1, s2}, w, &ks);
  }

  if (g_samplesBoth > 0)
    std::cout << "[ samples rep ] collapsed " << g_samplesHit << " of "
              << g_samplesBoth
              << " genuinely collapsible predicate probes ("
              << (100 * g_samplesHit / g_samplesBoth) << "%)" << std::endl;
}

TEST(AchievableImage_Exhaustive, unhandled_kind_rejected)
{
  Ctx c;
  AchievableImage img(c.mgr, 3);
  EXPECT_FALSE(AchievableImage::handledKind(ITE));
  EXPECT_FALSE(AchievableImage::handledKind(READ));
  GroundStep s = c.bin(BVNAND, 3, 1, true);
  EXPECT_FALSE(img.apply(s));
  EXPECT_FALSE(AchievableImage::predicateKind(AND));
  EXPECT_TRUE(AchievableImage::predicateKind(EQ));
  EXPECT_TRUE(AchievableImage::predicateKind(BVSGE));
}

TEST(AchievableImage_Exhaustive, square_small_domain_is_complete)
{
  // x*x at width 3: the domain (8 values) fits the sample budget, so
  // the enumeration makes the samples the COMPLETE image {0,1,4} and
  // every EQ probe decides exactly.
  Ctx c;
  AchievableImage img(c.mgr, 3);
  ASSERT_TRUE(img.apply(c.same(BVMULT, 3)));
  EXPECT_FALSE(img.isExact());
  for (uint64_t k = 0; k < 8; k++)
  {
    const bool member = (k == 0 || k == 1 || k == 4);
    AchievableImage::Decision d = img.decide(EQ, true, c.konst(k, 3));
    EXPECT_EQ(d.collapse, member) << "k=" << k;
  }
}

TEST(AchievableImage_Exhaustive, hint_backprop_through_extract_add)
{
  // (= 65515 (extract[15:0] (bvadd 0xFFFFFF75 (zx x)))) with x 8-bit:
  // satisfied only by x = 118, which no heuristic seed reaches. The
  // back-propagated hint chain recovers it exactly:
  // 65515 -> widen -> subtract the addend -> truncate = 118.
  Ctx c;
  const std::vector<GroundStep> steps = {
      c.extend(BVZX, 8, 32),
      c.bin(BVPLUS, 32, 0xFFFFFF75ull, true),
      c.extract(32, 15, 0),
  };
  AchievableImage img(c.mgr, 8);
  img.addHintChain(steps, c.konst(65515, 16));
  for (const GroundStep& s : steps)
    ASSERT_TRUE(img.apply(s));
  ASSERT_FALSE(img.isExact()); // the wrapping add degrades the interval

  AchievableImage::Decision d = img.decide(EQ, true, c.konst(65515, 16));
  ASSERT_TRUE(d.collapse);
  EXPECT_EQ(evalChain64(steps, d.witnessTrue.GetUnsignedConst()), 65515u);
  EXPECT_NE(evalChain64(steps, d.witnessFalse.GetUnsignedConst()), 65515u);
}

TEST(AchievableImage_Exhaustive, hint_backprop_through_shifted_window)
{
  // The testcase15 family: (bvugt (bvadd B ((extract[26:0] x) << 5)) K)
  // where K - B = 160. The image is B + multiples of 32; values above K
  // exist (x = 6 gives B + 192) but the heuristic seeds skip the small
  // witnesses. The hint chain maps K back to 5, and the +-1 neighbours
  // provide the winning 6.
  Ctx c;
  const uint64_t B = 3203227404ull, K = 3203227564ull;
  const std::vector<GroundStep> steps = {
      c.extract(32, 26, 0),
      c.concat(27, 0, 5, true), // x ++ 0:5
      c.bin(BVPLUS, 32, B, true),
  };
  AchievableImage img(c.mgr, 32);
  img.addHintChain(steps, c.konst(K, 32));
  for (const GroundStep& s : steps)
    ASSERT_TRUE(img.apply(s));

  AchievableImage::Decision d = img.decide(BVGT, true, c.konst(K, 32));
  ASSERT_TRUE(d.collapse);
  EXPECT_GT(evalChain64(steps, d.witnessTrue.GetUnsignedConst()), K);
  EXPECT_LE(evalChain64(steps, d.witnessFalse.GetUnsignedConst()), K);
}

TEST(AchievableImage_Exhaustive, wide_chain_width128)
{
  // ((x mod 100) + 7) >u 50 at width 128: stays exact, collapses, and
  // the witnesses check out under the arbitrary-precision evaluator.
  Ctx c;
  const unsigned w = 128;
  AchievableImage img(c.mgr, w);
  ASSERT_TRUE(img.apply(c.bin(BVMOD, w, 100, true)));
  ASSERT_TRUE(img.apply(c.bin(BVPLUS, w, 7, true)));
  ASSERT_TRUE(img.isExact());

  AchievableImage::Decision d = img.decide(BVGT, true, c.konst(50, w));
  ASSERT_TRUE(d.collapse);

  NodeFactory* hf = c.mgr.hashingNodeFactory;
  auto chainOn = [&](const ASTNode& x) {
    ASTNode t = hf->CreateTerm(BVMOD, w, x, c.konst(100, w));
    t = hf->CreateTerm(BVPLUS, w, t, c.konst(7, w));
    return NonMemberBVConstEvaluator(
        &c.mgr, hf->CreateNode(BVGT, t, c.konst(50, w)));
  };
  EXPECT_EQ(chainOn(d.witnessTrue), c.mgr.ASTTrue);
  EXPECT_EQ(chainOn(d.witnessFalse), c.mgr.ASTFalse);
}

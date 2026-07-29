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

// Exhaustively checks the UnsignedIntervalSet domain at low bitwidths, on two
// fronts:
//
//   Soundness  -- for every combination of input interval-sets, every concrete
//                 result the operation can produce is a member of the computed
//                 set. STP's constant evaluator supplies the reference
//                 semantics, so the checks can't drift from the solver.
//
//   Refinement -- driven with the same single-interval inputs, the set domain
//                 is never worse than the existing single-interval domain: its
//                 hull lies within the single interval, and for the exact kinds
//                 the two hulls agree.
//
// Multi-piece inputs (genuinely disjoint sets) are covered separately, as is
// the set-native ITE union.

#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedIntervalSetAnalysis.h"
#include "stp/Simplifier/UnsignedIntervalSet.h"
#include <gtest/gtest.h>
#include <set>
#include <vector>

namespace
{

struct Boot
{
  Boot() { CONSTANTBV::BitVector_Boot(); }
};

struct Context
{
  Boot boot;
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  stp::UnsignedIntervalAnalysis single;
  stp::UnsignedIntervalSetAnalysis setA;

  Context(unsigned cap)
      : snf(*(mgr.hashingNodeFactory), mgr), single(mgr), setA(mgr, cap)
  {
    mgr.defaultNodeFactory = &snf;
  }
};

stp::CBV makeCBV(unsigned width, uint64_t value)
{
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width && i < 64; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(r, i);
  return r;
}

uint64_t cbvValue(const stp::CBV c, unsigned width)
{
  return *c & (width >= 64 ? ~0ull : ((1ull << width) - 1));
}

stp::UnsignedInterval* makeInterval_(unsigned width, uint64_t lo, uint64_t hi)
{
  return new stp::UnsignedInterval(makeCBV(width, lo), makeCBV(width, hi));
}

uint64_t constantValue(const stp::ASTNode& n)
{
  if (n.GetKind() == stp::TRUE)
    return 1;
  if (n.GetKind() == stp::FALSE)
    return 0;
  return cbvValue(n.GetBVConst(), n.GetValueWidth());
}

stp::UnsignedIntervalSet* makeSet(unsigned width, unsigned cap,
                                  const std::set<uint64_t>& values)
{
  stp::UnsignedIntervalSet* s = new stp::UnsignedIntervalSet(width, cap);
  for (uint64_t v : values)
  {
    stp::CBV c = makeCBV(width, v);
    s->addInterval(c, c);
    CONSTANTBV::BitVector_Destroy(c);
  }
  return s;
}

stp::UnsignedIntervalSet* makeIntervalSet(unsigned width, unsigned cap,
                                          uint64_t lo, uint64_t hi)
{
  stp::UnsignedIntervalSet* s = new stp::UnsignedIntervalSet(width, cap);
  stp::CBV a = makeCBV(width, lo);
  stp::CBV b = makeCBV(width, hi);
  s->addInterval(a, b);
  CONSTANTBV::BitVector_Destroy(a);
  CONSTANTBV::BitVector_Destroy(b);
  return s;
}

bool setContains(const stp::UnsignedIntervalSet& s, unsigned width, uint64_t v)
{
  stp::CBV c = makeCBV(width, v);
  bool r = s.in(c);
  CONSTANTBV::BitVector_Destroy(c);
  return r;
}

// ---- Single-interval-input soundness + refinement vs the single domain ----

// isPredicate => 1-bit result. w0==w1==wOut for the arithmetic kinds here.
void checkBinary(stp::Kind k, unsigned width, bool isPredicate, bool exact,
                 unsigned cap)
{
  Context c(cap);
  const uint64_t N = 1ull << width;
  const unsigned resultWidth = isPredicate ? 1 : width;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, width));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, width));
  const stp::ASTNode n =
      isPredicate ? c.mgr.hashingNodeFactory->CreateNode(k, symbols)
                  : c.mgr.hashingNodeFactory->CreateTerm(k, width, symbols);

  std::vector<uint64_t> table(N * N);
  for (uint64_t a = 0; a < N; a++)
    for (uint64_t b = 0; b < N; b++)
    {
      stp::ASTVec consts;
      consts.push_back(c.mgr.CreateBVConst(width, a));
      consts.push_back(c.mgr.CreateBVConst(width, b));
      const stp::ASTNode op =
          isPredicate ? c.mgr.hashingNodeFactory->CreateNode(k, consts)
                      : c.mgr.hashingNodeFactory->CreateTerm(k, width, consts);
      table[a * N + b] = constantValue(stp::NonMemberBVConstEvaluator(&c.mgr, op));
    }

  for (uint64_t lo0 = 0; lo0 < N; lo0++)
    for (uint64_t hi0 = lo0; hi0 < N; hi0++)
      for (uint64_t lo1 = 0; lo1 < N; lo1++)
        for (uint64_t hi1 = lo1; hi1 < N; hi1++)
        {
          std::set<uint64_t> reach;
          uint64_t bmin = UINT64_MAX, bmax = 0;
          for (uint64_t a = lo0; a <= hi0; a++)
            for (uint64_t b = lo1; b <= hi1; b++)
            {
              const uint64_t v = table[a * N + b];
              reach.insert(v);
              bmin = std::min(bmin, v);
              bmax = std::max(bmax, v);
            }

          stp::UnsignedIntervalSet* s0 = makeIntervalSet(width, cap, lo0, hi0);
          stp::UnsignedIntervalSet* s1 = makeIntervalSet(width, cap, lo1, hi1);
          std::vector<const stp::UnsignedIntervalSet*> ch = {s0, s1};
          stp::UnsignedIntervalSet* out = c.setA.transfer(n, ch);

          // Soundness.
          for (uint64_t v : reach)
            ASSERT_TRUE(setContains(*out, resultWidth, v))
                << "kind " << k << " UNSOUND: missing " << v << " for x in ["
                << lo0 << "," << hi0 << "] y in [" << lo1 << "," << hi1 << "]";
          out->checkInvariant();

          // Refinement vs the single-interval domain.
          std::vector<const stp::UnsignedInterval*> sch = {
              makeInterval_(width, lo0, hi0), makeInterval_(width, lo1, hi1)};
          stp::UnsignedInterval* singleR =
              c.single.dispatchToTransferFunctions(n, sch);
          stp::UnsignedInterval* hull = out->hull();

          if (singleR != nullptr && hull != nullptr)
          {
            const uint64_t sMin = cbvValue(singleR->minV, resultWidth);
            const uint64_t sMax = cbvValue(singleR->maxV, resultWidth);
            const uint64_t hMin = cbvValue(hull->minV, resultWidth);
            const uint64_t hMax = cbvValue(hull->maxV, resultWidth);
            EXPECT_GE(hMin, sMin) << "kind " << k << ": set hull looser than single";
            EXPECT_LE(hMax, sMax) << "kind " << k << ": set hull looser than single";
            if (exact)
            {
              EXPECT_EQ(hMin, bmin);
              EXPECT_EQ(hMax, bmax);
            }
          }

          delete sch[0];
          delete sch[1];
          delete singleR;
          delete hull;
          delete out;
          delete s0;
          delete s1;
        }
}

const bool EXACT = true;
const bool APPROX = false;
const bool PRED = true;
const bool TERM = false;

TEST(UnsignedIntervalSetExhaustive, arithmeticSound)
{
  const unsigned W = 4, CAP = 4;
  checkBinary(stp::BVPLUS, W, TERM, EXACT, CAP);
  checkBinary(stp::BVAND, W, TERM, EXACT, CAP);
  checkBinary(stp::BVOR, W, TERM, EXACT, CAP);
  checkBinary(stp::BVXOR, W, TERM, EXACT, CAP);
  checkBinary(stp::BVDIV, W, TERM, EXACT, CAP);
  checkBinary(stp::BVMULT, W, TERM, APPROX, CAP);
  checkBinary(stp::BVMOD, W, TERM, APPROX, CAP);
  checkBinary(stp::BVLEFTSHIFT, W, TERM, APPROX, CAP);
  checkBinary(stp::BVRIGHTSHIFT, W, TERM, APPROX, CAP);
}

TEST(UnsignedIntervalSetExhaustive, signedArithmeticSound)
{
  const unsigned W = 4, CAP = 4;
  checkBinary(stp::SBVDIV, W, TERM, APPROX, CAP);
  checkBinary(stp::SBVREM, W, TERM, APPROX, CAP);
  checkBinary(stp::SBVMOD, W, TERM, APPROX, CAP);
  checkBinary(stp::BVSRSHIFT, W, TERM, APPROX, CAP);
}

TEST(UnsignedIntervalSetExhaustive, predicatesSound)
{
  const unsigned W = 4, CAP = 4;
  checkBinary(stp::EQ, W, PRED, APPROX, CAP);
  checkBinary(stp::BVGT, W, PRED, APPROX, CAP);
  checkBinary(stp::BVSGT, W, PRED, APPROX, CAP);
}

// Genuinely disjoint multi-piece inputs: iterate over every subset of a small
// width and confirm soundness against the exact reachable set.
TEST(UnsignedIntervalSetExhaustive, multiPieceSound)
{
  const unsigned W = 3, CAP = 8; // cap high enough to keep all pieces
  const uint64_t N = 1ull << W;
  Context c(CAP);

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, W));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, W));

  const stp::Kind kinds[] = {stp::BVPLUS, stp::BVDIV,  stp::SBVDIV,
                             stp::SBVREM, stp::BVMULT, stp::BVXOR};

  for (stp::Kind k : kinds)
  {
    const stp::ASTNode n = c.mgr.hashingNodeFactory->CreateTerm(k, W, symbols);

    std::vector<uint64_t> table(N * N);
    for (uint64_t a = 0; a < N; a++)
      for (uint64_t b = 0; b < N; b++)
      {
        stp::ASTVec consts;
        consts.push_back(c.mgr.CreateBVConst(W, a));
        consts.push_back(c.mgr.CreateBVConst(W, b));
        const stp::ASTNode op = c.mgr.hashingNodeFactory->CreateTerm(k, W, consts);
        table[a * N + b] = constantValue(stp::NonMemberBVConstEvaluator(&c.mgr, op));
      }

    for (uint64_t m0 = 1; m0 < (1ull << N); m0++)
      for (uint64_t m1 = 1; m1 < (1ull << N); m1++)
      {
        std::set<uint64_t> vals0, vals1;
        for (uint64_t v = 0; v < N; v++)
        {
          if (m0 & (1ull << v))
            vals0.insert(v);
          if (m1 & (1ull << v))
            vals1.insert(v);
        }

        stp::UnsignedIntervalSet* s0 = makeSet(W, CAP, vals0);
        stp::UnsignedIntervalSet* s1 = makeSet(W, CAP, vals1);
        std::vector<const stp::UnsignedIntervalSet*> ch = {s0, s1};
        stp::UnsignedIntervalSet* out = c.setA.transfer(n, ch);

        for (uint64_t a : vals0)
          for (uint64_t b : vals1)
          {
            const uint64_t v = table[a * N + b];
            ASSERT_TRUE(setContains(*out, W, v))
                << "kind " << k << " UNSOUND multipiece: missing " << v;
          }
        out->checkInvariant();

        delete out;
        delete s0;
        delete s1;
      }
  }
}

// ITE is the union of its branches; a disjoint then/else must stay disjoint.
TEST(UnsignedIntervalSetExhaustive, iteUnion)
{
  const unsigned W = 4, CAP = 4;
  Context c(CAP);

  stp::ASTNode cond = c.mgr.CreateSymbol("c", 0, 0);
  stp::ASTNode x = c.mgr.CreateSymbol("x", 0, W);
  stp::ASTNode y = c.mgr.CreateSymbol("y", 0, W);
  stp::ASTVec iteKids = {cond, x, y};
  const stp::ASTNode n = c.mgr.hashingNodeFactory->CreateTerm(stp::ITE, W, iteKids);

  // Unknown condition: result must contain both branches' values.
  stp::UnsignedIntervalSet* condS = new stp::UnsignedIntervalSet(1, CAP);
  condS->resetToComplete();
  stp::UnsignedIntervalSet* thenS = makeIntervalSet(W, CAP, 1, 2);
  stp::UnsignedIntervalSet* elseS = makeIntervalSet(W, CAP, 10, 11);
  std::vector<const stp::UnsignedIntervalSet*> ch = {condS, thenS, elseS};
  stp::UnsignedIntervalSet* out = c.setA.transfer(n, ch);

  for (uint64_t v : {1u, 2u, 10u, 11u})
    EXPECT_TRUE(setContains(*out, W, v));
  for (uint64_t v : {0u, 5u, 12u})
    EXPECT_FALSE(setContains(*out, W, v)); // the gap survives (cap allows it)
  out->checkInvariant();

  delete out;
  delete condS;
  delete thenS;
  delete elseS;
}

} // namespace

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

// Exhaustively checks that the interval transfer functions in
// UnsignedIntervalAnalysis are sound at low bitwidths. For every interval
// (or pair of intervals) of each width, the interval computed for the node
// must contain the operation's result for every concrete value the children
// can take. STP's constant evaluator provides the reference semantics, so
// the tests can't drift from the solver's.
//
// A null result claims nothing, so it is always sound; these tests don't
// check precision.

#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include <gtest/gtest.h>
#include <vector>

namespace
{

// BitVector_Boot must run before anything allocates constant bitvectors.
struct Boot
{
  Boot() { CONSTANTBV::BitVector_Boot(); }
};

struct Context
{
  Boot boot;
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  stp::UnsignedIntervalAnalysis analysis;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), analysis(mgr)
  {
    mgr.defaultNodeFactory = &snf;
  }
};

stp::CBV makeCBV(unsigned width, uint64_t value)
{
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(r, i);
  return r;
}

stp::UnsignedInterval* makeInterval(unsigned width, uint64_t min, uint64_t max)
{
  return new stp::UnsignedInterval(makeCBV(width, min), makeCBV(width, max));
}

// The widths used here always fit into the first word of the bitvector.
uint64_t cbvValue(const stp::CBV c, unsigned width)
{
  return *c & ((1ull << width) - 1);
}

uint64_t constantValue(const stp::ASTNode& n)
{
  if (n.GetKind() == stp::TRUE)
    return 1;
  if (n.GetKind() == stp::FALSE)
    return 0;
  return cbvValue(n.GetBVConst(), n.GetValueWidth());
}

void cleanup(std::vector<const stp::UnsignedInterval*>& children,
             stp::UnsignedInterval* result)
{
  for (const auto* c : children)
    delete c;
  delete result;
}

// Checks that every value in [rmin, rmax] claimed for the node covers the
// reference result. Reports and returns false on the first violation.
bool covered(stp::Kind k, unsigned width, const stp::UnsignedInterval* result,
             unsigned resultWidth, uint64_t reference, uint64_t a, uint64_t b)
{
  const uint64_t rmin = cbvValue(result->minV, resultWidth);
  const uint64_t rmax = cbvValue(result->maxV, resultWidth);

  if (reference < rmin || reference > rmax)
  {
    ADD_FAILURE() << "kind " << k << " at width " << width << ": operands ("
                  << a << ", " << b << ") give " << reference
                  << ", outside the computed interval [" << rmin << ", "
                  << rmax << "]";
    return false;
  }
  return true;
}

// Exhaustively checks a two-child operation: child widths w0 and w1, result
// width wOut. Propositions (BVGT and friends) have a one-bit result.
void checkBinary(stp::Kind k, unsigned w0, unsigned w1, unsigned wOut,
                 bool isPredicate)
{
  Context c;
  const uint64_t N0 = 1ull << w0;
  const uint64_t N1 = 1ull << w1;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, w0));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, w1));
  const stp::ASTNode n =
      isPredicate ? c.mgr.hashingNodeFactory->CreateNode(k, symbols)
                  : c.mgr.hashingNodeFactory->CreateTerm(k, wOut, symbols);

  // Reference results from the solver's constant evaluator.
  std::vector<uint64_t> table(N0 * N1);
  for (uint64_t a = 0; a < N0; a++)
    for (uint64_t b = 0; b < N1; b++)
    {
      stp::ASTVec consts;
      consts.push_back(c.mgr.CreateBVConst(w0, a));
      consts.push_back(c.mgr.CreateBVConst(w1, b));
      const stp::ASTNode op =
          isPredicate ? c.mgr.hashingNodeFactory->CreateNode(k, consts)
                      : c.mgr.hashingNodeFactory->CreateTerm(k, wOut, consts);
      table[a * N1 + b] = constantValue(NonMemberBVConstEvaluator(&c.mgr, op));
    }

  const unsigned resultWidth = isPredicate ? 1 : wOut;

  for (uint64_t lo0 = 0; lo0 < N0; lo0++)
    for (uint64_t hi0 = lo0; hi0 < N0; hi0++)
      for (uint64_t lo1 = 0; lo1 < N1; lo1++)
        for (uint64_t hi1 = lo1; hi1 < N1; hi1++)
        {
          std::vector<const stp::UnsignedInterval*> children = {
              makeInterval(w0, lo0, hi0), makeInterval(w1, lo1, hi1)};
          stp::UnsignedInterval* result =
              c.analysis.dispatchToTransferFunctions(n, children);

          if (result != nullptr)
            for (uint64_t a = lo0; a <= hi0; a++)
              for (uint64_t b = lo1; b <= hi1; b++)
                if (!covered(k, w0, result, resultWidth, table[a * N1 + b], a,
                             b))
                {
                  cleanup(children, result);
                  return;
                }

          cleanup(children, result);
        }
}

void checkBinary(stp::Kind k, unsigned width)
{
  checkBinary(k, width, width, width, false);
}

void checkPredicate(stp::Kind k, unsigned width)
{
  checkBinary(k, width, width, 1, true);
}

void checkUnary(stp::Kind k, unsigned width)
{
  Context c;
  const uint64_t N = 1ull << width;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, width));
  const stp::ASTNode n =
      c.mgr.hashingNodeFactory->CreateTerm(k, width, symbols);

  std::vector<uint64_t> table(N);
  for (uint64_t a = 0; a < N; a++)
  {
    stp::ASTVec consts;
    consts.push_back(c.mgr.CreateBVConst(width, a));
    const stp::ASTNode op =
        c.mgr.hashingNodeFactory->CreateTerm(k, width, consts);
    table[a] = constantValue(NonMemberBVConstEvaluator(&c.mgr, op));
  }

  for (uint64_t lo = 0; lo < N; lo++)
    for (uint64_t hi = lo; hi < N; hi++)
    {
      std::vector<const stp::UnsignedInterval*> children = {
          makeInterval(width, lo, hi)};
      stp::UnsignedInterval* result =
          c.analysis.dispatchToTransferFunctions(n, children);

      if (result != nullptr)
        for (uint64_t a = lo; a <= hi; a++)
          if (!covered(k, width, result, width, table[a], a, 0))
          {
            cleanup(children, result);
            return;
          }

      cleanup(children, result);
    }
}

TEST(UnsignedIntervalExhaustive, Udiv)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVDIV, w);
}

TEST(UnsignedIntervalExhaustive, Urem)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVMOD, w);
}

TEST(UnsignedIntervalExhaustive, SignedDivRemMod)
{
  // Not implemented yet (always null), but keeps them covered if they are.
  for (unsigned w = 1; w <= 4; w++)
  {
    checkBinary(stp::SBVDIV, w);
    checkBinary(stp::SBVREM, w);
    checkBinary(stp::SBVMOD, w);
  }
}

TEST(UnsignedIntervalExhaustive, Plus)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVPLUS, w);
}

TEST(UnsignedIntervalExhaustive, Mult)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVMULT, w);
}

TEST(UnsignedIntervalExhaustive, Bvand)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVAND, w);
}

TEST(UnsignedIntervalExhaustive, Bvor)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVOR, w);
}

TEST(UnsignedIntervalExhaustive, Bvxor)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVXOR, w);
}

TEST(UnsignedIntervalExhaustive, RightShift)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVRIGHTSHIFT, w);
}

TEST(UnsignedIntervalExhaustive, LeftShift)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVLEFTSHIFT, w);
}

TEST(UnsignedIntervalExhaustive, SignedRightShift)
{
  for (unsigned w = 1; w <= 4; w++)
    checkBinary(stp::BVSRSHIFT, w);
}

TEST(UnsignedIntervalExhaustive, Concat)
{
  for (unsigned w0 = 1; w0 <= 3; w0++)
    for (unsigned w1 = 1; w1 <= 3; w1++)
      checkBinary(stp::BVCONCAT, w0, w1, w0 + w1, false);
}

TEST(UnsignedIntervalExhaustive, Bvgt)
{
  for (unsigned w = 1; w <= 4; w++)
    checkPredicate(stp::BVGT, w);
}

TEST(UnsignedIntervalExhaustive, Bvsgt)
{
  for (unsigned w = 1; w <= 4; w++)
    checkPredicate(stp::BVSGT, w);
}

TEST(UnsignedIntervalExhaustive, Eq)
{
  for (unsigned w = 1; w <= 4; w++)
    checkPredicate(stp::EQ, w);
}

TEST(UnsignedIntervalExhaustive, Bvnot)
{
  for (unsigned w = 1; w <= 5; w++)
    checkUnary(stp::BVNOT, w);
}

TEST(UnsignedIntervalExhaustive, Bvuminus)
{
  for (unsigned w = 1; w <= 5; w++)
    checkUnary(stp::BVUMINUS, w);
}

TEST(UnsignedIntervalExhaustive, Bvsx)
{
  for (unsigned wIn = 1; wIn <= 3; wIn++)
    for (unsigned wOut = wIn + 1; wOut <= 5; wOut++)
    {
      Context c;
      const uint64_t N = 1ull << wIn;

      stp::ASTVec symbols;
      symbols.push_back(c.mgr.CreateSymbol("x", 0, wIn));
      symbols.push_back(c.mgr.CreateBVConst(32, wOut));
      const stp::ASTNode n =
          c.mgr.hashingNodeFactory->CreateTerm(stp::BVSX, wOut, symbols);

      std::vector<uint64_t> table(N);
      for (uint64_t a = 0; a < N; a++)
      {
        stp::ASTVec consts;
        consts.push_back(c.mgr.CreateBVConst(wIn, a));
        consts.push_back(c.mgr.CreateBVConst(32, wOut));
        const stp::ASTNode op =
            c.mgr.hashingNodeFactory->CreateTerm(stp::BVSX, wOut, consts);
        table[a] = constantValue(NonMemberBVConstEvaluator(&c.mgr, op));
      }

      for (uint64_t lo = 0; lo < N; lo++)
        for (uint64_t hi = lo; hi < N; hi++)
        {
          std::vector<const stp::UnsignedInterval*> children = {
              makeInterval(wIn, lo, hi), nullptr};
          stp::UnsignedInterval* result =
              c.analysis.dispatchToTransferFunctions(n, children);

          if (result != nullptr)
            for (uint64_t a = lo; a <= hi; a++)
              if (!covered(stp::BVSX, wIn, result, wOut, table[a], a, wOut))
              {
                cleanup(children, result);
                return;
              }

          cleanup(children, result);
        }
    }
}

TEST(UnsignedIntervalExhaustive, Extract)
{
  for (unsigned w = 1; w <= 4; w++)
    for (unsigned lo = 0; lo < w; lo++)
      for (unsigned hi = lo; hi < w; hi++)
      {
        Context c;
        const uint64_t N = 1ull << w;
        const unsigned wOut = hi - lo + 1;

        stp::ASTVec symbols;
        symbols.push_back(c.mgr.CreateSymbol("x", 0, w));
        symbols.push_back(c.mgr.CreateBVConst(32, hi));
        symbols.push_back(c.mgr.CreateBVConst(32, lo));
        const stp::ASTNode n =
            c.mgr.hashingNodeFactory->CreateTerm(stp::BVEXTRACT, wOut,
                                                 symbols);

        std::vector<uint64_t> table(N);
        for (uint64_t a = 0; a < N; a++)
        {
          stp::ASTVec consts;
          consts.push_back(c.mgr.CreateBVConst(w, a));
          consts.push_back(c.mgr.CreateBVConst(32, hi));
          consts.push_back(c.mgr.CreateBVConst(32, lo));
          const stp::ASTNode op = c.mgr.hashingNodeFactory->CreateTerm(
              stp::BVEXTRACT, wOut, consts);
          table[a] = constantValue(NonMemberBVConstEvaluator(&c.mgr, op));
        }

        for (uint64_t lo0 = 0; lo0 < N; lo0++)
          for (uint64_t hi0 = lo0; hi0 < N; hi0++)
          {
            std::vector<const stp::UnsignedInterval*> children = {
                makeInterval(w, lo0, hi0), makeInterval(32, hi, hi),
                makeInterval(32, lo, lo)};
            stp::UnsignedInterval* result =
                c.analysis.dispatchToTransferFunctions(n, children);

            if (result != nullptr)
              for (uint64_t a = lo0; a <= hi0; a++)
                if (!covered(stp::BVEXTRACT, w, result, wOut, table[a], a,
                             lo))
                {
                  cleanup(children, result);
                  return;
                }

            cleanup(children, result);
          }
      }
}

TEST(UnsignedIntervalExhaustive, Ite)
{
  for (unsigned w = 1; w <= 4; w++)
  {
    Context c;
    const uint64_t N = 1ull << w;

    stp::ASTVec symbols;
    symbols.push_back(c.mgr.CreateSymbol("c", 0, 0));
    symbols.push_back(c.mgr.CreateSymbol("x", 0, w));
    symbols.push_back(c.mgr.CreateSymbol("y", 0, w));
    const stp::ASTNode n =
        c.mgr.hashingNodeFactory->CreateTerm(stp::ITE, w, symbols);

    // Condition alternatives: unknown, false, true; with the concrete
    // condition values each allows.
    const std::vector<std::vector<uint64_t>> condValues = {{0, 1}, {0}, {1}};

    for (unsigned condChoice = 0; condChoice < 3; condChoice++)
      for (uint64_t lo1 = 0; lo1 < N; lo1++)
        for (uint64_t hi1 = lo1; hi1 < N; hi1++)
          for (uint64_t lo2 = 0; lo2 < N; lo2++)
            for (uint64_t hi2 = lo2; hi2 < N; hi2++)
            {
              const stp::UnsignedInterval* cond = nullptr;
              if (condChoice == 1)
                cond = makeInterval(1, 0, 0);
              else if (condChoice == 2)
                cond = makeInterval(1, 1, 1);

              std::vector<const stp::UnsignedInterval*> children = {
                  cond, makeInterval(w, lo1, hi1), makeInterval(w, lo2, hi2)};
              stp::UnsignedInterval* result =
                  c.analysis.dispatchToTransferFunctions(n, children);

              if (result != nullptr)
                for (const uint64_t condV : condValues[condChoice])
                  for (uint64_t a = lo1; a <= hi1; a++)
                    for (uint64_t b = lo2; b <= hi2; b++)
                    {
                      const uint64_t v = condV ? a : b;
                      if (!covered(stp::ITE, w, result, w, v, a, b))
                      {
                        cleanup(children, result);
                        return;
                      }
                    }

              cleanup(children, result);
            }
  }
}

TEST(UnsignedIntervalExhaustive, BooleanOps)
{
  Context c;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("a", 0, 0));
  symbols.push_back(c.mgr.CreateSymbol("b", 0, 0));

  struct Op
  {
    stp::Kind kind;
    uint64_t (*eval)(uint64_t, uint64_t);
  };
  const std::vector<Op> ops = {
      {stp::AND, [](uint64_t a, uint64_t b) { return a & b; }},
      {stp::OR, [](uint64_t a, uint64_t b) { return a | b; }},
      {stp::XOR, [](uint64_t a, uint64_t b) { return a ^ b; }},
  };

  // Boolean alternatives: unknown, false, true; with the concrete values
  // each allows.
  const std::vector<std::vector<uint64_t>> boolValues = {{0, 1}, {0}, {1}};

  for (const auto& op : ops)
  {
    const stp::ASTNode n =
        c.mgr.hashingNodeFactory->CreateNode(op.kind, symbols);

    for (unsigned choice0 = 0; choice0 < 3; choice0++)
      for (unsigned choice1 = 0; choice1 < 3; choice1++)
      {
        const stp::UnsignedInterval* i0 =
            choice0 == 0 ? nullptr : makeInterval(1, choice0 - 1, choice0 - 1);
        const stp::UnsignedInterval* i1 =
            choice1 == 0 ? nullptr : makeInterval(1, choice1 - 1, choice1 - 1);

        std::vector<const stp::UnsignedInterval*> children = {i0, i1};
        stp::UnsignedInterval* result =
            c.analysis.dispatchToTransferFunctions(n, children);

        if (result != nullptr)
          for (const uint64_t a : boolValues[choice0])
            for (const uint64_t b : boolValues[choice1])
              if (!covered(op.kind, 1, result, 1, op.eval(a, b), a, b))
              {
                cleanup(children, result);
                return;
              }

        cleanup(children, result);
      }
  }

  // Boolean NOT.
  {
    stp::ASTVec child;
    child.push_back(symbols[0]);
    const stp::ASTNode n =
        c.mgr.hashingNodeFactory->CreateNode(stp::NOT, child);

    for (unsigned choice = 0; choice < 3; choice++)
    {
      const stp::UnsignedInterval* i0 =
          choice == 0 ? nullptr : makeInterval(1, choice - 1, choice - 1);

      std::vector<const stp::UnsignedInterval*> children = {i0};
      stp::UnsignedInterval* result =
          c.analysis.dispatchToTransferFunctions(n, children);

      if (result != nullptr)
        for (const uint64_t a : boolValues[choice])
          if (!covered(stp::NOT, 1, result, 1, a ^ 1, a, 0))
          {
            cleanup(children, result);
            return;
          }

      cleanup(children, result);
    }
  }
}

} // namespace

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

// Exact low-prefix refinement is deliberately tiny, but it is permanent
// CNF: test both its value-level predicate and the clauses independently and
// exhaustively. Four bits exercise all three encoded result bits while still
// leaving an unencoded high bit that must remain free.
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <memory>
#include <vector>

using namespace stp;

namespace
{

const unsigned WIDTH = 4;
const unsigned PREFIX = 3;
const unsigned VALUES = 1u << WIDTH;
const unsigned MASK = (1u << PREFIX) - 1;

std::vector<bool> bitsOf(unsigned value, unsigned width = WIDTH)
{
  std::vector<bool> bits(width);
  for (unsigned i = 0; i < width; ++i)
    bits[i] = ((value >> i) & 1u) != 0;
  return bits;
}

unsigned negated(unsigned value, unsigned width = WIDTH)
{
  const unsigned mask = (1u << width) - 1;
  return (-value) & mask;
}

class BVLowPrefixEncodingTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  std::unique_ptr<SATSolver> solver;
  std::vector<unsigned> aVars, bVars, resultVars;

  void build(Kind opKind, bool aNegated = false, bool bNegated = false)
  {
    solver.reset(createSATSolver(mgr.UserFlags));
    ASSERT_TRUE(solver != NULL) << "no SAT backend was compiled in";
    ASSERT_TRUE(solver->supportsAssumptions());

    aVars.resize(WIDTH);
    bVars.resize(WIDTH);
    resultVars.resize(WIDTH);
    for (unsigned i = 0; i < WIDTH; ++i)
    {
      aVars[i] = solver->newVar();
      bVars[i] = solver->newVar();
      resultVars[i] = solver->newVar();
      solver->setFrozen(aVars[i]);
      solver->setFrozen(bVars[i]);
      solver->setFrozen(resultVars[i]);
    }

    if (opKind == BVPLUS)
      encodeAddLowPrefix(*solver, aVars, bVars, resultVars, WIDTH, PREFIX,
                         aNegated, bNegated);
    else
      encodeMulLowPrefix(*solver, aVars, bVars, resultVars, WIDTH, PREFIX);
  }

  bool permits(unsigned a, unsigned b, unsigned result)
  {
    SATSolver::vec_literals assumptions;
    const unsigned values[3] = {a, b, result};
    const std::vector<unsigned>* vars[3] = {&aVars, &bVars, &resultVars};
    for (unsigned v = 0; v < 3; ++v)
      for (unsigned i = 0; i < WIDTH; ++i)
        assumptions.push(
            SATSolver::mkLit((*vars[v])[i], ((values[v] >> i) & 1u) == 0));

    bool timedOut = false;
    const bool sat = solver->solveWithAssumptions(assumptions, timedOut);
    EXPECT_FALSE(timedOut);
    return sat;
  }
};

} // namespace

TEST(BVLowPrefixSchema, value_predicate_is_exact_at_widths_one_through_six)
{
  for (unsigned width = 1; width <= 6; ++width)
  {
    const unsigned values = 1u << width;
    const unsigned prefix = std::min(PREFIX, width);
    for (Kind opKind : {BVPLUS, BVMULT})
      for (unsigned a = 0; a < values; ++a)
        for (unsigned b = 0; b < values; ++b)
        {
          const unsigned result =
              (opKind == BVPLUS) ? (a + b) & (values - 1)
                                 : (a * b) & (values - 1);
          ASSERT_TRUE(exactLowPrefixHolds(opKind, bitsOf(a, width),
                                          bitsOf(b, width),
                                          bitsOf(result, width), prefix))
              << _kind_names[opKind] << " width=" << width << " a=" << a
              << " b=" << b;
        }
  }
}

TEST_F(BVLowPrefixEncodingTest, addition_clauses_define_only_the_low_prefix)
{
  for (unsigned negatedOperand = 0; negatedOperand < 3; ++negatedOperand)
  {
    const bool aNegated = negatedOperand == 1;
    const bool bNegated = negatedOperand == 2;
    build(BVPLUS, aNegated, bNegated);
    for (unsigned a = 0; a < VALUES; ++a)
      for (unsigned b = 0; b < VALUES; ++b)
        for (unsigned result = 0; result < VALUES; ++result)
        {
          const unsigned effectiveA = aNegated ? negated(a) : a;
          const unsigned effectiveB = bNegated ? negated(b) : b;
          const bool want =
              (result & MASK) == ((effectiveA + effectiveB) & MASK);
          ASSERT_EQ(want, permits(a, b, result))
              << "negatedOperand=" << negatedOperand << " a=" << a
              << " b=" << b << " result=" << result;
        }
  }
}

TEST_F(BVLowPrefixEncodingTest,
       multiplication_clauses_define_only_the_low_prefix)
{
  build(BVMULT);
  for (unsigned a = 0; a < VALUES; ++a)
    for (unsigned b = 0; b < VALUES; ++b)
      for (unsigned result = 0; result < VALUES; ++result)
      {
        const bool want = (result & MASK) == ((a * b) & MASK);
        ASSERT_EQ(want, permits(a, b, result))
            << "a=" << a << " b=" << b << " result=" << result;
      }
}

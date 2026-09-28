/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

// Offering the whole active stack to the exact-stack preprocessor on every
// check, from an embedder that pushes and pops per query.
//
// The per-level incremental route encodes each level as it arrives and never
// simplifies across the stack, so what reaches the SAT solver is a formula
// nobody has been over. That is not a small thing: on one floating-point
// query the batch pipeline spends 13ms between the simplifier, constant-bit
// propagation, unconstrained removal, pure literals and strength reduction,
// and then searches for 10.1s, where the per-level route skips all five and
// the same search costs 31.1s.
//
// STP already had the route that supplies it -- the whole stack preprocessed
// into one assumption-scoped block -- but it was reachable only on an
// explicitly forced first engagement and only for a plain bit-vector stack.
// A caller whose queries carry array reads or floating point, which is every
// symbolic-execution embedder, could not get at it at all.
//
// What is pinned here is that the flag reaches its field and that turning it
// on does not change an answer. Whether it makes a given query faster is a
// stopwatch question, and the answer is "sometimes": see the flag's own
// documentation for the measurements.
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
const stp::UserDefinedFlags& flags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

// A push/assert/query/pop session, which is the shape an embedder that
// treats every query as independent produces -- and the shape the per-level
// route serves worst.
int solveScoped(VC vc, int scale)
{
  Type bv = vc_bvType(vc, 32);
  Expr a = vc_varExpr(vc, "a", bv);
  Expr b = vc_varExpr(vc, "b", bv);

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, a, b),
                                 vc_bvConstExprFromInt(vc, 32, scale)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, vc_bvConstExprFromInt(vc, 32, 1)));
  const int r = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);
  return r;
}
} // namespace

TEST(incremental_scoped_preprocessing, ItIsOffByDefault)
{
  VC vc = vc_createValidityChecker();
  EXPECT_FALSE(flags(vc).incremental_scoped_preprocessing);
  vc_Destroy(vc);
}

TEST(incremental_scoped_preprocessing, TheFlagReachesTheField)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, INCREMENTAL_SCOPED_PREPROCESSING, 1);
  EXPECT_TRUE(flags(vc).incremental_scoped_preprocessing);
  vc_setInterfaceFlags(vc, INCREMENTAL_SCOPED_PREPROCESSING, 0);
  EXPECT_FALSE(flags(vc).incremental_scoped_preprocessing);
  vc_Destroy(vc);
}

// Enough checks that the driver engages -- it takes over on the third for a
// caller with no set-logic to declare -- and the same answers either way.
// The route preprocesses into a block and adopts it only when the DAG at
// least halves, so which checks take it is its own business; what must not
// vary is what they answer.
TEST(incremental_scoped_preprocessing, TheAnswersDoNotChange)
{
  const int scales[6] = {3037 * 3041, 15, 1024, 7919 * 3, 65535, 42};

  for (int i = 0; i < 6; ++i)
  {
    VC off = vc_createValidityChecker();
    VC on = vc_createValidityChecker();
    vc_setInterfaceFlags(on, INCREMENTAL_SCOPED_PREPROCESSING, 1);

    // Run the whole sequence on each, so the driver is engaged by the time
    // the interesting checks arrive rather than being asked cold.
    int expected = 0, got = 0;
    for (int j = 0; j <= i; ++j)
    {
      expected = solveScoped(off, scales[j]);
      got = solveScoped(on, scales[j]);
    }
    EXPECT_EQ(expected, got) << "scale=" << scales[i];

    vc_Destroy(off);
    vc_Destroy(on);
  }
}

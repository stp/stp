/***********
AUTHORS: Andrew Teylu

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

// Array equality ('x' flag) over arrays whose index or element sorts
// are floating-point or RoundingMode, built through the C API. The
// equality operands are abstracted out of the formula when the
// equality is built, so every lowering the input formula receives
// (totalising partial operations, canonicalising float indexes,
// pinning RoundingMode reads) must also reach the recorded operands.

#include "stp/c_interface.h"
#include <gtest/gtest.h>

// (Array RoundingMode (_ FloatingPoint 5 11)): two stores at one
// RoundingMode index whose values are always =-equal floats --
// fp.min(f, x) against x where x is f converted to its own format.
// The fp.min inside the abstracted operand used to reach the float
// blaster without its totalised third child and abort the solve.
TEST(fp_array_extensionality, rm_indexed_equal_stores_sat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 5, 11);
  Type arr = vc_arrayType(vc, rm, fp);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr f = vc_varExpr(vc, "f", fp);
  Expr tofp = vc_fpToFPFromFP(vc, 5, 11, r, f);
  Expr mn = vc_fpMinExpr(vc, f, tofp);
  Expr s1 = vc_writeExpr(vc, a, r, mn);
  Expr s2 = vc_writeExpr(vc, s1, r, tofp);

  vc_assertFormula(vc, vc_eqExpr(vc, s1, s2));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// The negation of the same equality is unsatisfiable: a same-format
// conversion is the identity on values, fp.min of a value with itself
// is that value, so the two stores agree at the written index and
// share the base everywhere else.
TEST(fp_array_extensionality, rm_indexed_equal_stores_distinct_unsat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 5, 11);
  Type arr = vc_arrayType(vc, rm, fp);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr f = vc_varExpr(vc, "f", fp);
  Expr tofp = vc_fpToFPFromFP(vc, 5, 11, r, f);
  Expr mn = vc_fpMinExpr(vc, f, tofp);
  Expr s1 = vc_writeExpr(vc, a, r, mn);
  Expr s2 = vc_writeExpr(vc, s1, r, tofp);

  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, s1, s2)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// (Array (_ FloatingPoint 5 11) (_ BitVec 5)): a store chain at float
// indexes -- a -oo literal, a variable pinned to -oo by fp.geq, and
// two fp.rem results that denote NaN -- under a three-way array
// equality that the write-chain solver rewrites without minting a
// record. Simplification substitutes the pinned variable, folding the
// canonical index circuits to plain constants, while the -oo literal
// stays a float-flavoured constant: two constant nodes, one value.
// Every place that concluded "different constant nodes, different
// value" then went wrong together -- the read-over-write rule skipped
// a write it hits, the refinement's axiom shortcut dropped the pair,
// and the loop fell off its end ("reached the end without proper
// conclusion", on every backend).
TEST(fp_array_extensionality, float_indexed_chain_equalities_converge)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type fp = vc_fpType(vc, 5, 11);
  Type bv5 = vc_bvType(vc, 5);
  Type arr = vc_arrayType(vc, fp, bv5);

  Expr x1 = vc_varExpr(vc, "x1", bv5);
  Expr x2 = vc_varExpr(vc, "x2", fp);
  Expr moo = vc_fpMinusInfinity(vc, fp);
  Expr x3 = vc_varExpr(vc, "x3", arr);
  Expr x4 = vc_varExpr(vc, "x4", bv5);
  Expr x10 = vc_varExpr(vc, "x10", arr);
  Expr t14 = vc_readExpr(vc, x3, x2);
  Expr t18 = vc_fpRemExpr(vc, x2, x2);
  Expr t20 = vc_readExpr(vc, x10, x2);
  Expr t27 = vc_readExpr(vc, x10, t18);
  Expr t28 = vc_fpRemExpr(vc, t18, t18);
  Expr t34 = vc_writeExpr(vc, x10, moo, t20);
  Expr t35 = vc_writeExpr(vc, t34, x2, t27);
  Expr t36 = vc_writeExpr(vc, t35, moo, x4);
  Expr t37 = vc_writeExpr(vc, t36, x2, x4);
  Expr t38 = vc_writeExpr(vc, t37, moo, x1);
  Expr t39 = vc_writeExpr(vc, t38, t18, t14);
  Expr t40 = vc_writeExpr(vc, t39, t28, x4);

  vc_assertFormula(vc, vc_eqExpr(vc, t14, x4));
  vc_assertFormula(vc, vc_fpGeqExpr(vc, moo, x2));
  vc_assertFormula(vc, vc_andExpr(vc, vc_eqExpr(vc, t35, t40),
                                  vc_eqExpr(vc, t40, t34)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// (Array (_ FloatingPoint 8 24) (_ BitVec 8)): a guarded equality
// between two stores of one base at one float index, under minisat.
// The store index inside the abstracted operands used to stay raw
// while the formula's reads at the same index were canonicalised, so
// refinement compared two structurally different index terms for one
// index and the loop fell off its end ("reached the end without
// proper conclusion"). The satisfying assignments need r2 != r1 at a
// nonzero index, which minisat's model sequence used to walk into.
TEST(fp_array_extensionality, float_indexed_refinement_converges)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  vc_useMinisat(vc);

  Type fp = vc_fpType(vc, 8, 24);
  Type bv8 = vc_bvType(vc, 8);
  Type arr = vc_arrayType(vc, fp, bv8);

  Expr a0 = vc_varExpr(vc, "a0", arr);
  Expr a1 = vc_varExpr(vc, "a1", arr);
  Expr a2 = vc_varExpr(vc, "a2", arr);
  Expr bits = vc_bvConstExprFromDecStr(vc, 32, "1542123083");
  Expr idx = vc_fpToFPFromIEEEBV(vc, 8, 24, bits);
  Expr r1 = vc_readExpr(vc, a2, idx);
  Expr r2 = vc_readExpr(vc, a1, idx);
  Expr s1 = vc_writeExpr(vc, a0, idx, r1);
  Expr s2 = vc_writeExpr(vc, a0, idx, r2);

  vc_assertFormula(vc, vc_bvLeExpr(vc, r2, r1));
  vc_assertFormula(vc, vc_iffExpr(vc, vc_fpIsZeroExpr(vc, idx),
                                  vc_eqExpr(vc, s2, s1)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// With the 'x' flag the array model comes out of the deterministic
// sorted extraction rather than the pre-extension traversal. Both owe
// the caller entries at the array's declared sorts, so that an entry
// can be fed back -- see fp-model-roundtrip.cpp, which pins the same
// obligation on the traversal path.
TEST(fp_array_extensionality, sorted_model_entries_carry_their_sorts)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type f = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, f, f));
  Expr i = vc_varExpr(vc, "i", f);
  Expr one =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00ULL));

  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), one));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr* indices = NULL;
  Expr* values = NULL;
  int size = 0;
  vc_getCounterExampleArray(vc, a, &indices, &values, &size);
  ASSERT_GE(size, 1);

  // Asserted, not expected: vc_readExpr below refuses an index that is
  // not of the array's index sort, and takes the process down with it.
  for (int x = 0; x < size; x++)
  {
    ASSERT_EQ(FLOATINGPOINT_TYPE, getType(indices[x])) << "entry " << x;
    EXPECT_EQ(5, vc_getExpWidth(indices[x]));
    EXPECT_EQ(11, vc_getSigWidth(indices[x]));
    ASSERT_EQ(FLOATINGPOINT_TYPE, getType(values[x])) << "entry " << x;
    EXPECT_EQ(5, vc_getExpWidth(values[x]));
    EXPECT_EQ(11, vc_getSigWidth(values[x]));
  }

  // So every entry can be read back as an array access and re-asserted.
  for (int x = 0; x < size; x++)
    vc_assertFormula(vc,
                     vc_eqExpr(vc, vc_readExpr(vc, a, indices[x]), values[x]));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_deleteCounterExampleArray(indices, values, size);
  vc_Destroy(vc);
}

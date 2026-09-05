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
// equality stays opaque and traversable until the solve boundary, so
// whole-formula preparation (totalising partial operations, canonicalising
// float indexes, and pinning RoundingMode reads) reaches its operands before
// extensionality replaces it with a proxy and witness bundle.

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

// FpTotalise rewrites the nonconstant floating-point index in `stored` to
// its canonical bit representation before extensionality lowers `eq`. The C
// API handle still denotes the original opaque ARRAY_EQ, however, so model
// evaluation must follow that original node to the solve-local lowering of
// its rewritten counterpart. Exercise both Boolean values across scopes.
TEST(fp_array_extensionality,
     original_opaque_equality_handle_uses_totalised_model_lowering)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type fp = vc_fpType(vc, 5, 11);
  Type bv1 = vc_bvType(vc, 1);
  Type arr = vc_arrayType(vc, fp, bv1);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr b = vc_varExpr(vc, "b", arr);
  Expr i = vc_varExpr(vc, "i", fp);
  Expr one = vc_bvConstExprFromLL(vc, 1, 1);
  Expr stored = vc_writeExpr(vc, a, i, one);
  Expr eq = vc_eqExpr(vc, stored, b);

  vc_push(vc);
  vc_assertFormula(vc, eq);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, eq)));
  vc_pop(vc);

  vc_push(vc);
  vc_assertFormula(vc, vc_notExpr(vc, eq));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(FALSE, getExprKind(vc_getCounterExample(vc, eq)));
  vc_pop(vc);

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
  // The historic livelock needed MiniSat's model sequence; without that
  // backend the selection stays on the default, and the test still pins
  // the property that refinement over a float-indexed array terminates.
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

// An unsatisfiable query over (_ FloatingPoint 15 113), (_ BitVec 112)
// and (Array (_ BitVec 112) (_ BitVec 1)) that must stay unsatisfiable
// when it is solved again. Writing A for the array variable, x for the
// 112-bit variable, k for the 112-bit constant, f for the float
// variable and F for the float constant, the three assertions are
//
//   fp.leq(ite(fp.eq(f, f), f, F), ite(fp.eq(f, f), f, F))
//   bvslt(read(W, k), read(W, k)) <-> bvsle(read(W, k), read(A, x))
//   ite(fp.eq(f, f), A, W) = store(W, k, read(A, x))
//
// with W = store(A, bvsrem(x, k), read(A, x)). The first holds
// always: fp.eq(f, f) is false exactly when f is NaN, so the
// if-then-else never yields a NaN and fp.leq of a non-NaN with itself
// is true. It is there to keep the float condition in the formula. The
// second forces read(W, k) = 0 and read(A, x) = 1, because bvslt of a
// term with itself is false and the only 1-bit signed pair that is not
// bvsle-ordered is (0, 1). The third then fails in both branches of
// its if-then-else: taking A demands read(A, k) = 1 and hence
// read(W, k) = 1, taking W demands read(W, k) = read(A, x) = 1, and
// both contradict read(W, k) = 0. So the query is unsatisfiable
// whatever f is.
//
// Solving eliminates the array-valued if-then-else in favour of a
// fresh array pinned to the branches by two guarded equalities, and
// caches the replacement for later solves. The second solve inherited
// the replacement, and its equality records, without restating the
// guards -- an array related to nothing, which satisfies the third
// assertion on its own.
TEST(fp_array_extensionality, repeated_solve_restates_array_ite_guards)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type fp = vc_fpType(vc, 15, 113);
  Type bv1 = vc_bvType(vc, 1);
  Type bv112 = vc_bvType(vc, 112);
  Type arr = vc_arrayType(vc, bv112, bv1);

  Expr x = vc_varExpr(vc, "x", bv112);
  Expr f = vc_varExpr(vc, "f", fp);
  Expr a = vc_varExpr(vc, "a", arr);
  // A negative normal float: sign 1, biased exponent 1, so not a NaN.
  Expr fconst = vc_fpConstFromBits(
      vc, 15, 113,
      vc_bvConstExprFromStr(
          vc, "10000000000000011110010000000010110010100000111011001001001110"
              "011001011111111111001001100011111101011110110010001111010100"
              "001100"));
  Expr k = vc_bvConstExprFromStr(
      vc, "01111101101111000000010011110111101111010011000001011000100100"
          "01111100111010010010101100110011000111101001001011");

  Expr notNaN = vc_fpEqExpr(vc, f, f);
  Expr cell = vc_readExpr(vc, a, x);
  Expr w = vc_writeExpr(vc, a, vc_sbvRemExpr(vc, 112, x, k), cell);
  Expr chosen = vc_iteExpr(vc, notNaN, a, w);
  Expr pickedFloat = vc_iteExpr(vc, notNaN, f, fconst);
  Expr atK = vc_readExpr(vc, w, k);

  vc_assertFormula(vc, vc_fpLeqExpr(vc, pickedFloat, pickedFloat));
  vc_assertFormula(vc, vc_iffExpr(vc, vc_sbvLtExpr(vc, atK, atK),
                                  vc_sbvLeExpr(vc, atK, cell)));
  vc_assertFormula(vc, vc_eqExpr(vc, chosen, vc_writeExpr(vc, w, k, cell)));

  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// (Array (_ BitVec 3) (_ FloatingPoint 5 11)): one store on top of the
// array it stores into, written back the cell it already holds. A
// conversion to the cell's own format is the identity on values, so
// the store changes nothing and the two arrays are the same array.
//
// An equality whose two sides are a chain of writes and that chain's
// own base is rewritten into cell comparisons rather than abstracted
// into a record, so those comparisons carry the element sort's
// equality, not bit equality. Compared as bits, a NaN payload held in
// the cell and the canonical NaN the conversion packs "differ", and
// the negated equality -- the store and its base are different arrays
// -- came out satisfiable over a single array.
TEST(fp_array_extensionality, write_chain_over_float_cells_quotients_nan)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type fp = vc_fpType(vc, 5, 11);
  Type bv3 = vc_bvType(vc, 3);
  Type arr = vc_arrayType(vc, bv3, fp);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr i = vc_varExpr(vc, "i", bv3);
  Expr cell = vc_readExpr(vc, a, i);
  Expr same =
      vc_fpToFPFromFP(vc, 5, 11, vc_fpRoundingMode(vc, VC_RM_RNE), cell);

  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_writeExpr(vc, a, i, same), a)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// (Array (_ BitVec 64) (_ FloatingPoint 11 53)): a three-way equality
// between an array variable and two store chains over it, alongside an
// fp.isZero on the float the chains store. Writing A for the array
// variable, x for the float variable and k for the all-ones index,
//
//   B = store(store(A, k, x), 0, x)      the shorter chain
//   C = store(B, k, -oo)                 the longer one
//
// and the query asserts fp.isZero(x) and A = C = B. The last write at
// an index decides the contents, so C = B needs B at k -- which is x,
// since the store at 0 is elsewhere -- to be -oo. But fp.isZero(x)
// holds only of the two zeroes, so the query is unsatisfiable.
//
// Solving abstracts the reads of A into fresh float-typed variables,
// and pinning one of those to -oo leaves its significand half equated
// to a constant. The word-level solver takes such an equation apart:
// it eliminates the variable an extract from bit 0 is taken of, by
// renaming the whole variable to a fresh variable concatenated with
// the solved bits. That concatenation is an ordinary bitvector node
// and carries no floating-point format, and the format is exactly what
// the float blaster -- which runs after the solver, and reads an
// operation's format off its operands -- needs to lower the fp.isZero
// still standing over the renamed variable. It blasted against a
// format of (0, 0):
//
//   symbolic_fp.cpp: blast_is_zero: Assertion
//     `expr.GetValueWidth() == size.packedWidth()' failed.
//
// Found by fuzzing with murxla; delta-minimized, then transcribed term
// for term (bar the assertions -- see below).
TEST(fp_array_extensionality, float_cell_pinned_under_chain_equality_unsat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type fp = vc_fpType(vc, 11, 53);
  Type bv64 = vc_bvType(vc, 64);
  Type arr = vc_arrayType(vc, bv64, fp);

  Expr moo = vc_fpMinusInfinity(vc, fp);
  Expr zero = vc_bvConstExprFromLL(vc, 64, 0);
  Expr x = vc_varExpr(vc, "x", fp);
  Expr a = vc_varExpr(vc, "a", arr);
  Expr ones = vc_bvXnorExpr(vc, zero, zero);

  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, x));

  Expr b = vc_writeExpr(vc, vc_writeExpr(vc, a, ones, x), zero, x);
  Expr c = vc_writeExpr(vc, b, ones, moo);

  // A = C = B. The trace states this as one three-way equality; here it
  // is the two conjuncts that means, asserted separately. The shape
  // matters -- conjoining them into a single assertion instead happens
  // to simplify down a path that never reaches the equation this goes
  // wrong on. BVSolver_Test pins the defect itself, equation in hand.
  vc_assertFormula(vc, vc_eqExpr(vc, a, c));
  vc_assertFormula(vc, vc_eqExpr(vc, c, b));

  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// The same defect as reached by fuzzing: three arrays over
// (Array (_ BitVec 15) (_ FloatingPoint 5 11)), built by long store
// chains off one base, asserted pairwise distinct.
//
// Writing r for the RoundingMode variable, x for the (_ BitVec 15)
// variable and A for the array variable, the terms are
//
//   k = #b011100111100100                  a constant index
//   j = ite(r != RNE, k, x)                a second index
//   d = bvadd(x, x)                        a third index
//   n = ((_ to_fp 5 11) RNE x)             15 signed bits always fit, so
//                                          n is finite and z below a zero
//   z = fp.sub(r, n, n)                    -0 under RTN, +0 otherwise
//   c = select(A, x)
//   W = store(A, j, z)
//   p = select(W, x)
//   s = fp.add(r, p, z)
//
// and, writing B for store(store(W, k, p), x, n), the three arrays are
//
//   A1 = B then x:=n, x:=n, d:=z, x:=n, x:=z, x:=z
//   A3 = B then x:=n five times, d:=c, x:=n, x:=z
//   A2 = A3 then j:=n, k:=n, j:=n, k:=n, j:=n, d:=s,
//                j:=n four times, k:=z, j:=n, j:=p
//
// Take r != RNE, so that j is the constant k, and take x != k, so that
// p is c. The last write at an index decides the contents, so A1 and
// A3 agree everywhere except at d, where A1 holds z and A3 holds c,
// and A2 agrees with A3 except at d, where it holds s. If d is x or k
// the writes at d are shadowed and two of the three arrays coincide,
// so pairwise distinctness needs d to be an index of its own; then
// A2 != A3 needs s != c. Now z is a zero, and adding a zero returns
// its operand except when that operand is itself a zero of the other
// sign: fp.add(r, c, z) differs from c only when c is a zero and z is
// the opposite zero, and then it is z. So A2 != A3 forces s = z, which
// is what A1 holds at d, making A1 and A2 the same array. Taking
// r = RNE instead makes j the index x, so p and s are both z and A1
// and A2 coincide again. The three cannot be pairwise distinct.
//
// A2 stacks its writes directly on A3, so that pair is exactly the
// chain-and-its-base shape rewritten into cell comparisons. Compared
// as bits, a NaN payload for c and the canonical NaN that fp.add packs
// for s "differ" at d, and the query answered satisfiable with a model
// whose A2 and A3 are one array.
TEST(fp_array_extensionality, distinct_float_arrays_off_a_shared_chain)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type fp = vc_fpType(vc, 5, 11);
  Type bv15 = vc_bvType(vc, 15);
  Type arr = vc_arrayType(vc, bv15, fp);

  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", bv15);
  Expr a = vc_varExpr(vc, "a", arr);

  Expr k = vc_bvConstExprFromStr(vc, "011100111100100");
  Expr j = vc_iteExpr(vc, vc_notExpr(vc, vc_eqExpr(vc, r, rne)), k, x);
  Expr d = vc_bvPlusExpr(vc, 15, x, x);
  Expr n = vc_fpToFPFromSignedBV(vc, 5, 11, rne, x);
  Expr z = vc_fpSubExpr(vc, r, n, n);
  Expr c = vc_readExpr(vc, a, x);
  Expr w = vc_writeExpr(vc, a, j, z);
  Expr p = vc_readExpr(vc, w, x);
  Expr s = vc_fpAddExpr(vc, r, p, z);

  Expr base = vc_writeExpr(vc, vc_writeExpr(vc, w, k, p), x, n);

  Expr a1 = vc_writeExpr(vc, base, x, n);
  a1 = vc_writeExpr(vc, a1, x, n);
  a1 = vc_writeExpr(vc, a1, d, z);
  a1 = vc_writeExpr(vc, a1, x, n);
  a1 = vc_writeExpr(vc, a1, x, z);
  a1 = vc_writeExpr(vc, a1, x, z);

  Expr a3 = base;
  for (int step = 0; step < 5; step++)
    a3 = vc_writeExpr(vc, a3, x, n);
  a3 = vc_writeExpr(vc, a3, d, c);
  a3 = vc_writeExpr(vc, a3, x, n);
  a3 = vc_writeExpr(vc, a3, x, z);

  Expr a2 = vc_writeExpr(vc, a3, j, n);
  a2 = vc_writeExpr(vc, a2, k, n);
  a2 = vc_writeExpr(vc, a2, j, n);
  a2 = vc_writeExpr(vc, a2, k, n);
  a2 = vc_writeExpr(vc, a2, j, n);
  a2 = vc_writeExpr(vc, a2, d, s);
  for (int step = 0; step < 4; step++)
    a2 = vc_writeExpr(vc, a2, j, n);
  a2 = vc_writeExpr(vc, a2, k, z);
  a2 = vc_writeExpr(vc, a2, j, n);
  a2 = vc_writeExpr(vc, a2, j, p);

  Expr distinct[3] = {vc_notExpr(vc, vc_eqExpr(vc, a1, a2)),
                      vc_notExpr(vc, vc_eqExpr(vc, a1, a3)),
                      vc_notExpr(vc, vc_eqExpr(vc, a2, a3))};
  vc_assertFormula(vc, vc_andExprN(vc, distinct, 3));

  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// The same word-level-solver defect as
// float_cell_pinned_under_chain_equality_unsat above, and closed by the
// same fix, but reached a second way -- so that a regression that
// re-breaks one trigger and not the other cannot pass unnoticed.
//
// There, the format-less float met the blaster through a classify
// predicate (fp.isZero -> blast_is_zero). Here there is no classify
// predicate at all. A chain equality pins a Float128 variable's bits to
// a constant; the solver eliminates the variable by renaming it through
// a concatenation, which carries no floating-point format; and the
// renamed float, its (15, 113) format now gone, reaches constant
// construction with a zero-width format instead:
//
//   STPManager.cpp: CreateFPConst: Assertion
//     `exp_width + sig_width == bvconst.GetValueWidth()' failed.
//
// a different abort site (STPManager, not symbolic_fp) for one root
// cause. Found by fuzzing with murxla over QF_ABVFP; delta-minimized,
// then transcribed term for term, in the order the trace built them --
// the assumption equality before the store chain -- because the defect
// is sensitive to construction order and the SMT-LIB frontend, which
// builds the asserted term first, does not reproduce it.
//
// Two writes to _x1: cell IDX holds +zero and cell 0 holds -_x3, while
// the assumption holds _x1[IDX] = _x3. So _x3 is a +zero, _x1[0] a
// -zero, and the query is satisfiable (bitwuzla agrees).
TEST(fp_array_extensionality, float_cell_negated_under_chain_equality_sat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type fp = vc_fpType(vc, 15, 113);
  Type bv128 = vc_bvType(vc, 128);
  Type arr = vc_arrayType(vc, bv128, fp);

  Expr ones = vc_bvNotExpr(vc, vc_bvConstExprFromLL(vc, 128, 0));
  Expr a = vc_varExpr(vc, "a", arr);
  Expr idx = vc_bvConstExprFromStr(
      vc,
      "01101001011011110101001010000101111011011011101001100101101001101"
      "111001100111100111101001100000001011011000111010111000110001010");
  // 0x696f5285edba65a6f33cf4c05b1d718a
  Expr x = vc_varExpr(vc, "x", fp);

  // The assumption equality, built first as the trace does.
  Expr assumption = vc_eqExpr(vc, vc_writeExpr(vc, a, idx, x), a);

  Expr zero128 = vc_bvMinusExpr(vc, 128, ones, ones); // a second, constant index
  Expr negx = vc_fpNegExpr(vc, x);
  Expr pzero = vc_fpPlusZero(vc, fp);

  Expr chain = vc_writeExpr(vc, a, idx, x);
  chain = vc_writeExpr(vc, chain, idx, pzero);
  chain = vc_writeExpr(vc, chain, zero128, pzero);
  chain = vc_writeExpr(vc, chain, zero128, negx);

  vc_assertFormula(vc, vc_eqExpr(vc, chain, a));

  // The assumption enters its own scope, as check-sat-assuming does.
  vc_push(vc);
  vc_assertFormula(vc, assumption);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // 0 == INVALID == satisfiable
  vc_pop(vc);

  vc_Destroy(vc);
}

// RoundingMode is a five-value source sort, not a synonym for its 5-bit
// implementation carrier.  Keep the public array boundary honest even though
// the packed widths happen to agree.
TEST(fp_array_extensionality, rm_value_is_rejected_by_bv5_array)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Type arr = vc_arrayType(vc, vc_bvType(vc, 1), vc_bvType(vc, 5));
        Expr a = vc_varExpr(vc, "a", arr);
        Expr i = vc_bvConstExprFromLL(vc, 1, 0);
        Expr r = vc_fpRoundingModeVar(vc, "r");
        (void)vc_writeExpr(vc, a, i, r);
      },
      "stored value sort differs from the array's bitvector element sort");
}

// A RoundingMode *symbol* that occurs nowhere but inside an array equality's
// operands.
//
// Declaring a mode pins its 5-bit carrier to the five one-hot encodings by
// asserting the constraint, and an assertion belongs to the level current at
// the time while the hash-consed symbol does not -- so building the mode in a
// vc_push/vc_pop bracket leaves it alive and unpinned. FpTotalise re-pins
// every mode the completed input formula names. An opaque array equality must
// therefore retain and expose its operands until that whole-formula pass:
// otherwise `r` is free to take one of the carrier's 27 junk patterns and STP
// answers sat to an unsatisfiable query.
//
// The equality compares two well-typed (Array (_ BitVec 1)
// (_ FloatingPoint 8 24)) store chains.  Its left-hand cells are
//
//   fp.mul(r, 2^-100, 2^-100)  and  fp.div(r, 1.0, 3.0),
//
// while its right-hand cells are the minimum positive subnormal and the lower
// binary32 approximation to 1/3.  No legal mode produces that pair: only RTP
// rounds the positive underflow up to the minimum subnormal, but RTP rounds
// 1/3 to the upper approximation; RTN and RTZ produce the requested lower
// approximation to 1/3, but round the underflow to +zero.  A junk carrier,
// however, matches none of SymFPU's five mode tests and exhibits exactly this
// non-IEEE combination.  The equality is therefore unsatisfiable precisely
// when whole-formula preparation reaches its operands and re-pins `r`.
TEST(fp_array_extensionality, rm_symbol_only_in_operands_stays_pinned)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type fp = vc_fpType(vc, 8, 24);
  Type arr = vc_arrayType(vc, vc_bvType(vc, 1), fp);
  Expr a = vc_varExpr(vc, "a", arr);
  Expr i0 = vc_bvConstExprFromLL(vc, 1, 0);
  Expr i1 = vc_bvConstExprFromLL(vc, 1, 1);
  Expr tiny = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x0D800000ULL)); // 2^-100
  Expr one = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x3F800000ULL));
  Expr three = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x40400000ULL));
  Expr minSubnormal = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x00000001ULL));
  Expr thirdDown = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x3EAAAAAAULL));

  // The bracket: `r`'s declaration constraint is asserted here and dies with
  // the level. The opaque equality is built here too, but remains traversable
  // when it is asserted and solved outside the bracket.
  vc_push(vc);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr actual = vc_writeExpr(
      vc, vc_writeExpr(vc, a, i0, vc_fpMulExpr(vc, r, tiny, tiny)), i1,
      vc_fpDivExpr(vc, r, one, three));
  Expr impossible = vc_writeExpr(
      vc, vc_writeExpr(vc, a, i0, minSubnormal), i1, thirdDown);
  Expr eq = vc_eqExpr(vc, actual, impossible);
  vc_pop(vc);

  vc_assertFormula(vc, eq);
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc))); // unsatisfiable

  vc_Destroy(vc);
}

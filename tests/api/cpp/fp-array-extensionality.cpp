/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// fp-array-extensionality.cpp -- whole-array equality (array-equality =
// on, the 2.x 'x' flag) over arrays whose index or element sorts are
// floating-point or RoundingMode, built through the 3.x API. The equality
// stays opaque and traversable until the solve boundary, so whole-formula
// preparation (totalising partial operations, canonicalising float indexes,
// and pinning RoundingMode reads) reaches its operands before extensionality
// replaces it with a proxy and witness bundle.

#include "api_common.hpp"

#include <vector>

using namespace stp;

namespace
{

// The checker these regressions ran on: array equality forced on (the 2.x 'x'
// flag), and the counterexample of every satisfiable answer built and checked
// against the input. 2.x forced that check ('d') on every checker; 3.x leaves
// check-sanity off by default, so it is asked for here.
Options checker_options()
{
  Options o;
  o.set_str("array-equality", "on");
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

// (Array RoundingMode (_ FloatingPoint 5 11)): two stores at one
// RoundingMode index whose values are always =-equal floats --
// fp.min(f, x) against x where x is f converted to its own format.
// The fp.min inside the abstracted operand used to reach the float
// blaster without its totalised third child and abort the solve.
TEST(fp_array_extensionality, rm_indexed_equal_stores_sat)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort rm = tm.mk_rm_sort();
  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort arr = tm.mk_array_sort(rm, fp);

  const Term a = tm.declare("a", arr);
  const Term r = tm.declare("r", rm);
  const Term f = tm.declare("f", fp);
  const Term tofp = to_fp(fp, r, f);
  const Term mn = fp_min(f, tofp);
  const Term s1 = store(a, r, mn);
  const Term s2 = store(s1, r, tofp);

  s.add(s1 == s2);
  EXPECT_TRUE(s.check_sat().is_sat());
}

// The negation of the same equality is unsatisfiable: a same-format
// conversion is the identity on values, fp.min of a value with itself
// is that value, so the two stores agree at the written index and
// share the base everywhere else.
TEST(fp_array_extensionality, rm_indexed_equal_stores_distinct_unsat)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort rm = tm.mk_rm_sort();
  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort arr = tm.mk_array_sort(rm, fp);

  const Term a = tm.declare("a", arr);
  const Term r = tm.declare("r", rm);
  const Term f = tm.declare("f", fp);
  const Term tofp = to_fp(fp, r, f);
  const Term mn = fp_min(f, tofp);
  const Term s1 = store(a, r, mn);
  const Term s2 = store(s1, r, tofp);

  s.add(!(s1 == s2));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// FpTotalise rewrites the nonconstant floating-point index in `stored` to
// its canonical bit representation before extensionality lowers `eq`. The
// API's term still denotes the original opaque ARRAY_EQ, however, so model
// evaluation must follow that original node to the solve-local lowering of
// its rewritten counterpart. Exercise both Boolean values across scopes.
TEST(fp_array_extensionality, original_opaque_equality_handle_uses_totalised_model_lowering)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort bv1 = tm.mk_bv_sort(1);
  const Sort arr = tm.mk_array_sort(fp, bv1);

  const Term a = tm.declare("a", arr), b = tm.declare("b", arr);
  const Term i = tm.declare("i", fp);
  const Term one = tm.mk_bv(1, 1);
  const Term stored = store(a, i, one);
  const Term eq = stored == b;

  s.push();
  s.add(eq);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(eq));
  s.pop();

  s.push();
  s.add(!eq);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(s.model().bool_value(eq));
  s.pop();
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
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort bv5 = tm.mk_bv_sort(5);
  const Sort arr = tm.mk_array_sort(fp, bv5);

  const Term x1 = tm.declare("x1", bv5);
  const Term x2 = tm.declare("x2", fp);
  const Term moo = tm.mk_fp_neg_inf(fp);
  const Term x3 = tm.declare("x3", arr);
  const Term x4 = tm.declare("x4", bv5);
  const Term x10 = tm.declare("x10", arr);
  const Term t14 = x3[x2];
  const Term t18 = fp_rem(x2, x2);
  const Term t20 = x10[x2];
  const Term t27 = x10[t18];
  const Term t28 = fp_rem(t18, t18);
  const Term t34 = store(x10, moo, t20);
  const Term t35 = store(t34, x2, t27);
  const Term t36 = store(t35, moo, x4);
  const Term t37 = store(t36, x2, x4);
  const Term t38 = store(t37, moo, x1);
  const Term t39 = store(t38, t18, t14);
  const Term t40 = store(t39, t28, x4);

  s.add(t14 == x4);
  s.add(fp_geq(moo, x2));
  s.add((t35 == t40) && (t40 == t34));
  EXPECT_TRUE(s.check_sat().is_sat());
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
  TermManager tm;
  Options o = checker_options();
  // The historic livelock needed MiniSat's model sequence; without that
  // backend the selection stays on the default, and the test still pins
  // the property that refinement over a float-indexed array terminates.
  if (has_sat_backend("minisat"))
    o.set_str("sat-backend", "minisat");
  Solver s(tm, o);

  const Sort fp = tm.mk_fp_sort(8, 24);
  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort arr = tm.mk_array_sort(fp, bv8);

  const Term a0 = tm.declare("a0", arr);
  const Term a1 = tm.declare("a1", arr);
  const Term a2 = tm.declare("a2", arr);
  const Term bits = tm.mk_bv(32, "1542123083", 10);
  const Term idx = to_fp_from_bits(fp, bits);
  const Term r1 = a2[idx];
  const Term r2 = a1[idx];
  const Term s1 = store(a0, idx, r1);
  const Term s2 = store(a0, idx, r2);

  s.add(bvule(r2, r1));
  s.add(fp_is_zero(idx) == (s2 == s1));
  EXPECT_TRUE(s.check_sat().is_sat());
}

// With array equality on, the array model comes out of the deterministic
// sorted extraction rather than the pre-extension traversal. Both owe the
// caller entries at the array's declared sorts, so that an entry can be
// fed back -- see fp-model-roundtrip.cpp, which pins the same
// obligation on the traversal path.
TEST(fp_array_extensionality, sorted_model_entries_carry_their_sorts)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort f = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(f, f));
  const Term i = tm.declare("i", f);
  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0x3C00));

  s.add(a[i] == one);
  ASSERT_TRUE(s.check_sat().is_sat());

  const std::vector<ArrayValue::Entry> entries = s.model().array_value(a).entries();
  ASSERT_GE(entries.size(), 1u);

  // Asserted, not expected: a read at an index not of the array's index
  // sort is refused (SORT_MISMATCH), and the loop below reads at each one.
  for (std::size_t x = 0; x < entries.size(); x++)
  {
    ASSERT_TRUE(entries[x].index.sort().is_fp()) << "entry " << x;
    EXPECT_EQ(5u, entries[x].index.sort().fp_exp_size());
    EXPECT_EQ(11u, entries[x].index.sort().fp_sig_size());
    ASSERT_TRUE(entries[x].element.sort().is_fp()) << "entry " << x;
    EXPECT_EQ(5u, entries[x].element.sort().fp_exp_size());
    EXPECT_EQ(11u, entries[x].element.sort().fp_sig_size());
  }

  // So every entry can be read back as an array access and re-asserted.
  for (const ArrayValue::Entry& e : entries)
    s.add(a[e.index] == e.element);
  ASSERT_TRUE(s.check_sat().is_sat());
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
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(15, 113);
  const Sort bv1 = tm.mk_bv_sort(1);
  const Sort bv112 = tm.mk_bv_sort(112);
  const Sort arr = tm.mk_array_sort(bv112, bv1);

  const Term x = tm.declare("x", bv112);
  const Term f = tm.declare("f", fp);
  const Term a = tm.declare("a", arr);
  // A negative normal float: sign 1, biased exponent 1, so not a NaN.
  const Term fconst = tm.mk_fp_from_bits(
      fp, tm.mk_bv(128,
                   "10000000000000011110010000000010110010100000111011001001001110"
                   "011001011111111111001001100011111101011110110010001111010100"
                   "001100",
                   2));
  const Term k = tm.mk_bv(112,
                          "01111101101111000000010011110111101111010011000001011000100100"
                          "01111100111010010010101100110011000111101001001011",
                          2);

  const Term notNaN = fp_eq(f, f);
  const Term cell = a[x];
  const Term w = store(a, bvsrem(x, k), cell);
  const Term chosen = ite(notNaN, a, w);
  const Term pickedFloat = ite(notNaN, f, fconst);
  const Term atK = w[k];

  s.add(fp_leq(pickedFloat, pickedFloat));
  s.add(bvslt(atK, atK) == bvsle(atK, cell));
  s.add(chosen == store(w, k, cell));

  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_TRUE(s.check_sat().is_unsat());
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
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort bv3 = tm.mk_bv_sort(3);
  const Sort arr = tm.mk_array_sort(bv3, fp);

  const Term a = tm.declare("a", arr);
  const Term i = tm.declare("i", bv3);
  const Term cell = a[i];
  const Term same = to_fp(fp, tm.mk_rm(RoundingMode::RNE), cell);

  s.add(!(store(a, i, same) == a));
  EXPECT_TRUE(s.check_sat().is_unsat());
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
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(11, 53);
  const Sort bv64 = tm.mk_bv_sort(64);
  const Sort arr = tm.mk_array_sort(bv64, fp);

  const Term moo = tm.mk_fp_neg_inf(fp);
  const Term zero = tm.mk_bv(64, 0);
  const Term x = tm.declare("x", fp);
  const Term a = tm.declare("a", arr);
  const Term ones = bvxnor(zero, zero);

  s.add(fp_is_zero(x));

  const Term b = store(store(a, ones, x), zero, x);
  const Term c = store(b, ones, moo);

  // A = C = B. The trace states this as one three-way equality; here it
  // is the two conjuncts that means, asserted separately. The shape
  // matters -- conjoining them into a single assertion instead happens
  // to simplify down a path that never reaches the equation this goes
  // wrong on. BVSolver_Test pins the defect itself, equation in hand.
  s.add(a == c);
  s.add(c == b);

  EXPECT_TRUE(s.check_sat().is_unsat());
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
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(5, 11);
  const Sort bv15 = tm.mk_bv_sort(15);
  const Sort arr = tm.mk_array_sort(bv15, fp);

  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term x = tm.declare("x", bv15);
  const Term a = tm.declare("a", arr);

  const Term k = tm.mk_bv(15, "011100111100100", 2);
  const Term j = ite(!(r == rne), k, x);
  const Term d = bvadd(x, x);
  const Term n = to_fp(fp, rne, x);
  const Term z = fp_sub(r, n, n);
  const Term c = a[x];
  const Term w = store(a, j, z);
  const Term p = w[x];
  const Term sum = fp_add(r, p, z);

  const Term base = store(store(w, k, p), x, n);

  Term a1 = store(base, x, n);
  a1 = store(a1, x, n);
  a1 = store(a1, d, z);
  a1 = store(a1, x, n);
  a1 = store(a1, x, z);
  a1 = store(a1, x, z);

  Term a3 = base;
  for (int step = 0; step < 5; step++)
    a3 = store(a3, x, n);
  a3 = store(a3, d, c);
  a3 = store(a3, x, n);
  a3 = store(a3, x, z);

  Term a2 = store(a3, j, n);
  a2 = store(a2, k, n);
  a2 = store(a2, j, n);
  a2 = store(a2, k, n);
  a2 = store(a2, j, n);
  a2 = store(a2, d, sum);
  for (int step = 0; step < 4; step++)
    a2 = store(a2, j, n);
  a2 = store(a2, k, z);
  a2 = store(a2, j, n);
  a2 = store(a2, j, p);

  s.add(and_({!(a1 == a2), !(a1 == a3), !(a2 == a3)}));

  EXPECT_TRUE(s.check_sat().is_unsat());
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
// -zero, and the query is satisfiable.
TEST(fp_array_extensionality, float_cell_negated_under_chain_equality_sat)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(15, 113);
  const Sort bv128 = tm.mk_bv_sort(128);
  const Sort arr = tm.mk_array_sort(bv128, fp);

  const Term ones = bvnot(tm.mk_bv(128, 0));
  const Term a = tm.declare("a", arr);
  const Term idx = tm.mk_bv(128,
                            "01101001011011110101001010000101111011011011101001100101101001101"
                            "111001100111100111101001100000001011011000111010111000110001010",
                            2);
  // 0x696f5285edba65a6f33cf4c05b1d718a
  const Term x = tm.declare("x", fp);

  // The assumption equality, built first as the trace does.
  const Term assumption = store(a, idx, x) == a;

  const Term zero128 = bvsub(ones, ones); // a second, constant index
  const Term negx = fp_neg(x);
  const Term pzero = tm.mk_fp_pos_zero(fp);

  Term chain = store(a, idx, x);
  chain = store(chain, idx, pzero);
  chain = store(chain, zero128, pzero);
  chain = store(chain, zero128, negx);

  s.add(chain == a);

  // The assumption enters its own scope, as it did in the 2.x
  // transcription of check-sat-assuming.
  s.push();
  s.add(assumption);
  EXPECT_TRUE(s.check_sat().is_sat());
  s.pop();
}

// RoundingMode is a five-value source sort, not a synonym for its 5-bit
// implementation carrier. Keep the public array boundary honest even though
// the packed widths happen to agree. 2.x ended the process here; the API
// refuses the store with a recoverable SORT_MISMATCH and builds nothing.
TEST(fp_array_extensionality, rm_value_is_rejected_by_bv5_array)
{
  TermManager tm;
  const Sort arr = tm.mk_array_sort(tm.mk_bv_sort(1), tm.mk_bv_sort(5));
  const Term a = tm.declare("a", arr);
  const Term i = tm.mk_bv(1, 0);
  const Term r = tm.declare("r", tm.mk_rm_sort());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)store(a, i, r));
}

// A RoundingMode *symbol* that occurs nowhere but inside an array equality's
// operands.
//
// The engine carries a mode in five bits, of which only the five one-hot
// patterns are modes. FpTotalise re-pins every mode the completed input
// formula names to those patterns. An opaque array equality must therefore
// retain and expose its operands until that whole-formula pass: otherwise
// `r` is free to take one of the carrier's 27 junk patterns and STP answers
// sat to an unsatisfiable query.
//
// In 2.x, declaring the mode also asserted its pin, at the level current at
// the time, while the hash-consed symbol outlived that level: building the
// mode inside a push/pop bracket left it alive and unpinned. A declaration
// under the API belongs to the manager and asserts nothing, so the pin can
// only come from preparation reaching the operands. The bracket is kept, as
// the scenario the regression was written against.
//
// The equality compares two well-typed (Array (_ BitVec 1)
// (_ FloatingPoint 8 24)) store chains. Its left-hand cells are
//
//   fp.mul(r, 2^-100, 2^-100)  and  fp.div(r, 1.0, 3.0),
//
// while its right-hand cells are the minimum positive subnormal and the lower
// binary32 approximation to 1/3. No legal mode produces that pair: only RTP
// rounds the positive underflow up to the minimum subnormal, but RTP rounds
// 1/3 to the upper approximation; RTN and RTZ produce the requested lower
// approximation to 1/3, but round the underflow to +zero. A junk carrier,
// however, matches none of SymFPU's five mode tests and exhibits exactly this
// non-IEEE combination. The equality is therefore unsatisfiable precisely
// when whole-formula preparation reaches its operands and re-pins `r`.
TEST(fp_array_extensionality, rm_symbol_only_in_operands_stays_pinned)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort fp = tm.mk_fp_sort(8, 24);
  const Sort arr = tm.mk_array_sort(tm.mk_bv_sort(1), fp);
  const Term a = tm.declare("a", arr);
  const Term i0 = tm.mk_bv(1, 0), i1 = tm.mk_bv(1, 1);
  const Term tiny = tm.mk_fp_from_bits(fp, tm.mk_bv(32, 0x0D800000)); // 2^-100
  const Term one = tm.mk_fp_from_bits(fp, tm.mk_bv(32, 0x3F800000));
  const Term three = tm.mk_fp_from_bits(fp, tm.mk_bv(32, 0x40400000));
  const Term minSubnormal = tm.mk_fp_from_bits(fp, tm.mk_bv(32, 0x00000001));
  const Term thirdDown = tm.mk_fp_from_bits(fp, tm.mk_bv(32, 0x3EAAAAAA));

  // The bracket: `r` and the opaque equality are built inside it, and the
  // equality is asserted and solved outside it.
  s.push();
  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term actual = store(store(a, i0, fp_mul(r, tiny, tiny)), i1, fp_div(r, one, three));
  const Term impossible = store(store(a, i0, minSubnormal), i1, thirdDown);
  const Term eq = actual == impossible;
  s.pop();

  s.add(eq);
  EXPECT_TRUE(s.check_sat().is_unsat()); // unsatisfiable
}

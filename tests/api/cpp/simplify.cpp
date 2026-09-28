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

// simplify.cpp -- simplification of a word reassembled from a byte array
// and cut back to its low byte, and of the engine's native distinct.
//
// 2.x's vc_simplify ran the solver's simplifier over a term, and lowered a
// native distinct first, as the solve paths do before preprocessing. 3.x's
// TermManager::simplify is local folding only and touches no solver, and
// distinct is a public kind: simplify keeps it, and the check lowers it. The
// native distinct is built on the manager's own engine (api_engine.hpp).

#include "api_engine.hpp"

#include <string>

using namespace stp::api;

namespace
{

// vc_bvCreateMemoryArray: bytes indexed by 32-bit addresses.
Term memoryArray(TermManager& tm, const char* name)
{
  return tm.declare(name, tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));
}

// 2.x set 'n', 'd' and 'p'. 'n' printed the verdict, which 3.x returns as a
// value; 'd' and 'p' are check-sanity and print-counterex.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("print-counterex", true);
  return o;
}

} // namespace

TEST(simplify, one)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term a = memoryArray(tm, "a");
  const Term index_3 = tm.mk_bv(32, 3);
  Term a_of_0 = a[index_3];
  for (int i = 2; i >= 0; i--)
    a_of_0 = concat(a_of_0, a[tm.mk_bv(32, i)]);
  const Term cast_32_to_8 = extract(7, 0, a_of_0);
  // 2.x's vc_bvSignExtend extended to a width; 3.x's sign_extend extends by a count
  const Term cast_8_to_32 = sign_extend(24, cast_32_to_8);
  // vc_printExpr: the presentation language
  EXPECT_EQ(cast_8_to_32.to_string(Format::CVC).rfind("BVSX(a[0x00000000],32)", 0), 0u)
      << cast_8_to_32.to_string(Format::CVC);

  // The manager folds at construction: the low byte of the reassembled word
  // is the read of a[0], sign-extended.
  const Term expected = sign_extend(24, a[tm.mk_bv(32, 0)]);
  EXPECT_EQ(cast_8_to_32.sort().bv_size(), 32u);
  EXPECT_TRUE(cast_8_to_32.same_as(expected));
  EXPECT_TRUE(s.entails(cast_8_to_32 == expected).is_valid());
}

TEST(simplify, two)
{
  for (int j = 0; j < 3; j++)
  {
    TermManager tm;
    Solver s(tm, checkerOptions());

    const Term a = memoryArray(tm, "a");
    const Term index_3 = tm.mk_bv(32, 3);

    Term a_of_0 = a[index_3];
    for (int i = 2; i >= 0; i--)
      a_of_0 = concat(a_of_0, a[tm.mk_bv(32, i)]);
    const Term cast_32_to_8 = extract(7, 0, a_of_0);
    const Term cast_8_to_32 = sign_extend(24, cast_32_to_8);
    EXPECT_EQ(cast_8_to_32.to_string(Format::CVC).rfind("BVSX(a[0x00000000],32)", 0), 0u);
    const Term simplified = tm.simplify(cast_8_to_32);
    // folded at construction already: simplify has nothing left to do
    EXPECT_TRUE(simplified.same_as(cast_8_to_32));
  }

  // Without construction-time folding the term is kept as written, and
  // simplify does the folding.
  TermManager raw = api_test::raw_manager();
  const Term a = memoryArray(raw, "a");
  Term a_of_0 = a[raw.mk_bv(32, 3)];
  for (int i = 2; i >= 0; i--)
    a_of_0 = concat(a_of_0, a[raw.mk_bv(32, i)]);
  const Term cast_8_to_32 = sign_extend(24, extract(7, 0, a_of_0));
  EXPECT_EQ(cast_8_to_32.child(0).kind(), stp::api::Kind::BV_EXTRACT);
  const Term simplified = raw.simplify(cast_8_to_32);
  EXPECT_TRUE(simplified.same_as(sign_extend(24, a[raw.mk_bv(32, 0)]))) << simplified;
}

// A native distinct over three symbols, built on the manager's engine as 2.x
// built it on the checker's. 2.x's vc_simplify had to lower it before its
// simplifier saw it.
TEST(simplify, native_distinct_is_lowered_before_preprocessing)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true); // 'd', as vc_createValidityChecker set it
  Solver s(tm, o);
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term y = tm.declare("y", bv8);
  const Term z = tm.declare("z", bv8);
  stp::STPMgr& mgr = api_test::engine_manager(tm);
  const stp::ASTNode native = mgr.CreateNode(
      stp::DISTINCT,
      stp::ASTVec{api_test::engine_node(x), api_test::engine_node(y), api_test::engine_node(z)});
  const Term t = api_test::api_term(tm, native);

  // 3.x: distinct is a public kind, and simplify (local folding, no solver)
  // keeps it; the native node is the one the public constructor builds.
  const Term simplified = tm.simplify(t);
  EXPECT_EQ(simplified.kind(), stp::api::Kind::DISTINCT);
  EXPECT_TRUE(stp::containsKind(api_test::engine_node(simplified), stp::DISTINCT));
  EXPECT_TRUE(simplified.same_as(distinct({x, y, z})));

  // The check lowers it before preprocessing and decides it: three pairwise
  // different values, and unsat once two of them are forced equal.
  s.add(simplified);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_NE(m.uint64_value(x), m.uint64_value(y));
  EXPECT_NE(m.uint64_value(x), m.uint64_value(z));
  EXPECT_NE(m.uint64_value(y), m.uint64_value(z));
  EXPECT_TRUE(m.bool_value(simplified));
  s.add(x == z);
  EXPECT_TRUE(s.check_sat().is_unsat());
}

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

#include "api_common.hpp"

using namespace stp;

TEST(BooleanArrays, source_terms_round_trip_without_exposing_carriers)
{
  for (bool simplify : {false, true})
  {
    SCOPED_TRACE(simplify);
    TermManager::Config config;
    config.simplify = simplify;
    TermManager tm(config);
    Solver s(tm);
    const Sort boolean = tm.mk_bool_sort(), bit = tm.mk_bv_sort(1);
    const Sort array = tm.mk_array_sort(boolean, boolean);
    const Term a = tm.declare("a", array);
    const Term p = tm.declare("p", boolean), q = tm.declare("q", boolean);
    const Term read = select(a, p), write = store(a, p, q);
    ASSERT_EQ(read.kind(), Kind::SELECT);
    ASSERT_EQ(read.num_children(), 2u);
    EXPECT_TRUE(read.sort() == boolean);
    EXPECT_TRUE(read.child(0).same_as(a));
    EXPECT_TRUE(read.child(1).same_as(p));
    ASSERT_EQ(write.kind(), Kind::STORE);
    EXPECT_TRUE(write.child(1).same_as(p));
    EXPECT_TRUE(write.child(2).same_as(q));
    for (const Term& t : {read, !read, bool_to_bv1(read), bool_to_bv1(!read),
                          write, select(a, read), store(a, read, q),
                          store(a, !p, !q)})
    {
      EXPECT_TRUE(
          tm.mk_term(t.kind(), t.children(), t.indices(), t.sort()).same_as(t));
      EXPECT_TRUE(s.parse_term(t.str()).same_as(t)) << t;
    }
    EXPECT_TRUE(read.substitute({{p, q}}).same_as(select(a, q)));
    EXPECT_TRUE(select(a, read).substitute({{read, q}}).same_as(select(a, q)));
    EXPECT_TRUE(store(a, read, read).substitute({{read, q}})
                    .same_as(store(a, q, q)));
    const Term shared = store(store(a, read, q), q, read);
    const std::string printed = shared.to_string(Format::SMTLIB2, true);
    const Term parsed = s.parse_term(printed);
    s.add(distinct(shared, parsed));
    EXPECT_TRUE(s.check_sat().is_unsat()) << printed;
    TermManager other;
    Solver replay(other);
    const std::string script = s.to_smt2(true);
    EXPECT_NE(script.find("(set-logic ALL)"), std::string::npos);
    replay.parse_smt2(script);
    EXPECT_TRUE(replay.check_sat().is_unsat()) << script;
    const Term constant = tm.mk_const_array(array, tm.mk_true());
    EXPECT_TRUE(constant.child(0).same_as(tm.mk_true()));
    EXPECT_TRUE(s.parse_term(constant.str()).same_as(constant));
    EXPECT_FALSE(array == tm.mk_array_sort(bit, bit));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, select(a, tm.mk_bv(1, 0)));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, store(a, p, tm.mk_bv(1, 1)));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH,
                     tm.mk_const_array(array, tm.mk_bv(1, 1)));
    const Term bits = tm.declare("bits", tm.mk_array_sort(bit, bit));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, select(bits, p));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, store(bits, tm.mk_bv(1, 0), q));
    API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, eq(a, bits));
  }
}

TEST(BooleanArrays, two_index_values_determine_extensional_equality)
{
  for (const char* incremental : {"off", "on"})
    for (unsigned budget : {0u, 100u})
    {
      SCOPED_TRACE(incremental);
      SCOPED_TRACE(budget);
      TermManager tm;
      Options options;
      options.set_str("incremental", incremental);
      options.set_uint("array-ackermann-budget", budget);
      options.set_bool("check-sanity", true);
      Solver s(tm, options);
      const Sort array = tm.mk_array_sort(tm.mk_bool_sort(), tm.mk_bv_sort(8));
      const Term a = tm.declare("a", array), b = tm.declare("b", array);
      s.add(eq(a[tm.mk_false()], b[tm.mk_false()]));
      s.add(eq(a[tm.mk_true()], b[tm.mk_true()]));
      s.push();
      s.add(distinct(a, b));
      EXPECT_TRUE(s.check_sat().is_unsat());
      s.pop();
      EXPECT_TRUE(s.check_sat().is_sat());
      EXPECT_TRUE(s.model().bool_value(eq(a, b)));
    }
}

TEST(BooleanArrays, models_keep_boolean_cells_indices_and_completed_values)
{
  TermManager tm;
  Solver s(tm);
  const Sort array = tm.mk_array_sort(tm.mk_bool_sort(), tm.mk_bool_sort());
  const Term a = tm.declare("a", array);
  s.add(!a[tm.mk_false()]);
  s.add(a[tm.mk_true()]);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model model = s.model();
  EXPECT_FALSE(model.bool_value(a[tm.mk_false()]));
  EXPECT_TRUE(model.bool_value(a[tm.mk_true()]));
  EXPECT_TRUE(model.bool_value(a[a[tm.mk_true()]]));
  EXPECT_EQ(model.value(bool_to_bv1(a[tm.mk_false()])).to_uint64(), 0u);
  EXPECT_EQ(model.value(bool_to_bv1(a[tm.mk_true()])).to_uint64(), 1u);
  const ArrayValue value = model.array_value(a);
  EXPECT_TRUE(value.default_value().sort() == tm.mk_bool_sort());
  EXPECT_FALSE(value.at(tm.mk_false()).to_bool());
  EXPECT_TRUE(value.at(tm.mk_true()).to_bool());
  for (const auto& entry : value.entries())
  {
    EXPECT_TRUE(entry.index.sort() == tm.mk_bool_sort());
    EXPECT_TRUE(entry.element.sort() == tm.mk_bool_sort());
  }
  const Term copy = value.as_term();
  EXPECT_TRUE(s.parse_term(copy.str()).same_as(copy));
  EXPECT_TRUE(model.bool_value(eq(copy, a)));
  Solver replay(tm);
  replay.add(distinct(copy[tm.mk_true()], tm.mk_true()));
  EXPECT_TRUE(replay.check_sat().is_unsat());

  const Term allFalse = tm.mk_const_array(array, tm.mk_false());
  const Term allTrue = tm.mk_const_array(array, tm.mk_true());
  const Term overwritten = store(store(allFalse, tm.mk_false(), tm.mk_true()),
                                 tm.mk_true(), tm.mk_true());
  EXPECT_TRUE(model.bool_value(eq(overwritten, allTrue)));
  EXPECT_FALSE(model.bool_value(eq(overwritten, allFalse)));
  EXPECT_TRUE(model.array_value(overwritten).at(tm.mk_false()).to_bool());
  EXPECT_TRUE(model.array_value(overwritten).at(tm.mk_true()).to_bool());

  s.push();
  s.add(!a[tm.mk_true()]);
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_TRUE(model.bool_value(a[tm.mk_true()]));
  s.pop();
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(BooleanArrays, boolean_components_combine_with_each_supported_scalar_sort)
{
  TermManager tm;
  const Sort boolean = tm.mk_bool_sort();
  const Sort bv = tm.mk_bv_sort(8), fp = tm.mk_fp_sort(5, 11);
  const Sort rm = tm.mk_rm_sort(), u = tm.declare_sort("U");
  unsigned id = 0;
  for (const Sort& scalar : {boolean, bv, fp, rm, u})
  {
    Solver s(tm);
    const std::string suffix = std::to_string(id++);
    const Term index = tm.declare("i" + suffix, scalar);
    const Term a = tm.declare("a" + suffix, tm.mk_array_sort(scalar, boolean));
    const Term b = tm.declare("b" + suffix, tm.mk_array_sort(boolean, scalar));
    s.add(a[index]);
    s.add(eq(b[tm.mk_false()], index));
    s.add(!select(store(a, b[tm.mk_false()], tm.mk_false()), index));
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(s.model().bool_value(a[index]));
    EXPECT_TRUE(s.model().bool_value(eq(b[tm.mk_false()], index)));
    s.add(!a[index]);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST(BooleanArrays, array_ites_and_symbolic_stores_preserve_last_write)
{
  TermManager tm;
  Solver s(tm);
  const Sort boolean = tm.mk_bool_sort();
  const Sort array = tm.mk_array_sort(boolean, boolean);
  const Term a = tm.declare("a", array), b = tm.declare("b", array);
  const Term p = tm.declare("p", boolean), q = tm.declare("q", boolean);
  const Term chosen = ite(p, a, b);
  const Term written = store(store(chosen, q, p), q, !p);
  s.add(eq(written[q], p));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

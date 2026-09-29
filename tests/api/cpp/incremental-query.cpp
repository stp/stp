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

// incremental-query.cpp -- many checks on one solver over the incremental
// driver.
//
// In 2.x a C session became incremental at its first vc_push (or with 'i'),
// the driver engaged from the second vc_query, and vc_query's negated query
// rode along as a retractable assumption. In 3.x `incremental = on` engages
// the driver from the first check, `auto` (the default) engages it for a
// solver that pushes, and entails(q) checks the assertions under the
// retractable assumption not q; check_sat() is 2.x's vc_query(false). So these
// tests answer many checks on one solver, and the answers after the first
// exercise the persistent solver.
//
// vc_createValidityChecker set 'd', so every 2.x case ran with the
// counterexample self-check on; every solver here runs with check-sanity,
// except in c_flag_alone_keeps_counterexamples, which is about the
// configuration without it.

#include "api_common.hpp"

#include <cstdint>
#include <string>

using namespace stp;

// Switching from per-level preprocessing to a whole-stack array block must
// not combine differently oriented model substitutions into a cycle (#1190).
TEST(incremental_query, whole_stack_models_do_not_replay_per_level_definitions)
{
  for (const char* incremental : {"auto", "on"})
  {
    SCOPED_TRACE(incremental);
    TermManager tm;
    Options options;
    options.set("incremental", incremental);
    options.set_bool("check-sanity", true);
    Solver s(tm, options);
    const Sort fp = tm.mk_fp_sort(3, 2);
    const Sort bv = tm.mk_bv_sort(2);
    const Term i = tm.declare("i", fp);
    const Term x = tm.declare("x", bv);
    const Term y = tm.declare("y", bv);
    const Term p = tm.declare("p", tm.mk_bool_sort());
    ASSERT_TRUE(s.check_sat().is_sat());
    const Term definition = y == ite(p, tm.mk_bv(2, 1), x);
    s.add((i == tm.mk_fp_nan(fp)) && definition);
    ASSERT_TRUE(s.check_sat().is_sat());
    s.push();
    s.add(!p);
    ASSERT_TRUE(s.check_sat().is_sat());

    const Sort array = tm.mk_array_sort(fp, bv);
    const Term different = tm.mk_const_array(array, tm.mk_bv(2, 2)) !=
        store(tm.mk_const_array(array, tm.mk_bv(2, 0)),
              tm.mk_fp_from_bits(fp, "10111"), tm.mk_bv(2, 3));
    s.add(different);
    for (int repeat = 0; repeat < 2; ++repeat)
    {
      ASSERT_TRUE(s.check_sat().is_sat());
      EXPECT_TRUE(s.model().bool_value(definition));
      EXPECT_TRUE(s.model().bool_value(different));
      EXPECT_EQ(s.model().uint64_value(x), s.model().uint64_value(y));
    }
    s.pop();
    ASSERT_TRUE(s.check_sat().is_sat()); // per-level replay is needed again
    EXPECT_TRUE(s.model().bool_value(definition));
    s.push();
    s.add(p && (x == tm.mk_bv(2, 2)) && different);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(s.model().uint64_value(x), 2u);
    EXPECT_EQ(s.model().uint64_value(y), 1u);
    s.add(y == tm.mk_bv(2, 0));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

// The classic bracket, over rounds whose verdicts alternate: retraction of
// both the pushed level and the previous query's negation must be real.
TEST(incremental_query, brackets_alternate_verdicts)
{
  TermManager tm;
  Options o;
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", true);   // 'd'
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term five = tm.mk_bv(8, 5);
  const Term six = tm.mk_bv(8, 6);

  s.add(x == five);

  // x = 5 entails x = 5: valid.
  s.push();
  EXPECT_TRUE(s.entails(x == five).is_valid());
  s.pop();

  // x = 5 refutes x = 6: invalid, with a counterexample. A stuck negated
  // query from the previous round would make the assertions unsatisfiable
  // and everything vacuously valid -- this is the retraction pin.
  s.push();
  EXPECT_TRUE(s.entails(x == six).is_invalid());
  s.pop();
  EXPECT_EQ(s.model().uint64_value(x), 5u);

  // A pushed contradiction makes anything valid, and dies with its level.
  s.push();
  s.add(x == six);
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();

  s.push();
  EXPECT_TRUE(s.check_sat().is_sat());
  s.pop();

  // the pushes engaged the driver (incremental = auto)
  EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 1u);
}

// Arrays: read congruence needs the driver's refinement loop, across several
// checks on one solver.
TEST(incremental_query, arrays_refine_across_queries)
{
  TermManager tm;
  Options o;
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", true);   // 'd'
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort arr = tm.mk_array_sort(bv8, bv8);
  const Term a = tm.declare("a", arr);
  const Term i = tm.declare("i", bv8);
  const Term j = tm.declare("j", bv8);
  const Term one = tm.mk_bv(8, 1);
  const Term two = tm.mk_bv(8, 2);

  s.add(a[i] == one);

  // a[i]=1, a[j]=2 and i=j contradict: the assertions are unsat.
  s.push();
  s.add(a[j] == two);
  s.add(i == j);
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();

  // With distinct indices the same reads are satisfiable again.
  s.push();
  s.add(a[j] == two);
  s.add(!(i == j));
  EXPECT_TRUE(s.check_sat().is_sat());
  s.pop();

  // Write shadowing, still on the same persistent solver.
  s.push();
  const Term stored = store(a, i, two);
  EXPECT_TRUE(s.entails(stored[i] == two).is_valid());
  s.pop();
}

// incremental = on ('i') engages the driver from the very first check,
// without any push in the session.
TEST(incremental_query, flag_i_without_push)
{
  TermManager tm;
  Options o;
  o.set("incremental", "on");         // 'i'
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", true);   // 'd'
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term five = tm.mk_bv(8, 5);

  s.add(bvult(x, five));

  // x < 5 (unsigned) does not entail x = 4...
  EXPECT_TRUE(s.entails(x == tm.mk_bv(8, 4)).is_invalid());
  // ...but does entail x < 6, on the same solver, one check later.
  EXPECT_TRUE(s.entails(bvult(x, tm.mk_bv(8, 6))).is_valid());
  EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 1u);
}

// Parse-time inlining of chained define-funs builds formulas tens of
// thousands of levels deep out of flat input (a 27k-define CPAchecker
// benchmark reaches depth ~25k); this loop builds the same shape directly.
// The driver's word-level passes walk such nodes by recursion, so the check
// has to run where the stack can take it -- on a default stack this check
// died of stack overflow before the solver ever saw a clause. The kinds must
// alternate: a same-kind chain is flattened wide at construction and never
// gets deep.
TEST(incremental_query, deep_alternating_chain)
{
  TermManager tm;
  Options o;
  o.set("incremental", "on");       // 'i'
  o.set_bool("check-sanity", true); // 'd'
  Solver s(tm, o);

  const Sort boolean = tm.mk_bool_sort();
  Term chain = tm.declare("x0", boolean);
  for (int i = 1; i < 120000; i++)
  {
    const Term v = tm.declare("x" + std::to_string(i), boolean);
    chain = (i % 2) ? (v || chain) : (v && chain);
  }
  s.add(chain);

  // Satisfiable -- every variable true.
  EXPECT_TRUE(s.check_sat().is_sat());
}

// CBP adoption rewrites a ctx-substituted conjunct under the engine's
// fixings, and hash-consing can REBUILD the raw inner AND the feed fixed TRUE
// -- a node the original conjunct no longer contained, so the pinning-fact
// walk asserted nothing for it and the inner conjuncts (here the definer and
// the sdiv comparison) silently left the encoding. This is murxla's shape:
// the driver on from the first check, no push, every assertion on the base
// level. The model must satisfy every raw conjunct -- before the fix it had
// x4=0, falsifying (bvsgt (bvsdiv x4 x4) x4), whose only witnesses are 0b10
// and 0b11 -- and disequalities excluding those witnesses (invisible to the
// bit-level engine) must flip the verdict rather than stay sat against the
// dropped conjunct.
TEST(incremental_query, cbp_adoption_keeps_rebuilt_fixed_node_constraint)
{
  TermManager tm;
  Options o;
  o.set("incremental", "on");         // 'i'
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", true);   // 'd'
  Solver s(tm, o);

  const Sort bv1 = tm.mk_bv_sort(1);
  const Sort bv2 = tm.mk_bv_sort(2);
  const Term x0 = tm.declare("x0", bv2);
  const Term x2 = tm.declare("x2", bv1);
  const Term x3 = tm.declare("x3", bv1);
  const Term x4 = tm.declare("x4", bv2);

  // (and (and (= x2 x3) (bvsgt (bvsdiv x4 x4) x4))
  //      (bvsle (bvlshr x0 x0) x0))
  const Term inner = (x2 == x3) && bvsgt(bvsdiv(x4, x4), x4);
  const Term outer = inner && bvsle(bvlshr(x0, x0), x0);
  s.add(outer);

  ASSERT_TRUE(s.check_sat().is_sat());

  // The model, checked against the raw conjuncts. Two-bit signed domain:
  // 0b10 = -2, 0b11 = -1.
  const Model m = s.model();
  const std::uint64_t vx0 = m.uint64_value(x0);
  const std::uint64_t vx2 = m.uint64_value(x2);
  const std::uint64_t vx3 = m.uint64_value(x3);
  const std::uint64_t vx4 = m.uint64_value(x4);
  const auto asSigned = [](std::uint64_t b) {
    return b >= 2 ? static_cast<int>(b) - 4 : static_cast<int>(b);
  };
  EXPECT_EQ(vx2, vx3);
  // SMT-LIB bvsdiv: x/x is 1 except 0/0, which is -1.
  const int sdiv = vx4 == 0 ? -1 : 1;
  EXPECT_GT(sdiv, asSigned(vx4));
  const std::uint64_t lshr = vx0 >= 2 ? 0 : (vx0 >> vx0) & 3;
  EXPECT_LE(asSigned(lshr), asSigned(vx0));

  // Only the sdiv conjunct refutes these; the bit-level engine learns
  // nothing from a disequality, so a dropped conjunct answers sat.
  const Term two = tm.mk_bv(2, 2);
  const Term three = tm.mk_bv(2, 3);
  s.add(!(x4 == two));
  s.add(!(x4 == three));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// 2.x's 'c' alone -- construct counterexamples, no self-check -- had to keep
// its counterexamples through the driver: both the batch pipeline and the
// driver used to recompute and clobber the request, so a 'c'-only pure
// bit-vector session on a release build read empty models (the self-check
// masked it by forcing the construction). In 3.x that is produce-models =
// true with check-sanity = false, the defaults, which is why this solver
// alone runs without the self-check.
TEST(incremental_query, c_flag_alone_keeps_counterexamples)
{
  TermManager tm;
  Options o;
  o.set("incremental", "on");         // 'i'
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", false);  // the configuration under test
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term five = tm.mk_bv(8, 5);

  s.add(x == five);

  // Two driver rounds, each with a readable model.
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 5u);

  const Term y = tm.declare("y", bv8);
  s.add(y == tm.mk_bv(8, 9));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(y), 9u);
  EXPECT_EQ(s.model().uint64_value(x), 5u);
  EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 1u);
}

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

// api3-push-pop-model.cpp -- a model's lifetime across push and pop, as the
// idiomatic usage (push, check, pop, then read the model) depends on it.
//
// 2.x's counterexample described the last vc_query, survived vc_pop, and was
// discarded by the next vc_push or vc_query -- deliberately unlike the SMT-LIB
// frontend, where a pop invalidates the model. In 3.x Solver::model() returns
// the model of the last check that answered sat until the next check (assert,
// push and pop do not invalidate it), and a Model already taken is a detached
// snapshot that survives the next check too. Whether the incremental driver
// engaged is read from the engine (api3_engine.hpp).

#include "api3_engine.hpp"

#include <sstream>
#include <string>

using namespace stp::api;

TEST(push_pop_model, counterexample_survives_pop_until_next_query)
{
  TermManager tm;
  Options o;
  o.set_bool("produce-models", true); // 'c'
  o.set_bool("check-sanity", true);   // 'd'
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term y = tm.declare("y", bv8);

  s.add(x == tm.mk_bv(8, 5));

  // The classic bracket: push, check, pop -- then read the model.
  s.push();
  s.add(y == tm.mk_bv(8, 7));
  ASSERT_TRUE(s.check_sat().is_sat());
  s.pop();

  // Both values are still readable after the pop.
  EXPECT_EQ(s.model().uint64_value(x), 5u);
  EXPECT_EQ(s.model().uint64_value(y), 7u);
  const Model first = s.model();

  // A new bracket replaces the model wholesale. 3.x: the push does not
  // discard it; the next check does.
  s.push();
  EXPECT_EQ(s.model().uint64_value(y), 7u);
  s.add(y == tm.mk_bv(8, 9));
  ASSERT_TRUE(s.check_sat().is_sat());
  s.pop();

  EXPECT_EQ(s.model().uint64_value(x), 5u);
  EXPECT_EQ(s.model().uint64_value(y), 9u);
  // The handle taken after the first bracket is a detached snapshot.
  EXPECT_EQ(first.uint64_value(y), 7u);

  // These two checks used the batch path. Reading their models must not
  // instantiate a persistent SAT backend as a side effect.
  EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 0u);
  EXPECT_FALSE(api3::engine_solver(s).hasIncrementalSolver());
}

// Every model reader must materialise the model the incremental driver
// answered with. 2.x's fd printer was the one exception: after a satisfiable
// solve on the driver it printed only its begin/end markers around an empty
// map. 3.x has one model printer, Model::to_smt2() (and the stream operator),
// over the snapshot Solver::model() takes.
TEST(push_pop_model, file_printer_materializes_deferred_counterexample)
{
  // 2.x built this checker around an existing engine manager
  // (vc_createValidityCheckerReuse). In 3.x a manager serves any number of
  // solvers, so the solver under test is built over a manager another solver
  // has already used.
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  Options checked;
  checked.set_bool("check-sanity", true); // 'd', as vc_createValidityChecker set it
  Solver earlier(tm, checked);
  const Term w = tm.declare("earlier_w", bv8);
  earlier.add(w == tm.mk_bv(8, 1));
  ASSERT_TRUE(earlier.check_sat().is_sat());

  // SMT-LIB's produce-models mode, the configuration under test: the model
  // must be readable, and nothing checks it. (2.x had to switch the reused
  // checker's eager counterexample check off by hand; in 3.x this is the
  // default.)
  Options o;
  o.set("incremental", "on"); // 'i'
  o.set_bool("produce-models", true);
  o.set_bool("check-sanity", false);
  Solver s(tm, o);

  const Term x = tm.declare("lazy_file_x", bv8);

  s.push();
  s.add(x == tm.mk_bv(8, 42));
  ASSERT_TRUE(s.check_sat().is_sat());
  s.pop();
  // the driver answered the check
  EXPECT_TRUE(api3::engine_solver(s).hasIncrementalSolver());

  std::ostringstream output;
  output << s.model();
  const std::string printed = output.str();
  EXPECT_EQ(printed.substr(0, 2), "(\n") << printed;
  EXPECT_NE(std::string::npos, printed.find("(define-fun lazy_file_x () (_ BitVec 8) #x2a)"))
      << printed;
  EXPECT_EQ(printed, s.model().to_smt2());

  // The earlier solver's model is its own.
  EXPECT_EQ(earlier.model().uint64_value(w), 1u);
  EXPECT_EQ(std::string::npos, earlier.model().to_smt2().find("lazy_file_x"));
}

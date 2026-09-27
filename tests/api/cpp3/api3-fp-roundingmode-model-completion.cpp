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

// api3-fp-roundingmode-model-completion.cpp -- every RoundingMode value a
// model hands back names one of the five modes.
//
// The sort is carried in five bits, one-hot, so twenty-seven of the
// thirty-two patterns name nothing. Every mode a formula names is pinned
// to the five -- by its declaration, by UF lowering, by FpTotalise at solve
// time, and by the array transform where it mints a cell -- but a pin
// belongs to the assertion level it was made at, while the incremental
// encoding keeps a symbol's SAT variables after that level is popped. The
// bits behind a mode-sorted symbol the last solve never named are therefore
// free, and the backend leaves whatever it likes in them.
//
// Publishing those bits as the symbol's value took the process down: reading
// a model lifts a RoundingMode carrier back to a mode, and a carrier that is
// not a mode has nothing to lift into.
//
//   Fatal Error: CreateRMConst requires one of the five rounding modes
//
// Such a symbol is a don't-care, and a don't-care RoundingMode has always
// been completed with RNE -- for the cell no observation covers, for the
// symbol simplified away. This is the same case and takes the same answer.

#include "api3_common.hpp"

using namespace stp;

namespace
{

// A solver on the incremental driver from its first check, which is what
// keeps a symbol's SAT variables across pops, and with the engine's
// counterexample self-check on (check-sanity), as every 2.x validity checker
// had it.
Options incremental()
{
  Options o;
  o.set("incremental", "on");
  o.set_bool("check-sanity", true);
  return o;
}

bool names_a_mode(RoundingMode m)
{
  return m == RoundingMode::RNE || m == RoundingMode::RTP || m == RoundingMode::RTN ||
         m == RoundingMode::RTZ || m == RoundingMode::RNA;
}

// The value the model of the last check gives a RoundingMode term: reading it
// must succeed, and name one of the five modes.
void expect_a_mode(const Solver& s, const Term& t)
{
  std::optional<RoundingMode> m;
  ASSERT_NO_THROW(m = s.model().rm_value(t)) << t;
  EXPECT_TRUE(names_a_mode(*m)) << t << " = " << static_cast<int>(*m);
}

} // namespace

// A rounding mode declared inside a scope, used by one check, and read back
// after a later check that never named it. The pin on it went with the popped
// level; the symbol's SAT variables did not, and the last check left them
// free. Before the fix this aborted the test binary.
TEST(fp_roundingmode_model_completion, symbol_the_last_solve_never_named)
{
  TermManager tm;
  Solver s(tm, incremental());

  const Sort rm = tm.mk_rm_sort();
  const Sort fp = tm.mk_fp64_sort();
  const Term rtn = tm.mk_rm(RoundingMode::RTN);

  s.push();

  const Term chooser = tm.declare("c", tm.mk_bool_sort());
  const Term r = tm.declare("r", rm);
  const Term mode = ite(chooser, rtn, r);

  const Term moo = tm.mk_fp_neg_inf(fp);
  const Term rti = fp_rti(r, moo);
  const Term sub = fp_sub(mode, rti, rti);

  // The check that names the mode, and the only one that does.
  s.add(fp_gt(rti, sub));
  (void)s.check_sat();

  // The model the read lands on: the level that named the mode -- and that
  // pinned it -- is gone.
  s.pop();
  ASSERT_TRUE(s.check_sat().is_sat());

  expect_a_mode(s, mode);
  expect_a_mode(s, r);
}

// The control, and it carries as much as the case above: completing a free
// carrier must not overwrite one the query decided. A fix that answered RNE
// for every RoundingMode symbol would pass the case and fail this.
TEST(fp_roundingmode_model_completion, a_decided_symbol_keeps_its_mode)
{
  TermManager tm;
  Solver s(tm, incremental());

  const Term r = tm.declare("r", tm.mk_rm_sort());
  s.add(r == tm.mk_rm(RoundingMode::RNA));

  s.push();
  ASSERT_TRUE(s.check_sat().is_sat());
  s.pop();

  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().rm_value(r), RoundingMode::RNA);
}

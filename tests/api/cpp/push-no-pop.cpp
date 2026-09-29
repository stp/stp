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

// push-no-pop.cpp -- a solver destroyed with a level still pushed, after
// an invalid and then a valid entailment. The 2.x case printed the verdicts and
// the counterexample and checked nothing; this one checks the verdicts, which
// model there is after each, and that the solver goes cleanly with its level
// still open.

#include "api_common.hpp"

#include <optional>
#include <string>
#include <string_view>

using namespace stp;

TEST(push_no_pop, one)
{
  TermManager tm;
  // 2.x set 'n', 'd' and 'p'. 'n' printed each verdict, which 3.x returns as a
  // value; 'd' is check-sanity, and 'p' is print-counterex, a printing option,
  // which writes to the solver's output sink.
  Options o;
  o.set_bool("check-sanity", true);
  o.set_bool("print-counterex", true);
  std::optional<Solver> s(std::in_place, tm, o);
  std::string printed, diagnostics;
  s->set_output_sink([&printed](std::string_view text) { printed.append(text); });
  s->set_diagnostic_sink([&diagnostics](std::string_view text) { diagnostics.append(text); });
  testing::internal::CaptureStdout();

  const Sort bv8 = tm.mk_bv_sort(8);

  const Term a = tm.declare("a", bv8);
  const Term ct_0 = tm.mk_bv(8, 0);

  const Term a_eq_0 = a == ct_0;

  // nothing constrains a: invalid, and the counterexample is the model
  const Entailment first = s->entails(a_eq_0);
  EXPECT_TRUE(first.is_invalid());
  const Model counterexample = s->model();
  EXPECT_NE(counterexample.uint64_value(a), 0u);

  const Term a_neq_0 = !a_eq_0;
  s->add(a_eq_0);
  s->push();

  const Term queryexp = a == tm.mk_bv(8, 0);

  const Entailment second = s->entails(queryexp);
  EXPECT_TRUE(second.is_valid());
  // vc_printCounterExample after a valid query: 3.x has no model after an
  // entailment holds (2.x printed an empty counterexample)
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s->model());
  // the first counterexample is a detached snapshot: it still reads
  EXPECT_FALSE(counterexample.bool_value(a_eq_0));
  EXPECT_TRUE(counterexample.bool_value(a_neq_0));

  // destroyed with the pushed level still open
  EXPECT_EQ(s->level(), 1u);
  s.reset();

  // print-counterex wrote the first entailment's counterexample to the output
  // sink, once (the second entailment held), and the library wrote nothing to
  // stdout.
  EXPECT_EQ(testing::internal::GetCapturedStdout(), "");
  const std::string prefix = "ASSERT( a = 0x";
  ASSERT_EQ(printed.rfind(prefix, 0), 0u) << printed;
  EXPECT_EQ(printed.find("ASSERT", prefix.size()), std::string::npos) << printed;
  EXPECT_EQ(std::stoul(printed.substr(prefix.size(), 2), nullptr, 16),
            counterexample.uint64_value(a))
      << printed;
  EXPECT_EQ(diagnostics, "");
}

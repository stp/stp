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

// api3-fp-printing.cpp -- the API's output half, for floating-point problems.
//
// SMT-LIB 2 is the printer that understands every sort STP has: a solver's
// state prints as a script (Solver::to_smt2), a model as its definitions
// (Model::to_smt2), a term as its text (Term::str). The CVC presentation
// language predates the floating-point theory and has no syntax for it, and
// its printer (PL_Print) treats a floating-point term as a fatal engine
// error, so the API refuses such a term or problem up front (UNSUPPORTED,
// saying why) before the printer sees it. Nothing here prints to stdout:
// every printer returns a string.

#include "api3_common.hpp"

#include <string>

using namespace stp;

namespace
{

// A 2.x checker's configuration: the counterexample self-check on (3.x's
// default is off), so every satisfiable check constructs its model and checks
// each assertion against it.
Options self_checking()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

bool contains(const std::string& haystack, const char* needle)
{
  return haystack.find(needle) != std::string::npos;
}

// The script a solver holding just `f` prints: the 3.x counterpart of
// printing one formula as a whole SMT-LIB 2 problem.
std::string smtlib2(TermManager& tm, const Term& f)
{
  Solver s(tm);
  s.add(f);
  return s.to_smt2();
}

} // namespace

// The float and the rounding mode print at their declared sorts, not as the
// bit-vectors they are carried in -- which is the whole difficulty, since
// nothing about a 5-bit constant says "rounding mode".
TEST(fp_printing, smtlib2_states_the_source_sorts)
{
  TermManager tm;

  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const Term y = tm.declare("y", tm.mk_fp_sort(8, 24));
  const Term r = tm.declare("r", tm.mk_rm_sort());
  // The predicate has to be one the manager cannot answer from the operands,
  // or the fp.add (and with it r) is gone before anything is printed:
  // fp.isNaN(x + x) folds to fp.isNaN(x), and fp.isNaN(x + y) to a question
  // about the two operands' classes. Overflow is not a property of the
  // operands, so fp.isInfinite of a sum keeps its adder. (The script declares
  // every symbol of the manager, so r's declaration is there either way; the
  // fp.add check is the one that sees the adder.)
  const Term f = fp_is_inf(fp_add(r, x, y));

  const std::string out = smtlib2(tm, f);

  // 3.x quotes a symbol in a declaration only where SMT-LIB requires it.
  EXPECT_TRUE(contains(out, "(declare-fun x () (_ FloatingPoint 8 24))")) << out;
  EXPECT_TRUE(contains(out, "(declare-fun r () RoundingMode)")) << out;
  EXPECT_TRUE(contains(out, "fp.isInfinite")) << out;
  EXPECT_TRUE(contains(out, "fp.add")) << out;
  // An FP logic, not QF_BV.
  EXPECT_TRUE(contains(out, "(set-logic QF_BVFP)") || contains(out, "(set-logic QF_FP)"))
      << out;
  // The term's own text says the same.
  EXPECT_EQ(f.str(), "(fp.isInfinite (fp.add r x y))");
}

// A model states each value at the sort it was declared with: the mode by
// name, the float in (fp ...) syntax. The presentation-language route cannot
// do either -- it has no syntax for them -- which is why this one exists.
TEST(fp_printing, smtlib2_counterexample_states_the_source_sorts)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  s.add(fp_is_nan(x));
  ASSERT_TRUE(s.check_sat().is_sat());

  // 3.x: the model prints to a string (Model::to_smt2), not to stdout.
  const std::string out = s.model().to_smt2();

  EXPECT_TRUE(contains(out, "(define-fun x () (_ FloatingPoint 8 24)")) << out;
  EXPECT_TRUE(contains(out, "(fp #b")) << out;
}

// The bit-vector-only route refuses rather than dies. 3.x: the refusal is a
// RecoverableError (UNSUPPORTED) that names what the CVC language lacks, and
// the term prints as SMT-LIB 2 as before.
TEST(fp_printing, the_bitvector_only_route_refuses)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const Term f = fp_is_nan(x);

  const auto e = API3_ERROR_OF(f.to_string(Format::CVC));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_EQ(e->function(), "Term::to_string");
  EXPECT_TRUE(contains(e->what(), "floating-point")) << e->what();

  // the same for a problem holding it
  Solver s(tm);
  s.add(f);
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s.to_string(Format::CVC));

  // and the SMT-LIB 2 route prints it
  EXPECT_EQ(f.to_string(Format::SMTLIB2, false), "(fp.isNaN x)");
  EXPECT_TRUE(contains(s.to_smt2(), "fp.isNaN"));
}

// A RoundingMode carries no format and no float need occur at all, so it is
// the case a "does this contain a float" test misses. It still cannot be
// printed by a bit-vector-only route: RoundingMode is not (_ BitVec 5), and
// printing it as one produces text that re-parses as a different problem.
TEST(fp_printing, a_rounding_mode_alone_is_still_the_fp_theory)
{
  TermManager tm;

  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term f = r == tm.mk_rm(RoundingMode::RTZ);

  EXPECT_TRUE(contains(smtlib2(tm, f), "RoundingMode"));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, f.to_string(Format::CVC));
}

// Pure bit-vector problems keep the older route, which is what makes the
// refusal above a floating-point rule rather than a general narrowing.
TEST(fp_printing, bitvector_problems_still_print_the_old_way)
{
  TermManager tm;

  const Term b = tm.declare("b", tm.mk_bv_sort(8));
  const Term f = b == tm.mk_bv(8, 1);

  const std::string out = f.to_string(Format::CVC);
  EXPECT_TRUE(contains(out, "0x01")) << out;

  // 3.x quotes a symbol in a declaration only where SMT-LIB requires it.
  EXPECT_TRUE(contains(smtlib2(tm, f), "(declare-fun b () (_ BitVec 8))"));
}

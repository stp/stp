#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdlib>
#include <string>

// The C API's *output* half, for floating-point problems.
//
// Roughly 1100 lines of floating-point constructors were added to this
// interface and none of its printing entry points. Every textual route died
// inside a printer -- PL_Print with "printing not implemented for this
// kind" -- so the one printer that understands the theory was unreachable
// from any shipping entry point.
//
// So there is now an export that understands every sort STP has, and the
// presentation-language route, which predates the theory, refuses it by name
// instead of dying inside itself. (vc_printSMTLIB, the SMT-LIB 1 route, has
// been removed along with the rest of the SMT-LIB 1 printer.)

namespace
{

std::string smtlib2(VC vc, Expr e)
{
  char* s = vc_printSMTLIB2(vc, e);
  const std::string out(s);
  free(s);
  return out;
}

bool contains(const std::string& haystack, const char* needle)
{
  return haystack.find(needle) != std::string::npos;
}

} // namespace

// The float and the rounding mode print at their declared sorts, not as the
// bit-vectors they are carried in -- which is the whole difficulty, since
// nothing about a 5-bit constant says "rounding mode".
TEST(fp_printing, smtlib2_states_the_source_sorts)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
  Expr y = vc_varExpr(vc, "y", vc_fpType(vc, 8, 24));
  Expr r = vc_varExpr(vc, "r", vc_fpRoundingModeType(vc));
  // Two DISTINCT floats: fp.isNaN(x + x) simplifies to fp.isNaN(x) at
  // construction, which would drop the fp.add (and r) this test is about.
  Expr f = vc_fpIsNaNExpr(vc, vc_fpAddExpr(vc, r, x, y));

  const std::string out = smtlib2(vc, f);

  EXPECT_TRUE(contains(out, "(declare-fun |x| () (_ FloatingPoint 8 24)"))
      << out;
  EXPECT_TRUE(contains(out, "(declare-fun |r| () RoundingMode")) << out;
  EXPECT_TRUE(contains(out, "fp.isNaN")) << out;
  EXPECT_TRUE(contains(out, "fp.add")) << out;
  // An FP logic, not QF_BV.
  EXPECT_TRUE(contains(out, "(set-logic QF_BVFP)") ||
              contains(out, "(set-logic QF_FP)"))
      << out;

  vc_Destroy(vc);
}

// A model states each value at the sort it was declared with: the mode by
// name, the float in (fp ...) syntax. The presentation-language route cannot
// do either -- it has no syntax for them -- which is why this one exists.
TEST(fp_printing, smtlib2_counterexample_states_the_source_sorts)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // invalid: a model exists

  // Printed to stdout by the interface, so capture it the way the interface
  // emits it rather than reaching past it.
  testing::internal::CaptureStdout();
  vc_printCounterExampleSMTLIB2(vc);
  const std::string out = testing::internal::GetCapturedStdout();

  EXPECT_TRUE(contains(out, "(define-fun |x| () (_ FloatingPoint 8 24)"))
      << out;
  EXPECT_TRUE(contains(out, "(fp #b")) << out;

  vc_Destroy(vc);
}

// The bit-vector-only route refuses rather than dies, and says what to use.
// A death test because a refusal here is a FatalError: the point is that the
// diagnostic names the replacement instead of naming a kind number from
// inside a printer.
TEST(fp_printing, the_bitvector_only_route_refuses)
{
  ::testing::FLAGS_gtest_death_test_style = "threadsafe";

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        vc_printExpr(vc, vc_fpIsNaNExpr(vc, x));
      },
      "vc_printSMTLIB2");
}

// A RoundingMode carries no format and no float need occur at all, so it is
// the case a "does this contain a float" test misses. It still cannot be
// printed by a bit-vector-only route: RoundingMode is not (_ BitVec 5), and
// printing it as one produces text that re-parses as a different problem.
TEST(fp_printing, a_rounding_mode_alone_is_still_the_fp_theory)
{
  VC vc = vc_createValidityChecker();

  Expr r = vc_varExpr(vc, "r", vc_fpRoundingModeType(vc));
  Expr f = vc_eqExpr(vc, r, vc_fpRoundingMode(vc, VC_RM_RTZ));

  EXPECT_TRUE(contains(smtlib2(vc, f), "RoundingMode"));

  vc_Destroy(vc);
}

// Pure bit-vector problems keep the older route, which is what makes the
// refusal above a floating-point rule rather than a general narrowing.
TEST(fp_printing, bitvector_problems_still_print_the_old_way)
{
  VC vc = vc_createValidityChecker();

  Expr b = vc_varExpr(vc, "b", vc_bvType(vc, 8));
  Expr f = vc_eqExpr(vc, b, vc_bvConstExprFromLL(vc, 8, 1));

  testing::internal::CaptureStdout();
  vc_printExpr(vc, f);
  const std::string out = testing::internal::GetCapturedStdout();
  EXPECT_TRUE(contains(out, "0x01")) << out;

  EXPECT_TRUE(contains(smtlib2(vc, f), "declare-fun |b|"));

  vc_Destroy(vc);
}

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// SMTLIB2 print-back of floating-point formulas must round-trip: what the
// printer emits contains the expected SMT-LIB spellings, re-parses in a
// fresh context, and prints again. Guards the operator name map, the indexed
// forms ((_ to_fp e s), (_ fp.to_ubv w)), rounding modes printing by name,
// float constants in (fp ...) syntax rather than #x.., and the FP-aware
// set-logic line -- the print-back path used to FatalError on any
// floating-point operator.
//
// Exact textual fixpointing is deliberately NOT demanded: symbol-set
// iteration order and the factory's commutative operand sort vary with node
// creation order, so two correct prints of one formula can order things
// differently.

#include "stp/AST/AST.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <sstream>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Ctx
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  Cpp_interface interface;

  Ctx() : snf(*(mgr.hashingNodeFactory), mgr), interface(mgr, &snf)
  {
    mgr.defaultNodeFactory = &snf;
    interface.startup();
    GlobalParserBM = &mgr;
    GlobalParserInterface = &interface;
  }

  ASTNode parse(const std::string& input)
  {
    SMT2ScanString(input.c_str());
    SMT2Parse();
    smt2lex_destroy();
    return mgr.CreateNode(AND, mgr.GetAsserts());
  }

  std::string print(const ASTNode& n)
  {
    std::ostringstream os;
    printer::SMTLIB2_PrintBack(os, n, &mgr, false);
    return os.str();
  }
};

static void roundTrips(const std::string& input,
                       const std::vector<std::string>& expected)
{
  std::string once;
  {
    Ctx a;
    once = a.print(a.parse(input));
  }
  for (const std::string& want : expected)
    EXPECT_NE(std::string::npos, once.find(want))
        << "missing '" << want << "' in:\n"
        << once;

  // The printed form must itself parse, and print again.
  Ctx b;
  const std::string twice = b.print(b.parse(once));
  EXPECT_NE(std::string::npos, twice.find("(assert "));
}

} // namespace

TEST(FPPrintBack, arithmetic_and_modes)
{
  roundTrips(R"(
    (set-logic QF_BVFP)
    (declare-fun x () (_ FloatingPoint 8 24))
    (declare-fun y () (_ FloatingPoint 8 24))
    (declare-const r RoundingMode)
    (assert (fp.lt (fp.add RNE x y) (fp.mul RTZ x y)))
    (assert (fp.leq (fp.sqrt RNA x) (fp.roundToIntegral r y)))
    (assert (fp.geq (fp.fma RTP x y y) (fp.rem x y)))
    (assert (fp.gt (fp.min x y) (fp.max x y)))
  )",
             {"(set-logic QF_BVFP)", "fp.add RNE", "fp.mul RTZ", "fp.sqrt RNA",
              "fp.roundToIntegral |r|", "fp.fma RTP", "fp.rem", "fp.min",
              "fp.max", "fp.lt", "fp.leq", "fp.geq", "fp.gt"});
}

TEST(FPPrintBack, constants_and_conversions)
{
  roundTrips(R"(
    (set-logic QF_BVFP)
    (declare-fun x () (_ FloatingPoint 5 11))
    (declare-fun b () (_ BitVec 16))
    (declare-fun w () (_ BitVec 8))
    (assert (fp.eq x (fp #b0 #b10000 #b0000000001)))
    (assert (fp.isNormal ((_ to_fp 5 11) b)))
    (assert (not (fp.isNaN ((_ to_fp 5 11) RNE x))))
    (assert (fp.isPositive ((_ to_fp_unsigned 5 11) RTN w)))
    (assert (= w ((_ fp.to_ubv 8) RTZ x)))
    (assert (= x (_ NaN 5 11)))
  )",
             {"(fp #b0 #b10000 #b0000000001)", "((_ to_fp 5 11) |b|)",
              "((_ to_fp 5 11) RNE |x|)", "((_ to_fp_unsigned 5 11) RTN |w|)",
              "((_ fp.to_ubv 8) RTZ |x|)", "fp.isNormal", "fp.isNaN",
              // The NaN special is a packed constant now.
              "(fp #b0 #b11111 #b0000000001)"});
}

TEST(FPPrintBack, specials_equality_and_classifications)
{
  roundTrips(R"(
    (set-logic QF_ABVFP)
    (declare-fun x () (_ FloatingPoint 3 5))
    (declare-fun y () (_ FloatingPoint 3 5))
    (declare-fun a () (Array (_ BitVec 4) (_ FloatingPoint 3 5)))
    (declare-fun i () (_ BitVec 4))
    (assert (= x (_ +oo 3 5)))
    (assert (fp.eq y (_ -zero 3 5)))
    (assert (or (fp.isSubnormal x) (fp.isZero y) (fp.isInfinite x)))
    (assert (or (fp.isNegative y) (fp.isPositive (select a i))))
  )",
             {"(fp #b0 #b111 #b0000)", "(fp #b1 #b000 #b0000)",
              "fp.isSubnormal", "fp.isZero", "fp.isInfinite", "fp.isNegative",
              "fp.isPositive",
              // The float-element array declares with its element sort.
              "(Array (_ BitVec 4) (_ FloatingPoint 3 5) )"});
}

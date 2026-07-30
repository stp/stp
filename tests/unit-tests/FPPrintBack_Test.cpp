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
              "fp.max", "fp.lt", "fp.leq", "fp.geq", "fp.gt",
              // The mode's declaration must name the sort, not the 5-bit
              // carrier: the operations ask for the sort, so printing the
              // carrier gives back something that no longer parses -- which
              // is what the re-parse below would then hit.
              "(declare-fun |r| () RoundingMode)"});
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
              // The NaN special is a packed constant: symfpu's canonical
              // quiet NaN, with the top stored-significand bit set.
              "(fp #b0 #b11111 #b1000000000)"});
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

// A SAT model may assign a float known only to be NaN any of the many NaN
// bit patterns; the printer spells every one of them as the canonical quiet
// NaN, so model text is deterministic at the value level (and matches what
// cvc5 and bitwuzla print). The plain-bitvector inputs matter: model values
// arrive at the printers as unstamped constants, whose bits the constant
// funnel never canonicalised.
TEST(FPPrintBack, nan_patterns_print_canonically)
{
  STPMgr mgr;

  const uint64_t patterns[] = {0x7F800001ULL,  // payload, not quiet
                               0xFFC00F00ULL,  // negative, quiet, payload
                               0x7FC00000ULL}; // already canonical
  for (const uint64_t bits : patterns)
  {
    std::ostringstream os;
    printer::outputFloatingPointSMTLIB2(mgr.CreateBVConst(32, bits), os, 8,
                                        24);
    EXPECT_EQ("(fp #b0 #b11111111 #b10000000000000000000000)", os.str());
  }

  // Infinities have the NaN exponent but a zero significand: untouched.
  std::ostringstream inf;
  printer::outputFloatingPointSMTLIB2(mgr.CreateBVConst(32, 0xFF800000ULL),
                                      inf, 8, 24);
  EXPECT_EQ("(fp #b1 #b11111111 #b00000000000000000000000)", inf.str());
}

// The format-taking overload prints exactly what the term-taking one
// prints. It exists for callers that know a value's format but hold no
// float-typed term for it -- e.g. printing the packed cells of a
// float-element array from the array symbol's format.
TEST(FPPrintBack, overload_by_format_matches_by_term)
{
  STPMgr mgr;
  const ASTNode bits = mgr.CreateBVConst(32, 0x3F800000ULL); // 1.0f packed
  const ASTNode fp = mgr.CreateFPConst(bits, 8, 24);

  std::ostringstream byTerm, byFormat;
  printer::outputFloatingPointSMTLIB2(fp, byTerm, fp);
  printer::outputFloatingPointSMTLIB2(bits, byFormat, 8, 24);

  EXPECT_EQ(byTerm.str(), byFormat.str());
  EXPECT_EQ("(fp #b0 #b01111111 #b00000000000000000000000)", byFormat.str());
}

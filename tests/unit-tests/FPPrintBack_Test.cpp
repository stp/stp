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

// Every sort a node cannot state for itself. The manager knows all of them,
// but only inside the frame that declared them -- the parser tears its frames
// down at end of file -- so by print time the printer has to read them off
// the term. Getting one wrong is not a cosmetic matter: the operations ask
// for the sort rather than the carrier's width, so the printed form stops
// parsing, which is what roundTrips' re-parse catches.
TEST(FPPrintBack, sorts_the_node_cannot_state)
{
  roundTrips(R"(
    (set-logic QF_ABVFP)
    (declare-const r RoundingMode)
    (declare-const x (_ FloatingPoint 8 24))
    (declare-const bv (_ BitVec 5))
    (declare-const modes (Array (_ BitVec 2) RoundingMode))
    (declare-const byfloat (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
    (declare-const byrm (Array RoundingMode (_ BitVec 8)))
    (declare-const floats (Array (_ BitVec 3) (_ FloatingPoint 5 11)))
    (assert (fp.isNormal (fp.add r x x)))
    (assert (fp.isNormal (fp.mul (select modes #b01) x x)))
    (assert (= (select byfloat x) #x01))
    (assert (= (select byrm r) #x02))
    (assert (fp.isNormal (select floats #b001)))
    (assert (= bv #b00011))
  )",
             {"(declare-fun |r| () RoundingMode)",
              "(declare-fun |modes| () (Array (_ BitVec 2) RoundingMode ))",
              "(declare-fun |byrm| () (Array RoundingMode (_ BitVec 8) ))",
              "(declare-fun |byfloat| () (Array (_ FloatingPoint 8 24) (_ BitVec 8) ))",
              "(declare-fun |floats| () (Array (_ BitVec 3) (_ FloatingPoint 5 11) ))",
              // Five bits wide and never used as a mode: still a bitvector.
              "(declare-fun |bv| () (_ BitVec 5))"});
}

// Which of a term's 5-bit bitvectors are rounding modes. Shape cannot answer
// it in either direction, so the printer goes by the operand position.
//
// A false positive loses a model silently: the to_fp family converts from a
// bitvector of any width, so `unsigned`/`signed` below look exactly like the
// mode beside them. Declaring one RoundingMode still re-parses -- and pins it
// to five encodings where the input allowed thirty-two.
//
// A false negative is loud: a mode reached through an ite is not itself a
// child of the operation, so `hidden` printed as (_ BitVec 5) and the printed
// form stopped parsing at "expected a rounding mode".
TEST(FPPrintBack, which_five_bit_bitvectors_are_modes)
{
  roundTrips(R"(
    (set-logic QF_ABVFP)
    (declare-const c Bool)
    (declare-const x (_ FloatingPoint 8 24))
    (declare-const hidden RoundingMode)
    (declare-const unsigned (_ BitVec 5))
    (declare-const signed (_ BitVec 5))
    (declare-const modes (Array (_ BitVec 2) RoundingMode))
    (assert (fp.isNormal (fp.div (ite c RTZ hidden) x x)))
    (assert (fp.isNormal (fp.add (ite c (select modes #b01) RTP) x x)))
    (assert (fp.isNormal ((_ to_fp_unsigned 8 24) RNE unsigned)))
    (assert (fp.isNormal ((_ to_fp 8 24) RNE signed)))
  )",
             {// Reached only through an ite, and still a mode.
              "(declare-fun |hidden| () RoundingMode)",
              // An ite over a read makes the array's elements modes.
              "(declare-fun |modes| () (Array (_ BitVec 2) RoundingMode ))",
              // Five bits, inside a floating-point operation, and not modes:
              // they are what to_fp converts *from*.
              "(declare-fun |unsigned| () (_ BitVec 5))",
              "(declare-fun |signed| () (_ BitVec 5))"});
}

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
              // The source fp.lt/fp.leq print back as their mirrors: the
              // factory rewrites them to swapped fp.gt/fp.geq at creation,
              // exactly as bvult prints back as bvugt. The re-parse below
              // still exercises the fp.lt/fp.leq parser paths.
              "fp.max", "fp.geq", "fp.gt",
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
    (declare-fun y () (_ FloatingPoint 8 24))
    (declare-fun b () (_ BitVec 16))
    (declare-fun w () (_ BitVec 8))
    (assert (fp.eq x (fp #b0 #b10000 #b0000000001)))
    (assert (fp.isNormal ((_ to_fp 5 11) b)))
    (assert (not (fp.isNaN ((_ to_fp 5 11) RNE y))))
    (assert (fp.isPositive ((_ to_fp_unsigned 5 11) RTN w)))
    (assert (= w ((_ fp.to_ubv 8) RTZ x)))
    (assert (= x (_ NaN 5 11)))
  )",
             // The rounding conversion narrows y: a widening (an identity
             // included) folds through the classification and would not
             // survive to be printed.
             {"(fp #b0 #b10000 #b0000000001)", "((_ to_fp 5 11) |b|)",
              "((_ to_fp 5 11) RNE |y|)", "((_ to_fp_unsigned 5 11) RTN |w|)",
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
    (assert (= y (_ -zero 3 5)))
    (assert (fp.eq x y))
    (assert (or (fp.isSubnormal x) (fp.isZero y) (fp.isInfinite x)))
    (assert (or (fp.isNegative y) (fp.isPositive (select a i))))
  )",
             // The equalities keep their constants: `=` is the strong one, so
             // the factory's fp.eq-against-a-constant reduction leaves it
             // alone. fp.eq between two symbols has nothing to reduce to and
             // survives for the printer to spell.
             {"(fp #b0 #b111 #b0000)", "(fp #b1 #b000 #b0000)", "fp.eq",
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

// Logic selection is a property of the expression being printed, not of all
// terms that have ever been built in its manager. The C-API test below this
// suite covers the popped-scope case; an entirely unused float is the smaller
// direct regression for the printer's manager-history leak.
TEST(FPPrintBack, logic_selection_is_expression_local)
{
  STPMgr mgr;
  (void)mgr.CreateSourceSymbol("unused_fp",
                               SourceSort::floatingPoint(5, 11));
  const ASTNode live =
      mgr.CreateSourceSymbol("live", SourceSort::bitVector(8));
  const ASTNode formula =
      mgr.CreateNode(EQ, live, mgr.CreateBVConst(8, 0x2a));

  ASSERT_TRUE(mgr.has_floating_point); // the conservative hint is sticky
  EXPECT_FALSE(containsFloatingPoint(formula, &mgr));
  EXPECT_FALSE(containsFloatingPointTheory(formula, &mgr));

  std::ostringstream os;
  printer::SMTLIB2_PrintBack(os, formula, &mgr, false);
  const std::string printed = os.str();
  EXPECT_EQ(0U, printed.find("(set-logic QF_BV)\n")) << printed;
  EXPECT_EQ(std::string::npos, printed.find("FloatingPoint")) << printed;
}

// RoundingMode by itself still belongs to the floating-point theory. It does
// not need FP arithmetic lowering, but its declaration cannot be printed
// under a bitvector-only logic.
TEST(FPPrintBack, rounding_mode_only_selects_fp_logic)
{
  roundTrips(R"(
    (set-logic QF_BVFP)
    (declare-const r RoundingMode)
    (assert (= r RNE))
  )",
             {"(set-logic QF_BVFP)",
              "(declare-fun |r| () RoundingMode)", "(= |r| RNE)"});
}

// Declared sorts are represented by finite bit-vector carriers internally,
// but print-back must expose the source sorts and select QF_AX. Otherwise a
// printed formula silently becomes an array-of-bitvectors problem.
TEST(FPPrintBack, qf_ax_declared_array_sorts_round_trip)
{
  roundTrips(R"(
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-const a (Array Index Element))
    (declare-const b (Array Index Element))
    (declare-const i Index)
    (declare-const e Element)
    (assert (= (select a i) e))
    (assert (not (= a b)))
  )",
             {"(set-logic QF_AX)",
              "(declare-sort Index 0)",
              "(declare-sort Element 0)",
              "(declare-fun |a| () (Array Index Element))",
              "(declare-fun |i| () Index)",
              "(declare-fun |e| () Element)"});
}

// A term is a DAG, and rounding-mode ites share their operands freely.
//
// The walk that decides which 5-bit bitvectors are modes has to descend into
// both arms of an ite, because a mode reached through one is not itself a
// child of the operation (see which_five_bit_bitvectors_are_modes). Doing
// that without a visited set turns "descend into both arms" into "enumerate
// every root-to-leaf path" -- and the two are wildly different numbers on a
// DAG, for a walk whose whole job is to insert into a set and which therefore
// cannot learn anything from a second visit.
//
// The two enclosing passes each carry a visited set; this one did not, and
// could not simply borrow theirs: the enclosing walk reaches a mode operand as
// an ordinary child as well, so one shared set would let whichever arrived
// first suppress the other.
//
// The shape below is the standard exponential-path DAG -- two distinct modes
// per level, each built from both modes of the level beneath -- so depth d is
// 2d nodes and 2^d paths. Note that the arms must differ: (ite c m m) is folded
// to m by the simplifying factory, which quietly collapses the whole structure
// and makes this test prove nothing.
//
// This does not measure time. At depth 40 the unfixed walk does not finish, so
// the assertion is that print-back returns at all. The `let` bindings keep the
// input linear too, and the printer letizes shared subterms on the way out, so
// nothing else here is exponential.
TEST(FPPrintBack, mode_ite_dag_is_walked_once)
{
  const int depth = 40;

  std::string input = "(set-logic QF_FP)\n"
                      "(declare-const r1 RoundingMode)\n"
                      "(declare-const r2 RoundingMode)\n"
                      "(declare-const x (_ FloatingPoint 8 24))\n";
  for (int k = 1; k <= depth; k++)
    input += "(declare-const p" + std::to_string(k) + " Bool)\n" +
             "(declare-const q" + std::to_string(k) + " Bool)\n";

  std::string opens, closes;
  for (int k = 1; k <= depth; k++)
  {
    const std::string a = (k == 1) ? "r1" : ("a" + std::to_string(k - 1));
    const std::string b = (k == 1) ? "r2" : ("b" + std::to_string(k - 1));
    const std::string k_s = std::to_string(k);
    opens += "(let ((a" + k_s + " (ite p" + k_s + " " + a + " " + b + "))) ";
    opens += "(let ((b" + k_s + " (ite q" + k_s + " " + a + " " + b + "))) ";
    closes += "))";
  }

  input += "(assert " + opens + "(fp.isNormal (fp.add a" +
           std::to_string(depth) + " x x))" + closes + ")\n";

  Ctx ctx;
  const std::string printed = ctx.print(ctx.parse(input));

  // Both leaves are still recognised as modes: the visited set must not cost
  // the answer the walk exists to produce.
  EXPECT_NE(std::string::npos,
            printed.find("(declare-fun |r1| () RoundingMode)"))
      << printed.substr(0, 600);
  EXPECT_NE(std::string::npos,
            printed.find("(declare-fun |r2| () RoundingMode)"))
      << printed.substr(0, 600);
}

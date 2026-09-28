/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

// The floating-point abstraction (--fp-abstraction): plumbing, the
// refinement loop end to end, and the rule catalogue against STP's own
// exact semantics.

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpAbstraction.h"
#include "stp/FloatBlaster/FpAbstractionRules.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATAIG.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstring>
#include <limits>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

ASTNode fpConst(STPMgr& mgr, unsigned eb, unsigned sb, uint64_t bits)
{
  return mgr.CreateFPConst(mgr.CreateBVConst(eb + sb, bits), eb, sb);
}

ASTNode rmConst(STPMgr& mgr, unsigned mode)
{
  return mgr.CreateRMConst(mode);
}

ASTNode conj(STPMgr& mgr, const std::vector<ASTNode>& xs)
{
  ASTNode out = mgr.ASTTrue;
  for (const ASTNode& x : xs)
    out = mgr.CreateNode(AND, out, x);
  return out;
}

bool containsTerm(const ASTNode& root, const ASTNode& term)
{
  ASTNodeSet seen;
  ASTVec todo{root};
  while (!todo.empty())
  {
    const ASTNode n = todo.back();
    todo.pop_back();
    if (n == term)
      return true;
    if (seen.insert(n).second)
      todo.insert(todo.end(), n.begin(), n.end());
  }
  return false;
}

SOLVER_RETURN_TYPE solve(STPMgr& mgr, const ASTNode& formula, bool abstracted,
                         FpAbstractionStatistics* stats = NULL)
{
  mgr.UserFlags.fp_abstraction = abstracted;
  mgr.UserFlags.fp_abstraction_width = 4;
  STP solver(&mgr);
  const SOLVER_RETURN_TYPE result = solver.TopLevelSTP(formula, mgr.ASTFalse);
  if (stats != NULL && abstracted && mgr.getFpAbstractionIfAny() != NULL)
    *stats = mgr.getFpAbstractionIfAny()->statistics();
  return result;
}

// Both pipelines on the same formula must agree; a satisfiable answer is
// model-checked by the solve itself (check_counterexample).
void expectParity(STPMgr& mgr, const ASTNode& formula,
                  SOLVER_RETURN_TYPE expected)
{
  mgr.UserFlags.check_counterexample_flag = true;
  EXPECT_EQ(expected, solve(mgr, formula, false));
  EXPECT_EQ(expected, solve(mgr, formula, true));
}

} // namespace

TEST(FpAbstraction, parses_operation_lists)
{
  unsigned mask = 0;
  EXPECT_TRUE(parseFpAbstractionOps("mul,div,sqrt,fma", mask));
  EXPECT_EQ(FP_ABSTRACT_DEFAULT, mask);
  EXPECT_TRUE(parseFpAbstractionOps("mul,div,sqrt", mask));
  EXPECT_EQ(FP_ABSTRACT_MUL | FP_ABSTRACT_DIV | FP_ABSTRACT_SQRT, mask);
  EXPECT_TRUE(parseFpAbstractionOps("default", mask));
  EXPECT_EQ(FP_ABSTRACT_DEFAULT, mask);
  EXPECT_TRUE(parseFpAbstractionOps(" add , fma ", mask));
  EXPECT_EQ(FP_ABSTRACT_ADD | FP_ABSTRACT_FMA, mask);
  EXPECT_TRUE(parseFpAbstractionOps("all", mask));
  EXPECT_EQ(1023u, mask);
  EXPECT_TRUE(parseFpAbstractionOps("rti", mask));
  EXPECT_EQ(FP_ABSTRACT_RTI, mask);
  EXPECT_TRUE(parseFpAbstractionOps("to_sbv,to_ubv", mask));
  EXPECT_EQ(FP_ABSTRACT_TO_SBV | FP_ABSTRACT_TO_UBV, mask);
  EXPECT_TRUE(parseFpAbstractionOps("none", mask));
  EXPECT_EQ(0u, mask);
  mask = 7;
  EXPECT_FALSE(parseFpAbstractionOps("mul,nope", mask));
  EXPECT_EQ(7u, mask);
}

// --fp-abstraction-constant-operands decides whether a product with a
// constant float operand is a record. Declined, it is lowered exactly: the
// constant's circuit is small and propagates, where a record puts a free
// result under rules the solver has to search. The symbolic product beside
// it is abstracted either way, and the query here holds one, so the
// automatic policy abstracts both.
TEST(FpAbstraction, constant_operand_products_follow_the_knob)
{
  typedef UserDefinedFlags::FpConstantOperandMode Mode;
  const Mode modes[] = {Mode::ON, Mode::OFF, Mode::AUTO};
  for (const Mode mode : modes)
  {
    const bool admit = mode != Mode::OFF;
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_width = 4;
    mgr.UserFlags.fp_abstraction_constant_operands = mode;
    const SourceSort format = SourceSort::floatingPoint(5, 11);
    const ASTNode x = mgr.CreateSourceSymbol("c_x", format);
    const ASTNode y = mgr.CreateSourceSymbol("c_y", format);
    const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode three = fpConst(mgr, 5, 11, 0x4200);
    const ASTNode byConst = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, three, x});
    const ASTNode symbolic = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, x, y});
    const ASTNode formula =
        conj(mgr, {mgr.CreateNode(FP_LT, byConst, symbolic),
                   mgr.CreateNode(FP_ISNORMAL, x), mgr.CreateNode(FP_ISNORMAL, y)});

    FpAbstraction abstraction(&mgr);
    abstraction.abstract(formula);
    ASSERT_TRUE(abstraction.active());
    EXPECT_EQ(admit ? 2u : 1u, abstraction.applications().size());
    bool sawConstantOperand = false;
    for (const std::unique_ptr<FpAbstraction::Application>& app :
         abstraction.applications())
      for (const ASTNode& proxy : app->proxies)
        if (proxy.isConstant() && proxy != app->proxies[0])
          sawConstantOperand = true;
    EXPECT_EQ(admit, sawConstantOperand);
  }
}

// The automatic policy reads the query: this one is linear over its
// coefficients -- every product is one constant times one variable,
// standing alone, so nothing the configuration abstracts has two operands
// it does not know and no record's operand is another record's result --
// and the products are left to their pruned shift-and-add circuits, no
// record being made. Asking for them explicitly still makes them.
TEST(FpAbstraction, constant_operand_policy_reads_the_query)
{
  typedef UserDefinedFlags::FpConstantOperandMode Mode;
  const Mode modes[] = {Mode::AUTO, Mode::ON};
  for (const Mode mode : modes)
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_width = 4;
    mgr.UserFlags.fp_abstraction_constant_operands = mode;
    const SourceSort format = SourceSort::floatingPoint(5, 11);
    const ASTNode x = mgr.CreateSourceSymbol("l_x", format);
    const ASTNode y = mgr.CreateSourceSymbol("l_y", format);
    const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode three = fpConst(mgr, 5, 11, 0x4200);
    const ASTNode two = fpConst(mgr, 5, 11, 0x4000);
    const ASTNode formula = conj(
        mgr, {mgr.CreateNode(FP_LT, mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, three, x}),
                             mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, two, y})),
              mgr.CreateNode(FP_ISNORMAL, x), mgr.CreateNode(FP_ISNORMAL, y)});

    FpAbstraction abstraction(&mgr);
    abstraction.abstract(formula);
    EXPECT_EQ(mode == Mode::ON ? 2u : 0u, abstraction.applications().size());
    EXPECT_EQ(mode == Mode::ON, abstraction.active());
  }
}

TEST(FpAbstraction, shared_and_commuted_applications_share_one_record)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  mgr.UserFlags.fp_abstraction_width = 4;
  const SourceSort format = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("s_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("s_y", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode xy = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, x, y});
  const ASTNode yx = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, y, x});
  const ASTNode one = fpConst(mgr, 5, 11, 0x3c00);
  const ASTNode formula = conj(
      mgr, {mgr.CreateNode(FP_LEQ, xy, one), mgr.CreateNode(FP_LEQ, one, yx),
            mgr.CreateNode(FP_ISNORMAL, x)});

  FpAbstraction abstraction(&mgr);
  const ASTNode abstracted = abstraction.abstract(formula);
  ASSERT_TRUE(abstraction.active());
  EXPECT_NE(formula, abstracted);
  EXPECT_EQ(1u, abstraction.applications().size());
  const FpAbstraction::Application& app = *abstraction.applications()[0];
  EXPECT_EQ(FP_MUL, app.kind);
  EXPECT_EQ(3u, app.proxies.size());
  EXPECT_TRUE(app.proxies[0].isConstant()); // the mode
  EXPECT_EQ(SYMBOL, app.proxies[1].GetKind());
  EXPECT_EQ(SYMBOL, app.proxies[2].GetKind());
  EXPECT_EQ(SYMBOL, app.surrogate.GetKind());
  EXPECT_EQ(16u, app.surrogate.GetValueWidth());
  EXPECT_EQ(format, app.surrogateView.GetSourceSort());
  EXPECT_TRUE(abstraction.isProtected(app.surrogate));
  EXPECT_TRUE(abstraction.isProtected(app.proxies[1]));
  EXPECT_FALSE(abstraction.isProtected(x));
  EXPECT_EQ(2u, abstraction.statistics().candidates);
  EXPECT_EQ(1u, abstraction.statistics().shared);
  EXPECT_GT(abstraction.statistics().ruleLemmas, 10u);

  // Disabled by default: an untouched manager abstracts nothing.
  STPMgr plain;
  EXPECT_FALSE(plain.UserFlags.fp_abstraction);
}

TEST(FpAbstraction, no_overflow_is_proved_without_the_multiplier)
{
  STPMgr mgr;
  const SourceSort format = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("o_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("o_y", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode t = mgr.CreateTerm(FP_MUL, 32, ASTVec{rne, x, y});
  const ASTNode eight = fpConst(mgr, 8, 24, 0x41000000);
  const ASTNode formula = conj(
      mgr, {mgr.CreateNode(FP_LEQ, mgr.CreateTerm(FP_ABS, 32, x), eight),
            mgr.CreateNode(FP_LEQ, mgr.CreateTerm(FP_ABS, 32, y), eight),
            mgr.CreateNode(OR, mgr.CreateNode(FP_ISINFINITE, t),
                           mgr.CreateNode(FP_ISNAN, t))});
  FpAbstractionStatistics stats;
  EXPECT_EQ(SOLVER_VALID, solve(mgr, formula, true, &stats));
  EXPECT_EQ(1u, stats.abstracted);
  EXPECT_EQ(0u, stats.releases);
  EXPECT_EQ(0u, stats.valueLemmas);
  EXPECT_EQ(SOLVER_VALID, solve(mgr, formula, false));
}

TEST(FpAbstraction, exact_witness_reaches_release_and_agrees)
{
  STPMgr mgr;
  const SourceSort format = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("w_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("w_y", format);
  const ASTNode z = mgr.CreateSourceSymbol("w_z", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode inner = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, x, y});
  const ASTNode outer = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, inner, z});
  const ASTNode pi = fpConst(mgr, 5, 11, 0x4248);
  const ASTNode formula = conj(
      mgr, {mgr.CreateNode(FP_ISNORMAL, x), mgr.CreateNode(FP_ISNORMAL, y),
            mgr.CreateNode(FP_ISNORMAL, z), mgr.CreateNode(FP_SMT_EQ, outer, pi),
            mgr.CreateNode(FP_LT, x, y)});
  mgr.UserFlags.check_counterexample_flag = true;
  // How many rounds this takes depends on the candidates the SAT solver
  // offers -- with the significand bands the first is usually exact, and
  // a refuted one may be repaired -- so what is checked is the answer,
  // model-checked, and that both products were abstracted. The release
  // path itself is forced in wide_release_restarts_the_pipeline.
  FpAbstractionStatistics stats;
  EXPECT_EQ(SOLVER_INVALID, solve(mgr, formula, true, &stats));
  EXPECT_EQ(2u, stats.abstracted);
  EXPECT_EQ(SOLVER_INVALID, solve(mgr, formula, false));
  mgr.UserFlags.fp_abstraction_significand_bits = 0;
  EXPECT_EQ(SOLVER_INVALID, solve(mgr, formula, true, &stats));
  EXPECT_EQ(2u, stats.abstracted);
  mgr.UserFlags.fp_abstraction_significand_bits = 8;
}

TEST(FpAbstraction, parity_on_a_battery_of_shapes)
{
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_TOWARD_ZERO,
                            symbolic_fp::ROUND_TOWARD_POSITIVE};
  for (unsigned mode : modes)
  {
    STPMgr mgr;
    const SourceSort format = SourceSort::floatingPoint(3, 4);
    const ASTNode x = mgr.CreateSourceSymbol("b_x", format);
    const ASTNode y = mgr.CreateSourceSymbol("b_y", format);
    const ASTNode rm = rmConst(mgr, mode);
    const ASTNode mul = mgr.CreateTerm(FP_MUL, 7, ASTVec{rm, x, y});
    const ASTNode div = mgr.CreateTerm(FP_DIV, 7, ASTVec{rm, x, y});
    const ASTNode sqrt = mgr.CreateTerm(FP_SQRT, 7, ASTVec{rm, x});
    const ASTNode one = fpConst(mgr, 3, 4, 0x18);
    const ASTNode two = fpConst(mgr, 3, 4, 0x20);
    const ASTNode pzero = fpConst(mgr, 3, 4, 0x00);
    const ASTNode nzero = fpConst(mgr, 3, 4, 0x40);
    // Exact zero product from two nonzero normals is impossible in (3,4):
    // the smallest product of two minimum normals is far above the
    // smallest subnormal there. UNSAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                            mgr.CreateNode(FP_ISNORMAL, y),
                            mgr.CreateNode(FP_ISZERO, mul)}),
                 SOLVER_VALID);
    // x / x = 1 for finite nonzero x. UNSAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                            mgr.CreateNode(NOT,
                                           mgr.CreateNode(
                                               FP_SMT_EQ,
                                               mgr.CreateTerm(FP_DIV, 7,
                                                              ASTVec{rm, x, x}),
                                               one))}),
                 SOLVER_VALID);
    // sqrt above 1 is at most its argument. UNSAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_LEQ, one, x),
                            mgr.CreateNode(FP_LT, x, sqrt)}),
                 SOLVER_VALID);
    // A product equal to two with normal operands exists. SAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                            mgr.CreateNode(FP_ISNORMAL, y),
                            mgr.CreateNode(FP_SMT_EQ, mul, two)}),
                 SOLVER_INVALID);
    // Signed zero: -0 * y with y positive finite is -0, never +0. UNSAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_SMT_EQ, x, nzero),
                            mgr.CreateNode(FP_ISNORMAL, y),
                            mgr.CreateNode(FP_ISPOSITIVE, y),
                            mgr.CreateNode(FP_SMT_EQ, mul, pzero)}),
                 SOLVER_VALID);
    // Division by zero of a nonzero finite is infinite. UNSAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                            mgr.CreateNode(FP_ISZERO, y),
                            mgr.CreateNode(NOT,
                                           mgr.CreateNode(FP_ISINFINITE, div))}),
                 SOLVER_VALID);
    // NaN through a symbolic-looking operand chain. SAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_ISNAN, mul),
                            mgr.CreateNode(NOT, mgr.CreateNode(FP_ISNAN, x)),
                            mgr.CreateNode(NOT, mgr.CreateNode(FP_ISNAN, y))}),
                 SOLVER_INVALID);
    // Rounding to an integer keeps a magnitude of at least one at least
    // one, in any mode. UNSAT.
    mgr.UserFlags.fp_abstraction_ops = FP_ABSTRACT_DEFAULT | FP_ABSTRACT_RTI;
    const ASTNode rti = mgr.CreateTerm(FP_ROUNDTOINTEGRAL, 7, ASTVec{rm, x});
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_LEQ, one, mgr.CreateTerm(FP_ABS, 7, x)),
                            mgr.CreateNode(FP_LT, mgr.CreateTerm(FP_ABS, 7, rti), one)}),
                 SOLVER_VALID);
    // A rounding that moved: two is the integer of something that is not
    // two. SAT.
    expectParity(mgr,
                 conj(mgr, {mgr.CreateNode(FP_SMT_EQ, rti, two),
                            mgr.CreateNode(NOT, mgr.CreateNode(FP_SMT_EQ, x, two))}),
                 SOLVER_INVALID);
    mgr.UserFlags.fp_abstraction_ops = FP_ABSTRACT_DEFAULT;
  }
}

TEST(FpAbstraction, symbolic_rounding_mode)
{
  STPMgr mgr;
  const SourceSort format = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("r_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("r_y", format);
  const ASTNode rm = mgr.CreateSourceSymbol("r_rm", SourceSort::roundingMode());
  const ASTNode t = mgr.CreateTerm(FP_MUL, 32, ASTVec{rm, x, y});
  const ASTNode one = fpConst(mgr, 8, 24, 0x3f800000);
  // |y| > 1 -> |x*y| >= |x|, in every mode. UNSAT.
  expectParity(mgr,
               conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                          mgr.CreateNode(FP_ISNORMAL, y),
                          mgr.CreateNode(FP_LT, one, y),
                          mgr.CreateNode(
                              NOT, mgr.CreateNode(
                                       FP_GEQ, mgr.CreateTerm(FP_ABS, 32, t),
                                       mgr.CreateTerm(FP_ABS, 32, x)))}),
               SOLVER_VALID);
  // Under some mode the product of two chosen normals rounds to a chosen
  // constant. SAT.
  expectParity(mgr,
               conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                          mgr.CreateNode(FP_ISNORMAL, y),
                          mgr.CreateNode(FP_SMT_EQ, t,
                                         fpConst(mgr, 8, 24, 0x40490fdb))}),
               SOLVER_INVALID);
}

namespace
{
void rememberRuleIds(const std::vector<FpRuleId>& ids,
                     const std::vector<ASTNode>& rules,
                     std::set<FpRuleId>& seen)
{
  ASSERT_EQ(rules.size(), ids.size());
  for (FpRuleId id : ids)
  {
    ASSERT_NE(FpRuleId::None, id);
    ASSERT_NE(FpRuleId::Count, id);
    seen.insert(id);
  }
}

// A passing validity test must actually encounter each schema assigned to
// its verification group. Merely adding an ID to the catalogue is not coverage.
void expectRuleCoverage(const std::set<FpRuleId>& seen, const char* group)
{
  for (unsigned i = 1; i < static_cast<unsigned>(FpRuleId::Count); ++i)
  {
    const auto id = static_cast<FpRuleId>(i);
    const auto& info = fpRuleInfo(id);
    if (std::strcmp(info.verification, group) == 0)
    {
      EXPECT_NE(seen.end(), seen.find(id))
          << info.name << " was never checked by verification group " << group;
    }
  }
}
} // namespace

// Every emitted rule, against the exact operation, over every value of a
// tiny format: exact ∧ ¬rule must be unsatisfiable. This is the C++
// catalogue checked by the solver's own semantics.
namespace
{

// A rule context over fresh bit-vector symbols for an application of `kind`
// at (eb, sb): the operands and the result are packed views of symbols, so
// the rules emitted are exactly those the solver emits over its proxies and
// surrogate. `exact` receives the definition t = op(x, ...).
struct RuleFixture
{
  std::vector<ASTNode> symbols; // the operand bit symbols, then the result's
  FpRuleContext context;
  ASTNode definition;

  RuleFixture(STPMgr& mgr, Kind kind, unsigned eb, unsigned sb, unsigned mode,
              const std::string& tag)
  {
    const unsigned width = eb + sb;
    const bool hasMode = kind != FP_REM;
    const unsigned arity =
        (kind == FP_SQRT || kind == FP_ROUNDTOINTEGRAL) ? 1
        : kind == FP_FMA                                 ? 3
                                                         : 2;
    const auto view = [&](const ASTNode& b) {
      return FloatBlaster::withFormat(
          &mgr,
          mgr.CreateTerm(FP_TOFP, width, mgr.CreateBVConst(32, eb),
                         mgr.CreateBVConst(32, sb), b),
          eb, sb);
    };
    context.bm = &mgr;
    context.kind = kind;
    context.eb = eb;
    context.sb = sb;
    context.rm = hasMode ? mode : 0;
    ASTVec operation;
    if (hasMode)
    {
      context.rmTerm = mode != 0
                           ? rmConst(mgr, mode)
                           : mgr.CreateSourceSymbol((tag + "_rm").c_str(),
                                                    SourceSort::roundingMode());
      operation.push_back(context.rmTerm);
    }
    for (unsigned i = 0; i < arity; ++i)
    {
      const ASTNode b = mgr.CreateSourceSymbol(
          (tag + "_x" + std::to_string(i)).c_str(),
          SourceSort::bitVector(width));
      symbols.push_back(b);
      context.bits.push_back(b);
      context.view.push_back(view(b));
      operation.push_back(context.view.back());
    }
    const ASTNode tb = mgr.CreateSourceSymbol((tag + "_t").c_str(),
                                              SourceSort::bitVector(width));
    symbols.push_back(tb);
    context.tb = tb;
    context.t = view(tb);
    definition = mgr.CreateNode(FP_SMT_EQ, context.t,
                                mgr.CreateTerm(kind, width, operation));
  }
};

// Select by stable ID, joining symmetric instances when the emitter has two.
ASTNode emittedRule(const FpRuleContext& context, FpRuleId wanted,
                    unsigned tier = 3, bool allowOmitted = false)
{
  std::vector<ASTNode> rules, selected;
  std::vector<FpRuleId> ids;
  emitFpAbstractionRules(context, tier, rules, &ids);
  for (size_t i = 0; i < ids.size(); ++i)
    if (ids[i] == wanted)
      selected.push_back(rules[i]);
  if (!allowOmitted)
  {
    EXPECT_FALSE(selected.empty()) << fpRuleName(wanted);
  }
  // A statically disabled row can be omitted as a true implication.
  return conj(*context.bm, selected);
}

ASTNode ruleInstance(const FpRuleContext& context, const ASTNode& rule,
                     const std::vector<ASTNode>& operands,
                     const ASTNode& result, unsigned mode = 0,
                     const ASTNode& undef = ASTNode())
{
  ASTNodeMap bindings, cache;
  for (size_t i = 0; i < operands.size(); ++i)
    bindings[context.bits[i]] = operands[i];
  bindings[context.tb] = result;
  if (mode != 0)
    bindings[context.rmTerm] = rmConst(*context.bm, mode);
  if (!undef.IsNull())
    bindings[context.undefBits] = undef;
  const ASTNode instance = SubstitutionMap::replace(
      rule, bindings, cache, context.bm->defaultNodeFactory, false, false);
  return NonMemberBVConstEvaluator(context.bm, instance);
}

void expectExactRule(const FpRuleContext& context, const ASTNode& definition,
                     const ASTNode& rule)
{
  STPMgr& mgr = *context.bm;
  mgr.UserFlags.fp_abstraction = false;
  ASTNode validMode = mgr.ASTTrue;
  if (context.rm == 0 && !context.rmTerm.IsNull())
  {
    validMode = mgr.ASTFalse;
    for (unsigned mode : {1u, 2u, 4u, 8u, 16u})
      validMode = mgr.CreateNode(
          OR, validMode,
          mgr.CreateNode(EQ, context.rmTerm, rmConst(mgr, mode)));
  }
  STP solver(&mgr);
  EXPECT_EQ(SOLVER_VALID,
            solver.TopLevelSTP(
                conj(mgr, {validMode, definition, mgr.CreateNode(NOT, rule)}),
                mgr.ASTFalse));
}

} // namespace

TEST(FpAbstraction, revised_sqrt_b2_even_bound_is_equivalent)
{
  for (const auto& format :
       {std::make_pair(2u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned mode : {1u, 2u, 4u, 8u, 16u})
    {
      const unsigned eb = format.first, p = format.second, width = eb + p;
      const int64_t emin = 2 - (int64_t(1) << (eb - 1));
      STPMgr mgr;
      RuleFixture f(mgr, FP_SQRT, eb, p, mode, "b2");
      const ASTNode rule = emittedRule(f.context, FpRuleId::SQRT_B2, 2);
      expectExactRule(f.context, f.definition, rule);
      const uint64_t submax = (uint64_t(1) << (p - 1)) - 1;
      for (uint64_t xb : {uint64_t(0), uint64_t(1), submax, submax + 1,
                          submax | (uint64_t(1) << (width - 1))})
      {
        const ASTNode x = mgr.CreateBVConst(width, xb);
        const bool sub =
            decodeFpPackedValue(x, eb, p).cls == FpPackedValue::Subnormal;
        for (uint64_t tb = 0; tb < (uint64_t(1) << width); ++tb)
        {
          const ASTNode t = mgr.CreateBVConst(width, tb);
          const auto tv = decodeFpPackedValue(t, eb, p);
          EXPECT_EQ(2 * tv.e <= emin + 1, 2 * tv.e <= emin);
          const bool old =
              !sub || tv.cls != FpPackedValue::Normal || 2 * tv.e <= emin + 1;
          EXPECT_EQ(old ? mgr.ASTTrue : mgr.ASTFalse,
                    ruleInstance(f.context, rule, {x}, t));
        }
      }
    }
}

TEST(FpAbstraction, revised_sqrt_s8_preserves_normal_root_coverage)
{
  for (const auto& format :
       {std::make_pair(2u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned mode : {1u, 2u, 4u, 8u, 16u})
    {
      const unsigned eb = format.first, p = format.second, width = eb + p;
      const int64_t emin = 2 - (int64_t(1) << (eb - 1));
      STPMgr mgr;
      RuleFixture f(mgr, FP_SQRT, eb, p, mode, "s8");
      const ASTNode rule = emittedRule(f.context, FpRuleId::SQRT_S8, 0);
      expectExactRule(f.context, f.definition, rule);
      // Exhaust input classes, signs and exponents. Test each output class
      // against the old implication, including the format where S7 is absent.
      for (uint64_t xb = 0; xb < (uint64_t(1) << width); ++xb)
      {
        const ASTNode x = mgr.CreateBVConst(width, xb);
        const auto xv = decodeFpPackedValue(x, eb, p);
        const bool normalPositive =
            xv.cls == FpPackedValue::Normal && !xv.negative;
        const bool oldGuard = normalPositive && xv.e >= 2 * emin;
        EXPECT_EQ(normalPositive, oldGuard);
        for (uint64_t tb : {uint64_t(0), uint64_t(1), uint64_t(1) << (p - 1),
                            ((uint64_t(1) << eb) - 1) << (p - 1),
                            (((uint64_t(1) << eb) - 1) << (p - 1)) | 1})
        {
          const ASTNode t = mgr.CreateBVConst(width, tb);
          const bool normalResult =
              decodeFpPackedValue(t, eb, p).cls == FpPackedValue::Normal;
          EXPECT_EQ((!oldGuard || normalResult) ? mgr.ASTTrue : mgr.ASTFalse,
                    ruleInstance(f.context, rule, {x}, t));
        }
      }
    }
}

// Every emitted rule, against the exact operation, over every value of a
// tiny format: exact ∧ ¬rule must be unsatisfiable. This is the C++
// catalogue checked by the solver's own semantics.
TEST(FpAbstraction, revised_sqrt_b1_distinguishes_upward_rounding)
{
  for (const auto& format :
       {std::make_pair(2u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
    {
      const unsigned eb = format.first, p = format.second, width = eb + p;
      const int64_t bias = (int64_t(1) << (eb - 1)) - 1;
      STPMgr mgr;
      RuleFixture f(mgr, FP_SQRT, eb, p, mode, "b1");
      const ASTNode rule = emittedRule(f.context, FpRuleId::SQRT_B1, 2);
      expectExactRule(f.context, f.definition, rule);
      for (int64_t ex = 1 - bias; ex <= bias; ++ex)
      {
        const int64_t n = ex >= 0 ? ex / 2 : (ex - 1) / 2;
        const uint64_t bits =
            (uint64_t(ex + bias) << (p - 1)) | ((uint64_t(1) << (p - 1)) - 1);
        const ASTNode x = mgr.CreateBVConst(width, bits);
        const ASTNode next =
            mgr.CreateBVConst(width, uint64_t(n + 1 + bias) << (p - 1));
        const ASTNode lower =
            mgr.CreateBVConst(width, uint64_t(n + bias) << (p - 1));
        for (unsigned chosen : {1u, 2u, 4u, 8u, 16u})
        {
          if (mode != 0 && mode != chosen)
            continue;
          const bool crosses =
              chosen == symbolic_fp::ROUND_TOWARD_POSITIVE && ex % 2 != 0;
          EXPECT_EQ(crosses ? mgr.ASTTrue : mgr.ASTFalse,
                    ruleInstance(f.context, rule, {x}, next, chosen));
          EXPECT_EQ(mgr.ASTTrue,
                    ruleInstance(f.context, rule, {x}, lower, chosen));
        }
      }
    }
}

TEST(FpAbstraction, revised_fma_b3_covers_added_binade)
{
  for (const auto& format :
       {std::make_pair(3u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned mode : {1u, 2u, 4u, 8u, 16u})
    {
      const unsigned eb = format.first, p = format.second, width = eb + p;
      const int64_t bias = (int64_t(1) << (eb - 1)) - 1;
      const uint64_t frac = (uint64_t(1) << (p - 1)) - 1;
      const auto bits = [&](int64_t e, uint64_t f)
      { return (uint64_t(e + bias) << (p - 1)) | f; };
      STPMgr mgr;
      RuleFixture f(mgr, FP_FMA, eb, p, mode, "fb3");
      const ASTNode rule = emittedRule(f.context, FpRuleId::FMA_B3, 2);
      expectExactRule(f.context, f.definition, rule);
      const ASTNode inf =
          mgr.CreateBVConst(width, ((uint64_t(1) << eb) - 1) << (p - 1));
      for (uint64_t z : {uint64_t(0), uint64_t(1), frac, bits(bias - 1, 0),
                         bits(bias - 1, frac)})
        for (unsigned signs = 0; signs < 8; ++signs)
        {
          const auto signedBits = [&](uint64_t b, unsigned i)
          {
            return mgr.CreateBVConst(
                width, b | (uint64_t((signs >> i) & 1) << (width - 1)));
          };
          const std::vector<ASTNode> args = {
              signedBits(bits(bias - 2, frac), 0), signedBits(bits(0, frac), 1),
              signedBits(z, 2)};
          EXPECT_EQ(mgr.ASTFalse, ruleInstance(f.context, rule, args, inf));
          EXPECT_EQ(mgr.ASTTrue, ruleInstance(f.context, rule, args,
                                              mgr.CreateZeroConst(width)));
        }
      // H=emax remains excluded: a top-binade addend can overflow.
      EXPECT_EQ(mgr.ASTTrue,
                ruleInstance(f.context, rule,
                             {mgr.CreateBVConst(width, bits(bias - 2, frac)),
                              mgr.CreateBVConst(width, bits(0, frac)),
                              mgr.CreateBVConst(width, bits(bias, frac))},
                             inf));
      EXPECT_EQ(mgr.ASTTrue,
                ruleInstance(f.context, rule,
                             {inf, mgr.CreateBVConst(width, bits(0, frac)),
                              mgr.CreateZeroConst(width)},
                             inf));
    }
}

TEST(FpAbstraction, revised_fma_x1_generates_and_cuts_in_added_binade)
{
  struct Case
  {
    unsigned eb, p;
    std::vector<uint64_t> args;
  };
  const Case cases[] = {{2, 3, {2, 4, 4}},    // 0.5 * 1 + 1
                        {3, 4, {24, 24, 40}}, // 1 * 1 + 4
                        {3, 4, {24, 32, 32}}, // 1 * 2 +/- 2
                        {3, 4, {1, 48, 40}}}; // minsub * 8 + 4
  for (const auto& c : cases)
    for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
    {
      const unsigned width = c.eb + c.p;
      STPMgr mgr;
      RuleFixture f(mgr, FP_FMA, c.eb, c.p, mode, "fx1");
      std::vector<ASTNode> args;
      for (uint64_t bits : c.args)
        args.push_back(mgr.CreateBVConst(width, bits));
      const ASTNode bad = mgr.CreateBVConst(width, 1);
      FpRuleId id;
      const ASTNode lemma = fpAbstractionShapeLemma(f.context, args, bad, &id);
      ASSERT_FALSE(lemma.IsNull());
      EXPECT_EQ(id, FpRuleId::FMA_X1);
      expectExactRule(f.context, f.definition, lemma);
      for (unsigned signs = 0; signs < 8; ++signs)
      {
        std::vector<ASTNode> signedArgs;
        for (unsigned i = 0; i < 3; ++i)
          signedArgs.push_back(mgr.CreateBVConst(
              width, c.args[i] | (uint64_t((signs >> i) & 1) << (width - 1))));
        EXPECT_EQ(mgr.ASTFalse,
                  ruleInstance(f.context, lemma, signedArgs, bad));
        EXPECT_EQ(mgr.ASTTrue, ruleInstance(f.context, lemma, signedArgs,
                                            mgr.CreateZeroConst(width)));
      }
      EXPECT_TRUE(fpAbstractionShapeLemma(f.context, args, args[2]).IsNull());
      EXPECT_TRUE(
          fpAbstractionShapeLemma(f.context, args, mgr.CreateZeroConst(width))
              .IsNull());
      // Merely having a finite candidate is insufficient outside the range.
      args[2] =
          mgr.CreateBVConst(width, ((uint64_t(1) << c.eb) - 2) << (c.p - 1));
      EXPECT_TRUE(fpAbstractionShapeLemma(f.context, args, bad).IsNull());
    }
}

TEST(FpAbstraction, revised_mul_p1_covers_both_upper_endpoint_cases)
{
  for (const auto& format : {std::make_pair(2u, 5u), std::make_pair(3u, 5u),
                             std::make_pair(3u, 7u), std::make_pair(5u, 11u)})
    for (unsigned k : std::set<unsigned>{2, (format.second - 1) / 2})
      for (unsigned mode : {1u, 2u, 4u, 8u, 16u})
      {
        const unsigned eb = format.first, p = format.second, width = eb + p;
        const uint64_t bias = (uint64_t(1) << (eb - 1)) - 1;
        const uint64_t frac = (uint64_t(1) << (p - 1)) - 1;
        STPMgr mgr;
        RuleFixture f(mgr, FP_MUL, eb, p, mode, "mp1");
        f.context.bandBits = k;
        const ASTNode rule = emittedRule(f.context, FpRuleId::MUL_P1, 2);
        expectExactRule(f.context, f.definition, rule);
        for (uint64_t xf : {uint64_t(0), frac})
          for (unsigned signs = 0; signs < 4; ++signs)
          {
            // xf=0: Q<2^(2k); xf=frac: Q=2^(2k), so U is not finite.
            const ASTNode x = mgr.CreateBVConst(
                width, ((2 * bias - 1) << (p - 1)) | xf |
                           (uint64_t(signs & 1) << (width - 1)));
            const ASTNode y = mgr.CreateBVConst(
                width, (bias << (p - 1)) | frac |
                           (uint64_t(signs >> 1) << (width - 1)));
            const ASTNode bad =
                mgr.CreateBVConst(width, (2 * bias - 1) << (p - 1));
            EXPECT_EQ(mgr.ASTFalse, ruleInstance(f.context, rule, {x, y}, bad));
          }
        // One binade higher remains outside the operand guard.
        EXPECT_EQ(mgr.ASTTrue,
                  ruleInstance(
                      f.context, rule,
                      {mgr.CreateBVConst(width, (2 * bias << (p - 1)) | frac),
                       mgr.CreateBVConst(width, (bias << (p - 1)) | frac)},
                      mgr.CreateBVConst(width, 2 * bias << (p - 1))));
      }
}

TEST(FpAbstraction, revised_add_a3_directed_boundary_and_orientations)
{
  for (Kind kind : {FP_ADD, FP_SUB})
    for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
    {
      STPMgr mgr;
      RuleFixture f(mgr, kind, 3, 4, mode, "aa3");
      const ASTNode rule = emittedRule(f.context, FpRuleId::ADD_A3, 3);
      expectExactRule(f.context, f.definition, rule);
      for (unsigned fraction : {0u, 1u})
        for (unsigned negative : {0u, 1u})
          for (uint64_t small : {20u, 12u, 6u}) // 0.75, 0.375, subnormal 0.1875
            for (unsigned orientation : {0u, 1u})
              for (unsigned chosen : {1u, 2u, 4u, 8u, 16u})
              {
                if (mode != 0 && mode != chosen)
                  continue;
                const uint64_t b =
                    48 + fraction + 64 * negative; // +/-8 or +/-9
                uint64_t x = b, y = small ^ (64 * (1 - negative));
                if (orientation != 0)
                  std::swap(x, y);
                if (kind == FP_SUB)
                  y ^= 64; // Undo the effective second-operand negation.
                const bool directed = chosen == 2 || chosen == 4 || chosen == 8;
                const bool guard =
                    small == 6 || (small == 12 && (fraction != 0 || directed));
                const bool inward = chosen == 8 || (chosen == 4 && !negative) ||
                                    (chosen == 2 && negative);
                const std::vector<ASTNode> args = {mgr.CreateBVConst(7, x),
                                                   mgr.CreateBVConst(7, y)};
                EXPECT_EQ(!guard || !inward ? mgr.ASTTrue : mgr.ASTFalse,
                          ruleInstance(f.context, rule, args,
                                       mgr.CreateBVConst(7, b), chosen));
                EXPECT_EQ(!guard || inward ? mgr.ASTTrue : mgr.ASTFalse,
                          ruleInstance(f.context, rule, args,
                                       mgr.CreateBVConst(7, b - 1), chosen));
              }
    }
}

TEST(FpAbstraction, revised_add_x1_top_binade_cancellation)
{
  for (const auto& format : {std::make_pair(2u, 3u), std::make_pair(3u, 4u)})
    for (Kind kind : {FP_ADD, FP_SUB, FP_REM})
      for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
      {
        if (kind == FP_REM && mode != 1)
          continue;
        const unsigned eb = format.first, p = format.second, width = eb + p;
        const uint64_t bias = (uint64_t(1) << (eb - 1)) - 1;
        const uint64_t sign = uint64_t(1) << (width - 1);
        const uint64_t large = 2 * bias << (p - 1);
        const uint64_t half = (2 * bias - 1) << (p - 1);
        for (uint64_t smaller : {large, half, half | (uint64_t(1) << (p - 2))})
          for (unsigned negative : {0u, 1u})
            for (unsigned orientation : {0u, 1u})
            {
              STPMgr mgr;
              RuleFixture f(mgr, kind, eb, p, mode, "ax1");
              uint64_t x = large | (negative ? sign : 0);
              uint64_t y = smaller |
                           ((kind == FP_ADD ? !negative : negative) ? sign : 0);
              if (orientation)
                std::swap(x, y);
              std::vector<ASTNode> args{mgr.CreateBVConst(width, x),
                                        mgr.CreateBVConst(width, y)};
              const ASTNode bad = mgr.CreateBVConst(width, 1);
              FpRuleId id;
              const ASTNode lemma =
                  fpAbstractionShapeLemma(f.context, args, bad, &id);
              ASSERT_FALSE(lemma.IsNull());
              EXPECT_EQ(id,
                        kind == FP_REM ? FpRuleId::REM_X1 : FpRuleId::ADD_X1);
              expectExactRule(f.context, f.definition, lemma);
              EXPECT_EQ(mgr.ASTFalse,
                        ruleInstance(f.context, lemma, args, bad));
              for (uint64_t zero : {uint64_t(0), sign})
                EXPECT_EQ(mgr.ASTTrue,
                          ruleInstance(f.context, lemma, args,
                                       mgr.CreateBVConst(width, zero)));
              EXPECT_TRUE(
                  fpAbstractionShapeLemma(f.context, args, args[0]).IsNull());
              EXPECT_TRUE(fpAbstractionShapeLemma(f.context, args,
                                                  mgr.CreateZeroConst(width))
                              .IsNull());
              args[1] = mgr.CreateBVConst(width, y ^ sign);
              EXPECT_EQ(kind != FP_REM,
                        fpAbstractionShapeLemma(f.context, args, bad).IsNull());
              EXPECT_EQ(kind == FP_REM ? mgr.ASTFalse : mgr.ASTTrue,
                        ruleInstance(f.context, lemma, args, bad));
            }
      }
}

TEST(FpAbstraction, revised_div_s7_nearest_and_directed_thresholds)
{
  for (const auto& format : {std::make_pair(2u, 2u), std::make_pair(3u, 3u),
                             std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
    {
      const unsigned eb = format.first, p = format.second, width = eb + p;
      const int64_t bias = (int64_t(1) << (eb - 1)) - 1, emin = 1 - bias;
      const int64_t nearest = emin - p + 1;
      const uint64_t sign = uint64_t(1) << (width - 1);
      STPMgr mgr;
      RuleFixture f(mgr, FP_DIV, eb, p, mode, "ds7");
      const ASTNode rule = emittedRule(f.context, FpRuleId::DIV_S7, 0);
      expectExactRule(f.context, f.definition, rule);
      for (int64_t s : {nearest - 1, nearest, nearest + 1})
      {
        const int64_t ey = emin - s;
        if (ey < emin || ey > bias)
          continue; // This format cannot reach the boundary with normals.
        const uint64_t xb = uint64_t(1) << (p - 1);
        const uint64_t yb =
            (uint64_t(ey + bias) << (p - 1)) | ((uint64_t(1) << (p - 1)) - 1);
        for (unsigned signs = 0; signs < 4; ++signs)
          for (unsigned chosen : {1u, 2u, 4u, 8u, 16u})
          {
            if (mode != 0 && chosen != mode)
              continue;
            const bool guard = s >= nearest + 1 ||
                               ((chosen == 1 || chosen == 16) && s >= nearest);
            const std::vector<ASTNode> args = {
                mgr.CreateBVConst(width, xb | ((signs & 1) ? sign : 0)),
                mgr.CreateBVConst(width, yb | ((signs & 2) ? sign : 0))};
            for (uint64_t zero : {uint64_t(0), sign})
              EXPECT_EQ(guard ? mgr.ASTFalse : mgr.ASTTrue,
                        ruleInstance(f.context, rule, args,
                                     mgr.CreateBVConst(width, zero), chosen));
          }
      }
      const ASTNode one = mgr.CreateBVConst(width, uint64_t(bias) << (p - 1));
      for (uint64_t excluded :
           {uint64_t(0), uint64_t(1), ((uint64_t(1) << eb) - 1) << (p - 1)})
        EXPECT_EQ(mgr.ASTTrue,
                  ruleInstance(f.context, rule,
                               {mgr.CreateBVConst(width, excluded), one},
                               mgr.CreateZeroConst(width),
                               mode == 0 ? 1 : mode));
    }
}

TEST(FpAbstraction, every_rule_holds_against_the_exact_operation)
{
  std::set<FpRuleId> seen;
  struct Case
  {
    Kind kind;
    unsigned eb, sb;
  };
  const Case cases[] = {{FP_MUL, 2, 3},  {FP_MUL, 3, 3},  {FP_MUL, 3, 4},
                        {FP_DIV, 2, 3},  {FP_DIV, 3, 3},  {FP_DIV, 3, 4},
                        {FP_SQRT, 2, 3}, {FP_SQRT, 3, 4}, {FP_SQRT, 4, 3},
                        {FP_ADD, 2, 3},  {FP_ADD, 3, 3},  {FP_ADD, 3, 4},
                        {FP_SUB, 2, 3},  {FP_SUB, 3, 4},  {FP_FMA, 2, 3},
                        {FP_FMA, 3, 3},  {FP_REM, 2, 3},  {FP_REM, 3, 3},
                        {FP_REM, 3, 4},  {FP_ROUNDTOINTEGRAL, 2, 3},
                        {FP_ROUNDTOINTEGRAL, 3, 4}, {FP_ROUNDTOINTEGRAL, 4, 3},
                        {FP_ROUNDTOINTEGRAL, 2, 4}};
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  for (const Case& c : cases)
    for (unsigned mode : modes)
    {
      if (c.kind == FP_REM && mode != modes[0])
        continue; // no mode
      STPMgr mgr;
      mgr.UserFlags.fp_abstraction = false;
      RuleFixture f(mgr, c.kind, c.eb, c.sb, mode, "v");
      std::vector<ASTNode> rules;
      std::vector<FpRuleId> ids;
      const unsigned emitted =
          emitFpAbstractionRules(f.context, 3, rules, &ids);
      ASSERT_NO_FATAL_FAILURE(rememberRuleIds(ids, rules, seen));
      ASSERT_EQ(emitted, rules.size());
      ASSERT_GT(emitted, 8u);
      for (size_t i = 0; i < rules.size(); ++i)
      {
        SCOPED_TRACE(fpRuleName(ids[i]));
        const ASTNode query =
            conj(mgr, {f.definition, mgr.CreateNode(NOT, rules[i])});
        STP solver(&mgr);
        EXPECT_EQ(SOLVER_VALID, solver.TopLevelSTP(query, mgr.ASTFalse))
            << "rule " << i << " of kind " << c.kind << " at (" << c.eb << ","
            << c.sb << ") mode " << mode << ": " << rules[i];
      }
    }
  expectRuleCoverage(seen, "arithmetic");
}

namespace
{

// The same for an integer conversion in its totalised form: the operand is
// the packed view of a symbol, the result and the unspecified value are
// symbols of the target width, and `definition` is
// t = to_sbv/to_ubv(m, rm, x, u) over them.
struct ConversionFixture
{
  FpRuleContext context;
  ASTNode definition;

  ConversionFixture(STPMgr& mgr, Kind kind, unsigned eb, unsigned sb,
                    unsigned m, unsigned mode, const std::string& tag)
  {
    const unsigned width = eb + sb;
    const ASTNode xb = mgr.CreateSourceSymbol((tag + "_x").c_str(),
                                              SourceSort::bitVector(width));
    const ASTNode x = FloatBlaster::withFormat(
        &mgr,
        mgr.CreateTerm(FP_TOFP, width, mgr.CreateBVConst(32, eb),
                       mgr.CreateBVConst(32, sb), xb),
        eb, sb);
    const ASTNode tb = mgr.CreateSourceSymbol((tag + "_t").c_str(),
                                              SourceSort::bitVector(m));
    const ASTNode undef = mgr.CreateSourceSymbol((tag + "_u").c_str(),
                                                 SourceSort::bitVector(m));
    context.bm = &mgr;
    context.kind = kind;
    context.eb = eb;
    context.sb = sb;
    context.rm = mode;
    context.rmTerm = mode != 0
                         ? rmConst(mgr, mode)
                         : mgr.CreateSourceSymbol((tag + "_rm").c_str(),
                                                  SourceSort::roundingMode());
    context.bits.push_back(xb);
    context.view.push_back(x);
    context.tb = tb;
    context.targetWidth = m;
    context.undefBits = undef;
    definition = mgr.CreateNode(
        EQ, tb,
        mgr.CreateTerm(kind, m,
                       ASTVec{mgr.CreateBVConst(32, m), context.rmTerm, x,
                              undef}));
  }
};

} // namespace

// Every emitted conversion rule, against the exact totalised operation, at
// formats on both sides of the one boundary that matters to them: whether
// the top binade of the target range holds non-integers (p > m) or not.
// The signed row for a negative of the top binade once sent every nonzero
// fraction to the unspecified value, which p > m refutes (-8.25 to 4 bits
// under RNE is -8); the formats with p > m here are what catches that.
TEST(FpAbstraction, revised_ubv_b5_zero_is_independent_of_totalisation)
{
  for (const auto& format :
       {std::make_pair(2u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned m : {2u, 64u, 128u})
      for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
      {
        const unsigned eb = format.first, p = format.second, width = eb + p;
        STPMgr mgr;
        ConversionFixture f(mgr, FP_TO_UBV, eb, p, m, mode, "ub5");
        const ASTNode rule = emittedRule(f.context, FpRuleId::UBV_B5, 2, true);
        EXPECT_FALSE(containsTerm(rule, f.context.undefBits));
        expectExactRule(f.context, f.definition, rule); // u remains symbolic.
        for (uint64_t xb = 0; xb < (uint64_t(1) << width); ++xb)
        {
          const ASTNode x = mgr.CreateBVConst(width, xb);
          const auto v = decodeFpPackedValue(x, eb, p);
          const bool small = v.negative && v.e < 0 &&
                             (v.cls == FpPackedValue::Normal ||
                              v.cls == FpPackedValue::Subnormal);
          for (unsigned chosen : {1u, 2u, 4u, 8u, 16u})
          {
            if (mode != 0 && chosen != mode)
              continue;
            const bool guard =
                small && (chosen == 8 || chosen == 2 ||
                          ((chosen == 1 || chosen == 16) && v.e <= -2));
            EXPECT_EQ(mgr.ASTTrue,
                      ruleInstance(f.context, rule, {x}, mgr.CreateZeroConst(m),
                                   chosen));
            EXPECT_EQ(guard ? mgr.ASTFalse : mgr.ASTTrue,
                      ruleInstance(f.context, rule, {x}, mgr.CreateOneConst(m),
                                   chosen));
          }
        }
      }
  for (Kind kind : {FP_TO_UBV, FP_TO_SBV})
  {
    STPMgr mgr;
    ConversionFixture f(mgr, kind, 3, 4, kind == FP_TO_UBV ? 1 : 64, 2,
                        "ub5_scope");
    std::vector<ASTNode> rules;
    std::vector<FpRuleId> ids;
    emitFpAbstractionRules(f.context, 3, rules, &ids);
    EXPECT_EQ(std::find(ids.begin(), ids.end(), FpRuleId::UBV_B5), ids.end());
  }
}

TEST(FpAbstraction, revised_ubv_b6_uses_the_full_symbolic_totalisation_value)
{
  for (const auto& format :
       {std::make_pair(2u, 3u), std::make_pair(3u, 4u), std::make_pair(4u, 3u)})
    for (unsigned m : {2u, 64u, 128u})
      for (unsigned mode : {0u, 1u, 2u, 4u, 8u, 16u})
      {
        const unsigned eb = format.first, p = format.second, width = eb + p;
        STPMgr mgr;
        ConversionFixture f(mgr, FP_TO_UBV, eb, p, m, mode, "ub6");
        const ASTNode rule = emittedRule(f.context, FpRuleId::UBV_B6, 2, true);
        if (mode == 0 || mode == 4)
        {
          EXPECT_TRUE(containsTerm(rule, f.context.undefBits));
        }
        expectExactRule(f.context, f.definition, rule);
        const ASTNode zero = mgr.CreateZeroConst(m),
                      one = mgr.CreateOneConst(m);
        const ASTNode high =
            mgr.CreateBVConst(std::string("1") + std::string(m - 1, '0'), 2, m);
        for (uint64_t xb = 0; xb < (uint64_t(1) << width); ++xb)
        {
          const ASTNode x = mgr.CreateBVConst(width, xb);
          const auto v = decodeFpPackedValue(x, eb, p);
          const bool small = v.negative && v.e < 0 &&
                             (v.cls == FpPackedValue::Normal ||
                              v.cls == FpPackedValue::Subnormal);
          for (unsigned chosen : {1u, 2u, 4u, 8u, 16u})
          {
            if (mode != 0 && chosen != mode)
              continue;
            for (const ASTNode& u : {zero, one, high})
            {
              EXPECT_EQ(mgr.ASTTrue,
                        ruleInstance(f.context, rule, {x}, u, chosen, u));
              EXPECT_EQ(small && chosen == 4 ? mgr.ASTFalse : mgr.ASTTrue,
                        ruleInstance(f.context, rule, {x},
                                     u == zero ? one : zero, chosen, u));
            }
          }
        }
      }
  for (Kind kind : {FP_TO_UBV, FP_TO_SBV})
  {
    STPMgr mgr;
    ConversionFixture f(mgr, kind, 3, 4, kind == FP_TO_UBV ? 1 : 64, 4,
                        "ub6_scope");
    std::vector<ASTNode> rules;
    std::vector<FpRuleId> ids;
    emitFpAbstractionRules(f.context, 3, rules, &ids);
    EXPECT_EQ(std::find(ids.begin(), ids.end(), FpRuleId::UBV_B6), ids.end());
  }
}

TEST(FpAbstraction, conversion_rules_hold_against_the_exact_operation)
{
  std::set<FpRuleId> seen;
  struct Case
  {
    Kind kind;
    unsigned eb, sb, m;
  };
  const Case cases[] = {{FP_TO_SBV, 3, 6, 4}, {FP_TO_SBV, 3, 5, 3},
                        {FP_TO_SBV, 3, 6, 2}, {FP_TO_SBV, 3, 4, 4},
                        {FP_TO_SBV, 4, 4, 5}, {FP_TO_SBV, 2, 6, 3},
                        {FP_TO_UBV, 3, 6, 4}, {FP_TO_UBV, 3, 5, 3},
                        {FP_TO_UBV, 3, 4, 4}, {FP_TO_UBV, 4, 4, 6},
                        // m must fit the signed exponent comparison even
                        // when it is much wider than the source format.
                        {FP_TO_SBV, 2, 2, 64}, {FP_TO_UBV, 2, 2, 64},
                        {FP_TO_SBV, 2, 3, 128}, {FP_TO_UBV, 2, 3, 128}};
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  for (const Case& c : cases)
    for (unsigned mode : modes)
    {
      STPMgr mgr;
      mgr.UserFlags.fp_abstraction = false;
      ConversionFixture f(mgr, c.kind, c.eb, c.sb, c.m, mode, "cv");
      std::vector<ASTNode> rules;
      std::vector<FpRuleId> ids;
      const unsigned emitted =
          emitFpAbstractionRules(f.context, 3, rules, &ids);
      ASSERT_NO_FATAL_FAILURE(rememberRuleIds(ids, rules, seen));
      ASSERT_EQ(emitted, rules.size());
      ASSERT_GE(emitted, 5u);
      for (size_t i = 0; i < rules.size(); ++i)
      {
        SCOPED_TRACE(fpRuleName(ids[i]));
        const ASTNode query =
            conj(mgr, {f.definition, mgr.CreateNode(NOT, rules[i])});
        STP solver(&mgr);
        EXPECT_EQ(SOLVER_VALID, solver.TopLevelSTP(query, mgr.ASTFalse))
            << "rule " << i << " of kind " << c.kind << " at (" << c.eb << ","
            << c.sb << ") to " << c.m << " bits, mode " << mode << ": "
            << rules[i];
      }
    }
  expectRuleCoverage(seen, "conversions");
}

TEST(FpAbstraction, one_bit_conversions_have_no_initial_rules)
{
  STPMgr mgr;
  for (Kind kind : {FP_TO_SBV, FP_TO_UBV})
  {
    ConversionFixture f(mgr, kind, 3, 4, 1,
                        symbolic_fp::ROUND_TOWARD_ZERO, "one_bit");
    std::vector<ASTNode> rules;
    EXPECT_EQ(0u, emitFpAbstractionRules(f.context, 3, rules));
    EXPECT_TRUE(rules.empty());
  }
}

// Congruence between two records of one operation whose operands are equal
// in the candidate but whose results are not: chosen, valid, and taken with
// the product's factors in either order; and not offered when the results
// agree.
TEST(FpAbstraction, congruence_lemmas_are_chosen_by_violation_and_hold)
{
  std::set<FpRuleId> seen;
  const Kind kinds[] = {FP_MUL, FP_DIV, FP_ADD, FP_SUB, FP_SQRT, FP_FMA,
                        FP_REM, FP_ROUNDTOINTEGRAL};
  const unsigned eb = 3, sb = 4, width = 7;
  for (Kind kind : kinds)
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = false;
    RuleFixture a(mgr, kind, eb, sb, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                  "ca");
    RuleFixture b(mgr, kind, eb, sb, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                  "cb");
    const size_t n = a.context.bits.size();
    // Equal operand values (a commuted pair for a product), different
    // results.
    std::vector<ASTNode> av, bv;
    for (size_t i = 0; i < n; ++i)
      av.push_back(mgr.CreateBVConst(width, 0x20 + i)); // 2.0, 2.25, ...
    bv = av;
    if (kind == FP_MUL || kind == FP_ADD || kind == FP_FMA)
      std::swap(bv[0], bv[1]);
    FpRuleId id;
    const ASTNode lemma = fpAbstractionRelationalLemma(
        a.context, av, mgr.CreateBVConst(width, 0x28), b.context, bv,
        mgr.CreateBVConst(width, 0x18), &id);
    SCOPED_TRACE(fpRuleName(id));
    ASSERT_NE(FpRuleId::None, id);
    seen.insert(id);
    ASSERT_FALSE(lemma.IsNull()) << kind;
    STP solver(&mgr);
    EXPECT_EQ(SOLVER_VALID,
              solver.TopLevelSTP(conj(mgr, {a.definition, b.definition,
                                            mgr.CreateNode(NOT, lemma)}),
                                 mgr.ASTFalse))
        << kind << " " << lemma;
    // Agreeing results: nothing to say.
    EXPECT_TRUE(fpAbstractionRelationalLemma(
                    a.context, av, mgr.CreateBVConst(width, 0x28), b.context,
                    bv, mgr.CreateBVConst(width, 0x28))
                    .IsNull())
        << kind;
  }
  expectRuleCoverage(seen, "congruence");
}

// The reduced-precision significand bands, at formats wide enough to hold
// them (2k + 1 <= p), against the exact operation in every mode; and that
// they are what the flag adds.
TEST(FpAbstraction, significand_bands_hold_against_the_exact_operation)
{
  std::set<FpRuleId> seen;
  struct Case
  {
    Kind kind;
    unsigned eb, sb, k;
  };
  const Case cases[] = {{FP_MUL, 2, 6, 2},  {FP_MUL, 3, 6, 2},  {FP_MUL, 3, 8, 3},
                        {FP_DIV, 2, 6, 2},  {FP_DIV, 3, 6, 2},  {FP_DIV, 3, 8, 3},
                        {FP_SQRT, 2, 6, 2}, {FP_SQRT, 3, 6, 2}, {FP_SQRT, 3, 8, 3},
                        {FP_MUL, 2, 8, 8},  {FP_DIV, 4, 7, 8}};
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  for (const Case& c : cases)
    for (unsigned mode : modes)
    {
      STPMgr mgr;
      mgr.UserFlags.fp_abstraction = false;
      RuleFixture f(mgr, c.kind, c.eb, c.sb, mode, "sb");
      std::vector<ASTNode> without;
      f.context.bandBits = 0;
      emitFpAbstractionRules(f.context, 3, without);
      std::vector<ASTNode> rules;
      std::vector<FpRuleId> ids;
      f.context.bandBits = c.k;
      const unsigned emitted =
          emitFpAbstractionRules(f.context, 3, rules, &ids);
      ASSERT_NO_FATAL_FAILURE(rememberRuleIds(ids, rules, seen));
      ASSERT_EQ(without.size() + 1, emitted)
          << "kind " << c.kind << " (" << c.eb << "," << c.sb << ") k=" << c.k;
      SCOPED_TRACE(fpRuleName(ids.back()));
      const ASTNode band = rules.back();
      const ASTNode query =
          conj(mgr, {f.definition, mgr.CreateNode(NOT, band)});
      STP solver(&mgr);
      EXPECT_EQ(SOLVER_VALID, solver.TopLevelSTP(query, mgr.ASTFalse))
          << "band of kind " << c.kind << " at (" << c.eb << "," << c.sb
          << ") k=" << c.k << " mode " << mode << ": " << band;
    }
  // Too narrow for a band: nothing is emitted.
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = false;
    RuleFixture f(mgr, FP_MUL, 3, 4, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                  "sn");
    std::vector<ASTNode> without, with;
    f.context.bandBits = 0;
    emitFpAbstractionRules(f.context, 3, without);
    f.context.bandBits = 8;
    emitFpAbstractionRules(f.context, 3, with);
    EXPECT_EQ(without.size(), with.size());
  }
  expectRuleCoverage(seen, "bands");
}

// The monotonicity facts: chosen by a candidate that violates one, valid
// against the exact operations of both applications.
TEST(FpAbstraction, relational_lemmas_are_chosen_by_violation_and_hold)
{
  std::set<FpRuleId> seen;
  struct Case
  {
    Kind kind;
    // Which operand of the second application is the first's (by index),
    // or -1 for none shared; the others are fresh.
    int shared[3];
  };
  const Case cases[] = {{FP_MUL, {0, -1, -1}},  {FP_MUL, {-1, 0, -1}},
                        {FP_ADD, {0, -1, -1}},  {FP_SUB, {0, -1, -1}},
                        {FP_SUB, {-1, 1, -1}},  {FP_DIV, {0, -1, -1}},
                        {FP_DIV, {-1, 1, -1}},  {FP_SQRT, {-1, -1, -1}},
                        {FP_ROUNDTOINTEGRAL, {-1, -1, -1}},
                        {FP_FMA, {0, -1, 2}},   {FP_FMA, {0, 1, -1}}};
  const unsigned eb = 3, sb = 4, width = 7;
  for (const Case& c : cases)
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = false;
    RuleFixture a(mgr, c.kind, eb, sb, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                  "ra");
    RuleFixture b(mgr, c.kind, eb, sb, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                  "rb");
    // Share by substituting a's symbols into b's context.
    ASTNodeMap share;
    for (unsigned i = 0; i < 3; ++i)
      if (c.shared[i] >= 0)
        share[b.context.bits[i]] = a.context.bits[c.shared[i]];
    const auto substitute = [&](const ASTNode& n) {
      ASTNodeMap cache;
      return SubstitutionMap::replace(n, share, cache, mgr.defaultNodeFactory,
                                      false, false);
    };
    for (size_t i = 0; i < b.context.bits.size(); ++i)
    {
      b.context.bits[i] = substitute(b.context.bits[i]);
      b.context.view[i] = substitute(b.context.view[i]);
    }
    b.definition = substitute(b.definition);

    // Candidate values: every operand 2.0 (shared or not), except the free
    // one of b, which is 4.0; the results in the wrong order for the
    // operation's monotonicity.
    const uint64_t two = 0x20, four = 0x28, one = 0x18, half = 0x10;
    std::vector<ASTNode> av, bv;
    for (size_t i = 0; i < a.context.bits.size(); ++i)
    {
      av.push_back(mgr.CreateBVConst(width, two));
      bv.push_back(mgr.CreateBVConst(width, c.shared[i] >= 0 ? two : four));
    }
    // The candidate results, chosen against each operation's direction.
    uint64_t ta = one, tb = half;
    bool expectLemma = true;
    switch (c.kind)
    {
      case FP_MUL:
      case FP_ADD:
      case FP_SQRT:
      case FP_ROUNDTOINTEGRAL:
      case FP_FMA:
        // Larger free operand, larger result: candidate has b's smaller.
        ta = four;
        tb = two;
        break;
      case FP_SUB:
        // x - y: sharing x, a larger y gives a smaller result; sharing y,
        // a larger x a larger one.
        if (c.shared[0] >= 0)
        {
          ta = half;
          tb = one;
        }
        else
        {
          ta = four;
          tb = two;
        }
        break;
      case FP_DIV:
        if (c.shared[0] >= 0)
        {
          // One dividend: the larger divisor gives the smaller quotient.
          ta = half;
          tb = one;
        }
        else
        {
          ta = four;
          tb = two;
        }
        break;
      default:
        expectLemma = false;
    }
    FpRuleId id;
    const ASTNode lemma = fpAbstractionRelationalLemma(
        a.context, av, mgr.CreateBVConst(width, ta), b.context, bv,
        mgr.CreateBVConst(width, tb), &id);
    SCOPED_TRACE(fpRuleName(id));
    ASSERT_EQ(expectLemma, !lemma.IsNull()) << c.kind;
    if (!expectLemma)
    {
      EXPECT_EQ(FpRuleId::None, id);
      continue;
    }
    ASSERT_NE(FpRuleId::None, id);
    seen.insert(id);
    // Valid: both exact definitions and the lemma's negation is unsat.
    STP solver(&mgr);
    EXPECT_EQ(SOLVER_VALID,
              solver.TopLevelSTP(
                  conj(mgr, {a.definition, b.definition,
                             mgr.CreateNode(NOT, lemma)}),
                  mgr.ASTFalse))
        << c.kind << " " << lemma;
    // And violated by the candidate that chose it: the same query with the
    // candidate's values pinned is unsat as well, so nothing here is
    // trivial -- but with the lemma alone and the values pinned, it is the
    // lemma that fails.
    ASTVec pinned;
    for (size_t i = 0; i < av.size(); ++i)
    {
      pinned.push_back(mgr.CreateNode(EQ, a.context.bits[i], av[i]));
      pinned.push_back(mgr.CreateNode(EQ, b.context.bits[i], bv[i]));
    }
    pinned.push_back(mgr.CreateNode(EQ, a.context.tb, mgr.CreateBVConst(width, ta)));
    pinned.push_back(mgr.CreateNode(EQ, b.context.tb, mgr.CreateBVConst(width, tb)));
    pinned.push_back(lemma);
    STP again(&mgr);
    EXPECT_EQ(SOLVER_VALID, again.TopLevelSTP(mgr.CreateNode(AND, pinned),
                                              mgr.ASTFalse))
        << c.kind;
  }
  expectRuleCoverage(seen, "relational");
}

// The facts between a fused multiply-add and the product of its factors or
// the sum of a factor with its addend: valid against the exact operations,
// at tiny formats, in every mode.
TEST(FpAbstraction, cross_operation_fma_rules_hold)
{
  std::set<FpRuleId> seen;
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  const unsigned formats[][2] = {{2, 3}, {3, 3}, {3, 4}};
  for (const unsigned* f : formats)
    for (unsigned mode : modes)
    {
      const unsigned eb = f[0], sb = f[1], width = eb + sb;
      STPMgr mgr;
      mgr.UserFlags.fp_abstraction = false;
      RuleFixture fma(mgr, FP_FMA, eb, sb, mode, "cf");
      // Partner contexts over the fma's own operand symbols, each with its
      // own result symbol and exact definition.
      const auto partner = [&](Kind kind, unsigned i, unsigned j,
                               const std::string& tag) {
        RuleFixture r(mgr, kind, eb, sb, mode, tag);
        r.context.bits[0] = fma.context.bits[i];
        r.context.view[0] = fma.context.view[i];
        r.context.bits[1] = fma.context.bits[j];
        r.context.view[1] = fma.context.view[j];
        r.definition = mgr.CreateNode(
            FP_SMT_EQ, r.context.t,
            mgr.CreateTerm(kind, width,
                           ASTVec{r.context.rmTerm, r.context.view[0],
                                  r.context.view[1]}));
        return r;
      };
      const RuleFixture product = partner(FP_MUL, 0, 1, "cp");
      const RuleFixture sumWithX = partner(FP_ADD, 0, 2, "cx");
      const RuleFixture sumWithY = partner(FP_ADD, 1, 2, "cy");
      std::vector<ASTNode> rules;
      std::vector<FpRuleId> ids;
      const unsigned emitted = emitFpAbstractionCrossRules(
          fma.context, &product.context, &sumWithX.context, &sumWithY.context,
          rules, &ids);
      ASSERT_NO_FATAL_FAILURE(rememberRuleIds(ids, rules, seen));
      ASSERT_EQ(5u, emitted);
      ASSERT_EQ(5u, rules.size());
      for (size_t i = 0; i < rules.size(); ++i)
      {
        SCOPED_TRACE(fpRuleName(ids[i]));
        const ASTNode query = conj(
            mgr, {fma.definition, product.definition, sumWithX.definition,
                  sumWithY.definition, mgr.CreateNode(NOT, rules[i])});
        STP solver(&mgr);
        EXPECT_EQ(SOLVER_VALID, solver.TopLevelSTP(query, mgr.ASTFalse))
            << "cross rule " << i << " at (" << eb << "," << sb << ") mode "
            << mode << ": " << rules[i];
      }
    }
  expectRuleCoverage(seen, "cross");
}

// The pass that finds the partners: a product recorded before the fma, a
// sum recorded after it, commuted operands, and nothing for a sum over the
// wrong pair.
TEST(FpAbstraction, cross_operation_rules_find_partners_either_way_round)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  mgr.UserFlags.fp_abstraction_width = 4;
  mgr.UserFlags.fp_abstraction_ops = 127;
  const SourceSort format = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("c_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("c_y", format);
  const ASTNode z = mgr.CreateSourceSymbol("c_z", format);
  const ASTNode w = mgr.CreateSourceSymbol("c_w", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode yx = mgr.CreateTerm(FP_MUL, 16, ASTVec{rne, y, x});
  const ASTNode fma = mgr.CreateTerm(FP_FMA, 16, ASTVec{rne, x, y, z});
  const ASTNode zx = mgr.CreateTerm(FP_ADD, 16, ASTVec{rne, z, x});
  const ASTNode zw = mgr.CreateTerm(FP_ADD, 16, ASTVec{rne, z, w});
  const ASTNode formula = conj(
      mgr, {mgr.CreateNode(FP_LT, yx, fma), mgr.CreateNode(FP_LT, zx, fma),
            mgr.CreateNode(FP_LT, zw, fma)});
  FpAbstraction abstraction(&mgr);
  abstraction.abstract(formula);
  ASSERT_TRUE(abstraction.active());
  EXPECT_EQ(4u, abstraction.applications().size());
  // Three against the product, one against add(x, z); add(z, w) shares
  // only the addend and is no partner.
  EXPECT_EQ(4u, abstraction.statistics().crossRules);

  // And end to end: an fma against its product with a non-negative addend
  // cannot be below it (unsat), while with a negative addend it can (sat).
  {
    STPMgr m;
    const ASTNode a = m.CreateSourceSymbol("e_a", format);
    const ASTNode b = m.CreateSourceSymbol("e_b", format);
    const ASTNode c = m.CreateSourceSymbol("e_c", format);
    const ASTNode rm = rmConst(m, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode p = m.CreateTerm(FP_MUL, 16, ASTVec{rm, a, b});
    const ASTNode t = m.CreateTerm(FP_FMA, 16, ASTVec{rm, a, b, c});
    const ASTNode pzero = fpConst(m, 5, 11, 0x0000);
    const ASTNode common = conj(
        m, {m.CreateNode(NOT, m.CreateNode(FP_ISNAN, p)),
            m.CreateNode(NOT, m.CreateNode(FP_ISNAN, t)),
            m.CreateNode(FP_LT, t, p)});
    m.UserFlags.fp_abstraction_ops = 127;
    expectParity(m, conj(m, {common, m.CreateNode(FP_LEQ, pzero, c)}),
                 SOLVER_VALID);
    expectParity(m, conj(m, {common, m.CreateNode(FP_LT, c, pzero)}),
                 SOLVER_INVALID);
  }
}

// Incremental pieces can introduce partners in any order. The piece that
// completes a relationship must assert it, with both records' definitions,
// and a later use of either participant must remain self-contained.
TEST(FpAbstraction, incremental_cross_rules_carry_late_partners_and_definitions)
{
  std::vector<unsigned> order{0, 1, 2, 3};
  do
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_width = 4;
    mgr.UserFlags.fp_abstraction_ops = FP_ABSTRACT_FMA | FP_ABSTRACT_MUL |
                                        FP_ABSTRACT_ADD;
    FpAbstraction abstraction(&mgr);
    const SourceSort format = SourceSort::floatingPoint(5, 11);
    const ASTNode x = mgr.CreateSourceSymbol("late_x", format);
    const ASTNode y = mgr.CreateSourceSymbol("late_y", format);
    const ASTNode z = mgr.CreateSourceSymbol("late_z", format);
    const ASTNode rm = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode ops[] = {
        mgr.CreateTerm(FP_FMA, 16, ASTVec{rm, x, y, z}),
        mgr.CreateTerm(FP_MUL, 16, ASTVec{rm, y, x}), // commuted partner
        mgr.CreateTerm(FP_ADD, 16, ASTVec{rm, z, x}),
        mgr.CreateTerm(FP_ADD, 16, ASTVec{rm, y, z})};
    const FpAbstraction::Application* records[4] = {};
    for (unsigned next : order)
    {
      const ASTNode piece = abstraction.abstractPiece(
          mgr.CreateNode(FP_ISNORMAL, ops[next]));
      records[next] = abstraction.applications().back().get();
      unsigned expected = 0;
      if (records[0] != NULL)
        for (unsigned partner = 1; partner < 4; ++partner)
        {
          if (records[partner] == NULL)
            continue;
          expected += partner == 1 ? 3 : 1;
          if (next != 0 && next != partner)
            continue;
          unsigned found = 0;
          for (const ASTNode& d : records[0]->defs)
            if (containsTerm(d, records[0]->surrogate) &&
                containsTerm(d, records[partner]->surrogate))
            {
              ++found;
              EXPECT_TRUE(containsTerm(piece, d));
            }
          EXPECT_EQ(partner == 1 ? 3u : 1u, found);
          // The product's own source contains no z: this also tests the
          // closure through the FMA introduced by the new relationship.
          EXPECT_TRUE(containsTerm(piece, z));
          for (const auto* record : {records[0], records[partner]})
            for (const ASTNode& d : record->defs)
              EXPECT_TRUE(containsTerm(piece, d));
        }
      EXPECT_EQ(expected, abstraction.statistics().crossRules);
    }
    for (unsigned again : order)
    {
      const ASTNode piece = abstraction.abstractPiece(
          mgr.CreateNode(FP_ISNORMAL, ops[again]));
      for (const auto* record : records)
        for (const ASTNode& d : record->defs)
          EXPECT_TRUE(containsTerm(piece, d));
    }
    EXPECT_EQ(5u, abstraction.statistics().crossRules);
  } while (std::next_permutation(order.begin(), order.end()));
}

TEST(FpAbstraction, incremental_cross_rules_keep_both_sum_roles)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  mgr.UserFlags.fp_abstraction_width = 4;
  mgr.UserFlags.fp_abstraction_ops = FP_ABSTRACT_FMA | FP_ABSTRACT_ADD;
  const SourceSort format = SourceSort::floatingPoint(5, 11);
  const ASTNode x = mgr.CreateSourceSymbol("roles_x", format);
  const ASTNode z = mgr.CreateSourceSymbol("roles_z", format);
  const ASTNode rm = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode fma = mgr.CreateTerm(FP_FMA, 16, ASTVec{rm, x, x, z});
  const ASTNode sum = mgr.CreateTerm(FP_ADD, 16, ASTVec{rm, x, z});
  FpAbstraction abstraction(&mgr);
  abstraction.abstractPiece(mgr.CreateNode(FP_ISNORMAL, fma));
  EXPECT_EQ(0u, abstraction.statistics().crossRules);
  abstraction.abstractPiece(mgr.CreateNode(FP_ISNORMAL, sum));
  EXPECT_EQ(2u, abstraction.statistics().crossRules);
  abstraction.abstractPiece(mgr.CreateNode(FP_ISNORMAL, sum));
  EXPECT_EQ(2u, abstraction.statistics().crossRules);
}

// A wide operation is released by running the pipeline again with it
// lowered exactly; the run after that still abstracts the rest, and its
// statistics count the run before it.
TEST(FpAbstraction, wide_release_restarts_the_pipeline)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  mgr.UserFlags.fp_abstraction_values = 0; // release at the first refutation
  mgr.UserFlags.fp_abstraction_shape = false;
  mgr.UserFlags.check_counterexample_flag = true;
  const SourceSort format = SourceSort::floatingPoint(11, 53);
  const ASTNode x = mgr.CreateSourceSymbol("rs_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("rs_y", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode xy = mgr.CreateTerm(FP_MUL, 64, ASTVec{rne, x, y});
  const ASTNode two = fpConst(mgr, 11, 53, 0x4000000000000000ull);
  const ASTNode x2 = mgr.CreateTerm(FP_MUL, 64, ASTVec{rne, x, two});
  const ASTNode three = fpConst(mgr, 11, 53, 0x4008000000000000ull);
  const ASTNode low = fpConst(mgr, 11, 53, 0x3ff199999999999aull);  // 1.1
  const ASTNode high = fpConst(mgr, 11, 53, 0x3ff3333333333333ull); // 1.2
  // The pinned product needs its value -- x is held in an interval whose
  // ends are not factors of three, so no candidate the rules admit is
  // exact -- and is released; the doubling is pinned by the power-of-two
  // identity rule, so its candidate is always exact and it stays
  // abstracted through every run.
  const ASTNode formula = conj(
      mgr, {mgr.CreateNode(FP_LT, low, x), mgr.CreateNode(FP_LT, x, high),
            mgr.CreateNode(FP_ISNORMAL, y), mgr.CreateNode(FP_SMT_EQ, xy, three),
            mgr.CreateNode(FP_ISNORMAL, x2)});
  {
    mgr.UserFlags.fp_abstraction_restart_width = 64;
    STP solver(&mgr);
    EXPECT_EQ(SOLVER_INVALID, solver.TopLevelSTP(formula, mgr.ASTFalse));
    ASSERT_TRUE(mgr.getFpAbstractionIfAny() != NULL);
    const FpAbstraction& last = *mgr.getFpAbstractionIfAny();
    EXPECT_EQ(1u, last.statistics().restarts);
    EXPECT_EQ(1u, last.applications().size());
    EXPECT_EQ(FP_MUL, last.applications()[0]->kind);
    EXPECT_EQ(0u, last.statistics().releases);
    EXPECT_FALSE(last.restartRequested());
  }
  {
    // In place: one run, the release spliced, no restart.
    mgr.UserFlags.fp_abstraction_restart_width = 0;
    STP solver(&mgr);
    EXPECT_EQ(SOLVER_INVALID, solver.TopLevelSTP(formula, mgr.ASTFalse));
    ASSERT_TRUE(mgr.getFpAbstractionIfAny() != NULL);
    const FpAbstraction& last = *mgr.getFpAbstractionIfAny();
    EXPECT_EQ(0u, last.statistics().restarts);
    EXPECT_EQ(2u, last.applications().size());
    EXPECT_EQ(1u, last.statistics().releases);
  }
  // And below the width, in place whatever the setting.
  {
    STPMgr m;
    m.UserFlags.fp_abstraction = true;
    m.UserFlags.fp_abstraction_restart_width = 64;
    m.UserFlags.fp_abstraction_values = 0;
    m.UserFlags.fp_abstraction_shape = false;
    m.UserFlags.check_counterexample_flag = true;
    const SourceSort f32 = SourceSort::floatingPoint(8, 24);
    const ASTNode a = m.CreateSourceSymbol("rs_a", f32);
    const ASTNode b = m.CreateSourceSymbol("rs_b", f32);
    const ASTNode rm = rmConst(m, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode ab = m.CreateTerm(FP_MUL, 32, ASTVec{rm, a, b});
    const ASTNode formula32 = conj(
        m, {m.CreateNode(FP_LT, fpConst(m, 8, 24, 0x3f8ccccd), a), // 1.1
            m.CreateNode(FP_LT, a, fpConst(m, 8, 24, 0x3f99999a)), // 1.2
            m.CreateNode(FP_ISNORMAL, b),
            m.CreateNode(FP_SMT_EQ, ab, fpConst(m, 8, 24, 0x40400000))});
    STP solver(&m);
    EXPECT_EQ(SOLVER_INVALID, solver.TopLevelSTP(formula32, m.ASTFalse));
    ASSERT_TRUE(m.getFpAbstractionIfAny() != NULL);
    EXPECT_EQ(0u, m.getFpAbstractionIfAny()->statistics().restarts);
    EXPECT_EQ(1u, m.getFpAbstractionIfAny()->statistics().releases);
  }
}

// A refuted candidate whose values for the original symbols satisfy the
// original formula is a model: accepted by the replay, with nothing
// refined. Without the repair the same query takes a round.
TEST(FpAbstraction, refuted_candidate_is_accepted_when_the_formula_holds_anyway)
{
  const bool repair[] = {true, false};
  for (bool r : repair)
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_width = 4;
    mgr.UserFlags.fp_abstraction_repair = r;
    // No significand bands: the first candidate's surrogate is then never
    // the exact product by chance, so the candidate is always refuted.
    mgr.UserFlags.fp_abstraction_significand_bits = 0;
    mgr.UserFlags.check_counterexample_flag = true;
    const SourceSort format = SourceSort::floatingPoint(8, 24);
    const ASTNode x = mgr.CreateSourceSymbol("mr_x", format);
    const ASTNode y = mgr.CreateSourceSymbol("mr_y", format);
    const ASTNode z = mgr.CreateSourceSymbol("mr_z", format);
    const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode xy = mgr.CreateTerm(FP_MUL, 32, ASTVec{rne, x, y});
    // For finite x and y and a z that is not NaN, one of t < z and z <= t
    // holds whatever the product is: the claim holds of the exact product
    // whatever the surrogate said, and no box arithmetic sees it.
    // The factors are held in intervals no identity rule pins, so the
    // candidate's surrogate is not the product.
    const ASTNode formula = conj(
        mgr, {mgr.CreateNode(FP_LT, fpConst(mgr, 8, 24, 0x3f8ccccd), x), // 1.1
              mgr.CreateNode(FP_LT, x, fpConst(mgr, 8, 24, 0x3f99999a)), // 1.2
              mgr.CreateNode(FP_LT, fpConst(mgr, 8, 24, 0x3fa66666), y), // 1.3
              mgr.CreateNode(FP_LT, y, fpConst(mgr, 8, 24, 0x3fb33333)), // 1.4
              mgr.CreateNode(NOT, mgr.CreateNode(FP_ISNAN, z)),
              mgr.CreateNode(OR, mgr.CreateNode(FP_LT, xy, z),
                             mgr.CreateNode(FP_LEQ, z, xy))});
    STP solver(&mgr);
    EXPECT_EQ(SOLVER_INVALID, solver.TopLevelSTP(formula, mgr.ASTFalse));
    ASSERT_TRUE(mgr.getFpAbstractionIfAny() != NULL);
    const FpAbstractionStatistics& st = mgr.getFpAbstractionIfAny()->statistics();
    if (r)
    {
      // The first candidate is refuted and repaired: nothing refined.
      EXPECT_EQ(1u, st.inconsistent);
      EXPECT_EQ(1u, st.repairs);
      EXPECT_EQ(0u, st.rounds);
      EXPECT_EQ(0u, st.releases);
    }
    else
    {
      // Refined until a candidate is exact. How many candidates that takes
      // is the SAT solver's (one under CaDiCaL, five under CryptoMiniSat).
      EXPECT_EQ(0u, st.repairs);
      EXPECT_GE(st.inconsistent, 1u);
      EXPECT_GE(st.rounds, 1u);
    }
  }
}

// The restart guard: not past the limit, and not after a run that met
// nothing it released.
TEST(FpAbstraction, restart_is_refused_past_the_limit_and_without_progress)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  mgr.UserFlags.fp_abstraction_width = 4;
  mgr.UserFlags.fp_abstraction_restart_limit = 2;
  const SourceSort format = SourceSort::floatingPoint(11, 53);
  const ASTNode x = mgr.CreateSourceSymbol("rg_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("rg_y", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode formula =
      mgr.CreateNode(FP_ISNORMAL, mgr.CreateTerm(FP_MUL, 64, ASTVec{rne, x, y}));
  {
    FpAbstraction fresh(&mgr);
    EXPECT_TRUE(fresh.restartAllowed());
  }
  {
    FpAbstraction atLimit(&mgr, std::set<ASTNode>(), 2, 1);
    EXPECT_FALSE(atLimit.restartAllowed());
  }
  {
    // One restart so far, after a run of two records: this run's one is
    // progress.
    FpAbstraction progressed(&mgr, std::set<ASTNode>(), 1, 2);
    progressed.abstract(formula);
    ASSERT_TRUE(progressed.active());
    EXPECT_TRUE(progressed.restartAllowed());
  }
  {
    // One restart, after a run of one record: this run's one is none.
    FpAbstraction stuck(&mgr, std::set<ASTNode>(), 1, 1);
    stuck.abstract(formula);
    ASSERT_TRUE(stuck.active());
    EXPECT_FALSE(stuck.restartAllowed());
  }
}

TEST(FpAbstraction, fma_is_abstracted_as_a_link_in_a_chain)
{
  STPMgr mgr;
  mgr.UserFlags.fp_abstraction = true;
  const SourceSort format = SourceSort::floatingPoint(8, 24);
  const ASTNode x = mgr.CreateSourceSymbol("ch_x", format);
  const ASTNode y = mgr.CreateSourceSymbol("ch_y", format);
  const ASTNode z = mgr.CreateSourceSymbol("ch_z", format);
  const ASTNode w = mgr.CreateSourceSymbol("ch_w", format);
  const ASTNode rne = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode xy = mgr.CreateTerm(FP_MUL, 32, ASTVec{rne, x, y});
  // Over the product's result: a link in a chain. Over inputs alone: not.
  const ASTNode chainedFma = mgr.CreateTerm(FP_FMA, 32, ASTVec{rne, xy, z, w});
  const ASTNode plainFma = mgr.CreateTerm(FP_FMA, 32, ASTVec{rne, x, z, w});
  const ASTNode formula =
      conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                 mgr.CreateNode(FP_LT, chainedFma, plainFma)});
  {
    // By default the fma is abstracted wherever it stands.
    FpAbstraction abs(&mgr);
    abs.abstract(formula);
    ASSERT_TRUE(abs.active());
    EXPECT_EQ(3u, abs.applications().size());
    EXPECT_EQ(0u, abs.statistics().chained);
  }
  mgr.UserFlags.fp_abstraction_ops =
      FP_ABSTRACT_MUL | FP_ABSTRACT_DIV | FP_ABSTRACT_SQRT;
  mgr.UserFlags.fp_abstraction_chain_ops = FP_ABSTRACT_FMA;
  {
    // As a chain operation: the one over the product's result only.
    FpAbstraction abs(&mgr);
    abs.abstract(formula);
    ASSERT_TRUE(abs.active());
    ASSERT_EQ(2u, abs.applications().size());
    EXPECT_EQ(1u, abs.statistics().chained);
    EXPECT_EQ(FP_MUL, abs.applications()[0]->kind);
    EXPECT_EQ(FP_FMA, abs.applications()[1]->kind);
    // The chained fma's product operand is the product's surrogate view,
    // and its symbol in lemmas is the product's surrogate.
    EXPECT_EQ(abs.applications()[0]->surrogateView,
              abs.applications()[1]->children[1]);
    EXPECT_EQ(abs.applications()[0]->surrogate,
              abs.applications()[1]->proxies[1]);
  }
  {
    // Neither named nor a chain operation: the product alone.
    mgr.UserFlags.fp_abstraction_chain_ops = 0;
    FpAbstraction abs(&mgr);
    abs.abstract(formula);
    ASSERT_EQ(1u, abs.applications().size());
    EXPECT_EQ(0u, abs.statistics().chained);
  }
  // And a chained record answers like the exact encoding: in (3,4), over
  // normals, x*y*z + w is never NaN (an overflowed product gives an
  // infinity, and infinity plus a finite is that infinity) but can be
  // infinite.
  {
    STPMgr small;
    small.UserFlags.fp_abstraction = true;
    small.UserFlags.fp_abstraction_width = 4;
    small.UserFlags.fp_abstraction_ops =
        FP_ABSTRACT_MUL | FP_ABSTRACT_DIV | FP_ABSTRACT_SQRT;
    small.UserFlags.fp_abstraction_chain_ops = FP_ABSTRACT_FMA;
    const SourceSort tiny = SourceSort::floatingPoint(3, 4);
    const ASTNode a = small.CreateSourceSymbol("ch_a", tiny);
    const ASTNode b = small.CreateSourceSymbol("ch_b", tiny);
    const ASTNode c = small.CreateSourceSymbol("ch_c", tiny);
    const ASTNode d = small.CreateSourceSymbol("ch_d", tiny);
    const ASTNode rm = rmConst(small, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode ab = small.CreateTerm(FP_MUL, 7, ASTVec{rm, a, b});
    const ASTNode fma = small.CreateTerm(FP_FMA, 7, ASTVec{rm, ab, c, d});
    const ASTNode normals =
        conj(small, {small.CreateNode(FP_ISNORMAL, a),
                     small.CreateNode(FP_ISNORMAL, b),
                     small.CreateNode(FP_ISNORMAL, c),
                     small.CreateNode(FP_ISNORMAL, d)});
    expectParity(small,
                 conj(small, {normals, small.CreateNode(FP_ISNAN, fma)}),
                 SOLVER_VALID);
    expectParity(small,
                 conj(small, {normals, small.CreateNode(FP_ISINFINITE, fma)}),
                 SOLVER_INVALID);
  }
}

TEST(FpAbstraction, trailing_exponent_predicate_matches_the_concrete_definition)
{
  STPMgr mgr;
  const unsigned eb = 3, sb = 4, width = 7;
  for (unsigned bits = 0; bits < (1u << width); ++bits)
  {
    const ASTNode c = mgr.CreateBVConst(width, bits);
    const FpPackedValue v = decodeFpPackedValue(c, eb, sb);
    for (int64_t threshold = -8; threshold <= 6; ++threshold)
    {
      const ASTNode pred =
          NonMemberBVConstEvaluator(&mgr, fpRuleTrailingExponentAtLeast(
                                              &mgr, c, eb, sb, threshold));
      const bool expected =
          v.cls == FpPackedValue::Zero ||
          ((v.cls == FpPackedValue::Normal || v.cls == FpPackedValue::Subnormal) &&
           v.f >= threshold);
      ASSERT_TRUE(pred == mgr.ASTTrue || pred == mgr.ASTFalse)
          << bits << " " << threshold << " " << pred;
      EXPECT_EQ(expected, pred == mgr.ASTTrue) << bits << " f=" << v.f
                                               << " threshold=" << threshold;
    }
  }
}

TEST(FpAbstraction, trailing_exponent_predicate_handles_wide_signed_thresholds)
{
  const unsigned formats[][2] = {{11, 53}, {4, 63}, {4, 64}, {15, 113}};
  for (const unsigned* f : formats)
  {
    STPMgr mgr;
    const unsigned eb = f[0], sb = f[1], fw = sb - 1;
    const uint64_t bias = ((uint64_t)1 << (eb - 1)) - 1;
    const int64_t emin = 1 - (int64_t)bias, emax = (int64_t)bias;
    const ASTNode fractions[] = {
        mgr.CreateZeroConst(fw), mgr.CreateOneConst(fw),
        mgr.CreateMaxConst(fw),
        mgr.CreateBVConst(std::string("1") + std::string(fw - 1, '0'), 2, fw)};
    const uint64_t exponents[] = {0, 1, bias - 1, bias, 2 * bias, 2 * bias + 1};
    const int64_t thresholds[] = {emin - (int64_t)fw - 1, emin - (int64_t)fw,
                                  emin, -1, 0, 1, emax, emax + 1,
                                  std::numeric_limits<int64_t>::min(),
                                  std::numeric_limits<int64_t>::max()};
    for (unsigned sign = 0; sign < 2; ++sign)
      for (uint64_t exponent : exponents)
        for (const ASTNode& fraction : fractions)
        {
          const ASTNode bits = NonMemberBVConstEvaluator(
              &mgr, mgr.CreateTerm(
                        BVCONCAT, eb + sb, mgr.CreateBVConst(1, sign),
                        mgr.CreateTerm(BVCONCAT, eb + fw,
                                       mgr.CreateBVConst(eb, exponent), fraction)));
          const FpPackedValue v = decodeFpPackedValue(bits, eb, sb);
          for (int64_t threshold : thresholds)
          {
            const ASTNode pred = NonMemberBVConstEvaluator(
                &mgr, fpRuleTrailingExponentAtLeast(&mgr, bits, eb, sb, threshold));
            const bool expected =
                v.cls == FpPackedValue::Zero ||
                ((v.cls == FpPackedValue::Normal || v.cls == FpPackedValue::Subnormal) &&
                 v.f >= threshold);
            EXPECT_EQ(expected ? mgr.ASTTrue : mgr.ASTFalse, pred)
                << "eb=" << eb << " sb=" << sb << " bits=" << bits
                << " threshold=" << threshold;
          }
        }
  }
}

TEST(FpAbstraction, shape_lemmas_hold_against_exact_operation)
{
  std::set<FpRuleId> seen;
  const Kind kinds[] = {FP_MUL, FP_ADD, FP_SUB, FP_REM, FP_FMA};
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  for (Kind kind : kinds)
    for (unsigned mode : modes)
    {
      if (kind == FP_REM && mode != modes[0])
        continue;
      STPMgr mgr;
      RuleFixture f(mgr, kind, 3, 4, mode, "shape");
      // Every operand is 0.5. The candidate minimum subnormal violates
      // their common lattice; the resulting lemma generalises the tuple.
      const std::vector<ASTNode> values(f.context.bits.size(),
                                        mgr.CreateBVConst(7, 0x10));
      FpRuleId id;
      const ASTNode lemma = fpAbstractionShapeLemma(
          f.context, values, mgr.CreateBVConst(7, 1), &id);
      SCOPED_TRACE(fpRuleName(id));
      ASSERT_FALSE(lemma.IsNull());
      ASSERT_NE(FpRuleId::None, id);
      seen.insert(id);
      STP solver(&mgr);
      EXPECT_EQ(SOLVER_VALID,
                solver.TopLevelSTP(
                    conj(mgr, {f.definition, mgr.CreateNode(NOT, lemma)}),
                    mgr.ASTFalse));
      // Check exclusion separately from validity.
      ASTNodeMap substitutions, cache;
      for (size_t i = 0; i < values.size(); ++i)
        substitutions[f.context.bits[i]] = values[i];
      substitutions[f.context.tb] = mgr.CreateBVConst(7, 1);
      const ASTNode instance = SubstitutionMap::replace(
          lemma, substitutions, cache, mgr.defaultNodeFactory, false, false);
      EXPECT_EQ(mgr.ASTFalse, NonMemberBVConstEvaluator(&mgr, instance));
    }
  expectRuleCoverage(seen, "shapes");
}

TEST(FpAbstraction, binary128_shape_lemma_cuts_its_candidate)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateBVConst(
      std::string("3fff8000000000000000000000000000"), 16, 128); // 1.5
  const ASTNode t = mgr.CreateBVConst(
      std::string("40002000000000000000000000000001"), 16, 128); // nextUp(2.25)
  FpRuleContext c;
  c.bm = &mgr;
  c.kind = FP_MUL;
  c.eb = 15;
  c.sb = 113;
  c.rm = symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN;
  c.bits = {x, x};
  c.tb = t;
  const ASTNode lemma = fpAbstractionShapeLemma(c, {x, x}, t);
  ASSERT_FALSE(lemma.IsNull());
  EXPECT_EQ(mgr.ASTFalse, NonMemberBVConstEvaluator(&mgr, lemma));
}

namespace
{
struct CandidateFixture
{
  STPMgr mgr;
  SubstitutionMap substitutions{&mgr};
  Simplifier simplifier{&mgr, &substitutions};
  ArrayTransformer transformer{&mgr, &simplifier};
  FpEncodingContext encoding{&mgr};
  AbsRefine_CounterExample model{&mgr, &simplifier, &transformer};
  FpAbstraction abstraction{&mgr};

  CandidateFixture()
  {
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_width = 4;
    mgr.UserFlags.fp_abstraction_tiers = 0;
    mgr.UserFlags.fp_abstraction_shape = false;
    mgr.UserFlags.fp_abstraction_relational = false;
    mgr.UserFlags.fp_abstraction_budget = 0;
    model.setFpEncodingContext(&encoding);
  }

  const FpAbstraction::Application& division(uint64_t x, uint64_t y, uint64_t t)
  {
    const SourceSort format = SourceSort::floatingPoint(5, 11);
    const ASTNode sx = mgr.CreateSourceSymbol("repair_x", format);
    const ASTNode sy = mgr.CreateSourceSymbol("repair_y", format);
    const ASTNode rm = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode div = mgr.CreateTerm(FP_DIV, 16, ASTVec{rm, sx, sy});
    abstraction.abstract(mgr.CreateNode(FP_ISNORMAL, div));
    const auto& app = *abstraction.applications().at(0);
    model.InsertIntoCounterExampleMap(sx, mgr.CreateBVConst(16, x));
    model.InsertIntoCounterExampleMap(sy, mgr.CreateBVConst(16, y));
    model.InsertIntoCounterExampleMap(app.proxies[1], mgr.CreateBVConst(16, x));
    model.InsertIntoCounterExampleMap(app.proxies[2], mgr.CreateBVConst(16, y));
    model.InsertIntoCounterExampleMap(app.surrogate, mgr.CreateBVConst(16, t));
    return app;
  }

  const FpAbstraction::Application& operation(
      Kind kind, unsigned eb, unsigned sb, unsigned mode,
      const std::vector<uint64_t>& operands, uint64_t result,
      bool symbolicMode = false)
  {
    mgr.UserFlags.fp_abstraction_ops = 1023;
    const SourceSort format = SourceSort::floatingPoint(eb, sb);
    ASTVec children, values;
    if (kind != FP_REM)
    {
      children.push_back(symbolicMode
                             ? mgr.CreateSourceSymbol("box_rm", SourceSort::roundingMode())
                             : rmConst(mgr, mode));
      values.push_back(mgr.CreateBVConst(5, mode));
    }
    for (size_t i = 0; i < operands.size(); ++i)
    {
      children.push_back(mgr.CreateSourceSymbol(
          ("box_arg_" + std::to_string(i)).c_str(), format));
      values.push_back(mgr.CreateBVConst(eb + sb, operands[i]));
    }
    const ASTNode op = mgr.CreateTerm(kind, eb + sb, children);
    abstraction.abstract(mgr.CreateNode(FP_ISNORMAL, op));
    const auto& app = *abstraction.applications().at(0);
    for (size_t i = 0; i < children.size(); ++i)
      if (!children[i].isConstant())
      {
        model.InsertIntoCounterExampleMap(children[i], values[i]);
        model.InsertIntoCounterExampleMap(app.proxies[i], values[i]);
      }
    model.InsertIntoCounterExampleMap(app.surrogate,
                                     mgr.CreateBVConst(eb + sb, result));
    return app;
  }
};
} // namespace

TEST(FpAbstraction, remainder_box_counterexample_uses_only_a_value_lemma)
{
  CandidateFixture f;
  f.mgr.UserFlags.fp_abstraction_box_lemmas = true;
  const auto& app = f.operation(FP_REM, 8, 24, 0,
                                {0x791b0000, 0x3fd90000}, 0x3ed80000);
  ASSERT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
  ASSERT_EQ(1u, f.abstraction.pendingLemmas().size());
  EXPECT_EQ(1u, f.abstraction.statistics().valueLemmas);
  EXPECT_EQ(0u, f.abstraction.statistics().boxLemmas);
  // These operands are inside the old corner box, but their exact remainder
  // has a different prefix. The valid value lemma must preserve this model.
  f.model.ClearCounterExampleMap();
  f.model.ClearComputeFormulaMap();
  const uint64_t witness[] = {0x791b3fff, 0x3fd90000};
  for (size_t i = 0; i < 2; ++i)
    f.model.InsertIntoCounterExampleMap(app.proxies[i], f.mgr.CreateBVConst(32, witness[i]));
  f.model.InsertIntoCounterExampleMap(app.surrogate, f.mgr.CreateBVConst(32, 0x3ed80000));
  for (const ASTNode& lemma : f.abstraction.pendingLemmas())
    EXPECT_EQ(f.mgr.ASTTrue, f.model.ModelValueOfFormula(lemma));
}

// Verify the actual emitted implications against exact symbolic circuits,
// not against the corner evaluator that constructed them. Symbolic modes
// check that widening retains the mode guard; both output signs are covered.
TEST(FpAbstraction, operand_boxes_hold_against_exact_circuits)
{
  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY,
                            symbolic_fp::ROUND_TOWARD_POSITIVE,
                            symbolic_fp::ROUND_TOWARD_NEGATIVE,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  struct Case { Kind kind; std::vector<uint64_t> operands; };
  // Format (3,15): 1.5, 1.25 and 0.5, with room for the 12-bit prefix
  // and interior tuples that are not corners of its fraction box.
  const Case cases[] = {{FP_MUL, {0xe000, 0xd000}},
                        {FP_DIV, {0xe000, 0xd000}},
                        {FP_SQRT, {0xe000}},
                        {FP_ADD, {0xe000, 0xd000}},
                        {FP_SUB, {0xe000, 0x8000}},
                        {FP_FMA, {0xe000, 0xd000, 0x8000}},
                        {FP_ROUNDTOINTEGRAL, {0xe000}}};
  for (const Case& c : cases)
    for (unsigned mode : modes)
      for (bool negative : {false, true})
      {
        if (negative && c.kind == FP_SQRT)
          continue;
        SCOPED_TRACE(::testing::Message() << c.kind << " mode=" << mode
                                          << " negative=" << negative);
        CandidateFixture f;
        f.mgr.UserFlags.fp_abstraction_box_lemmas = true;
        std::vector<uint64_t> operands = c.operands;
        // Avoid straddling a result-prefix boundary through cancellation,
        // where the correct behavior would be to omit the optional box.
        operands[0] += 12;
        if (negative)
          operands[0] |= 1u << 17;
        const auto& app = f.operation(c.kind, 3, 15, mode, operands, 0, true);
        ASSERT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
        ASSERT_EQ(1u, f.abstraction.statistics().boxLemmas);
        ASSERT_EQ(2u, f.abstraction.pendingLemmas().size());
        const ASTNode exact = f.mgr.CreateNode(
            FP_SMT_EQ, app.surrogateView,
            f.mgr.CreateTerm(c.kind, 18, app.proxyViews));
        ASSERT_EQ((std::vector<FpRuleId>{FpRuleId::REF_V1, FpRuleId::REF_B1}),
                  f.abstraction.pendingRuleIds());
        SCOPED_TRACE(fpRuleName(f.abstraction.pendingRuleIds().back()));
        const ASTNode box = f.abstraction.pendingLemmas().back();
        EXPECT_EQ(SOLVER_VALID,
                  solve(f.mgr, conj(f.mgr, {exact, f.mgr.CreateNode(NOT, box)}), false));
      }
}

TEST(FpAbstraction, operand_box_rejects_a_zero_divisor_endpoint)
{
  CandidateFixture f;
  f.mgr.UserFlags.fp_abstraction_box_lemmas = true;
  f.operation(FP_DIV, 3, 15, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN, {1, 1}, 0);
  ASSERT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
  EXPECT_EQ(0u, f.abstraction.statistics().boxLemmas);
  EXPECT_EQ(1u, f.abstraction.statistics().valueLemmas);
}

TEST(FpAbstraction, repair_discards_pending_releases_without_marking_exact)
{
  for (bool restart : {false, true})
  {
    CandidateFixture f;
    f.mgr.UserFlags.fp_abstraction_values = 0;
    f.mgr.UserFlags.fp_abstraction_restart_width = restart ? 4 : 0;
    const auto& app = f.division(0x3c00, 0x4000, 0x3c00); // 1/2 != 1
    const auto conflict = restart ? FpAbstraction::Outcome::Restart
                                  : FpAbstraction::Outcome::Conflict;
    ASSERT_EQ(conflict, f.abstraction.checkCandidate(f.model));
    EXPECT_TRUE(app.releasePending);
    EXPECT_FALSE(app.released);
    f.abstraction.acceptRepairedCandidate();
    EXPECT_TRUE(f.abstraction.pendingRuleIds().empty());
    EXPECT_FALSE(app.releasePending);
    EXPECT_FALSE(app.released);
    EXPECT_FALSE(f.abstraction.hasPendingLemma());
    EXPECT_FALSE(f.abstraction.restartRequested());
    EXPECT_EQ(0u, f.abstraction.statistics().releases);
    f.abstraction.beginQuery();
    EXPECT_EQ(conflict, f.abstraction.checkCandidate(f.model));
  }
}

TEST(FpAbstraction, committed_release_replays_with_fresh_symbol_bindings)
{
  CandidateFixture f;
  f.mgr.UserFlags.fp_abstraction_values = 0;
  f.abstraction.forbidRestarts();
  f.abstraction.useBitPreciseEqualities();
  const auto& app = f.division(0x3c00, 0x4000, 0x3c00); // 1/2 != 1
  ASSERT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
  ASSERT_TRUE(app.releasePending);
  ASSERT_EQ(std::vector<FpRuleId>{FpRuleId::REF_E1},
            f.abstraction.pendingRuleIds());
  SCOPED_TRACE(fpRuleName(f.abstraction.pendingRuleIds().front()));
  for (unsigned epoch = 0; epoch < 2; ++epoch)
  {
    std::unique_ptr<SATSolver> solver(createSATSolver(f.mgr.UserFlags));
    ToSATAIG tosat(&f.mgr, &f.transformer, false);
    ASSERT_TRUE(solver->supportsAssumptions());
    // Give the second backend different variable numbers, as a real
    // rebuild does; replay must bind the symbols through its new live map.
    for (unsigned i = 0; i < epoch * 9; ++i)
      solver->newVar();
    auto& live = tosat.SATVar_to_SymbolIndexMap();
    for (const ASTNode& s : f.abstraction.protectedSymbols())
      for (unsigned i = 0; i < s.GetValueWidth(); ++i)
      {
        const unsigned v = solver->newVar();
        solver->setFrozen(v);
        live[s].push_back(v);
      }
    if (epoch == 0)
      f.abstraction.encodePendingLemmas(*solver, &tosat);
    else
    {
      f.abstraction.resetForNewSolverEpoch();
      ASSERT_TRUE(f.abstraction.hasUnassertedFacts());
      ASSERT_EQ(std::vector<FpRuleId>{FpRuleId::REF_E1},
                f.abstraction.committedRuleIds());
      EXPECT_TRUE(f.abstraction.pendingRuleIds().empty());
      ASSERT_TRUE(app.released);
      f.abstraction.syncPermanentFacts(*solver, &tosat);
    }
    ASSERT_EQ(std::vector<FpRuleId>{FpRuleId::REF_E1},
              f.abstraction.committedRuleIds());
    EXPECT_TRUE(f.abstraction.pendingRuleIds().empty());
    ASSERT_TRUE(app.released);
    ASSERT_FALSE(app.releasePending);
    ASSERT_FALSE(f.abstraction.hasUnassertedFacts());
    const auto permits = [&](unsigned x, unsigned y, unsigned t) {
      SATSolver::vec_literals assumptions;
      const ASTNode symbols[] = {app.proxies[1], app.proxies[2], app.surrogate};
      const unsigned values[] = {x, y, t};
      for (unsigned j = 0; j < 3; ++j)
        for (unsigned i = 0; i < 16; ++i)
          assumptions.push(SATSolver::mkLit(live.at(symbols[j])[i],
                                            ((values[j] >> i) & 1) == 0));
      bool timeout = false;
      const bool sat = solver->solveWithAssumptions(assumptions, timeout);
      EXPECT_FALSE(timeout);
      return sat;
    };
    EXPECT_FALSE(permits(0x3c00, 0x4000, 0x3c00));
    EXPECT_TRUE(permits(0x3c00, 0x4000, 0x3800));
    // Retracting the former operand assumptions must leave only the
    // operation's equation, with no stale operand values pinned in it.
    EXPECT_FALSE(permits(0x3c00, 0x3c00, 0x3800));
    EXPECT_TRUE(permits(0x3c00, 0x3c00, 0x3c00));
  }
}

TEST(FpAbstraction, repair_restores_discarded_value_budgets)
{
  CandidateFixture f;
  f.mgr.UserFlags.fp_abstraction_values = 1;
  const auto& app = f.division(0x3c00, 0x4000, 0x3c00);
  ASSERT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
  ASSERT_EQ(1u, app.valueLemmas);
  EXPECT_EQ(std::vector<FpRuleId>{FpRuleId::REF_V1},
            f.abstraction.pendingRuleIds());
  f.abstraction.acceptRepairedCandidate();
  EXPECT_TRUE(f.abstraction.pendingRuleIds().empty());
  EXPECT_EQ(0u, app.valueLemmas);
  EXPECT_EQ(0u, f.abstraction.statistics().valueLemmas);
  // No beginQuery: the transaction itself, not the next query, restores it.
  EXPECT_EQ(FpAbstraction::Outcome::Conflict, f.abstraction.checkCandidate(f.model));
  EXPECT_EQ(1u, app.valueLemmas);
  EXPECT_FALSE(app.releasePending);
}

TEST(FpAbstraction, nan_value_lemma_uses_the_candidate_check_equality)
{
  for (bool bitPrecise : {false, true})
  {
    CandidateFixture f;
    f.mgr.UserFlags.fp_abstraction_values = 1;
    if (bitPrecise)
      f.abstraction.useBitPreciseEqualities();
    // Exact 0/0 is the circuit's canonical NaN, not this payload.
    const auto& app = f.division(0, 0, 0x7e01);
    const auto expected = bitPrecise ? FpAbstraction::Outcome::Conflict
                                    : FpAbstraction::Outcome::Consistent;
    EXPECT_EQ(expected, f.abstraction.checkCandidate(f.model));
    // A bit-precise value lemma must cut; falling through to release is
    // safe but would conceal a still-incorrect NaN-class value lemma.
    EXPECT_EQ(bitPrecise ? 1u : 0u, app.valueLemmas);
    EXPECT_FALSE(app.releasePending);
  }
}

TEST(FpAbstraction, incremental_repair_does_not_forget_an_unasserted_release)
{
  for (bool repair : {false, true})
  {
    STPMgr mgr;
    mgr.UserFlags.fp_abstraction = true;
    mgr.UserFlags.fp_abstraction_incremental = true;
    mgr.UserFlags.fp_abstraction_tiers = 0;
    mgr.UserFlags.fp_abstraction_shape = false;
    mgr.UserFlags.fp_abstraction_relational = false;
    mgr.UserFlags.fp_abstraction_values = 0;
    mgr.UserFlags.fp_abstraction_repair = repair;
    SubstitutionMap substitutions(&mgr);
    Simplifier simplifier(&mgr, &substitutions);
    ArrayTransformer transformer(&mgr, &simplifier);
    AbsRefine_CounterExample ce(&mgr, &simplifier, &transformer);
    IncrementalSolver inc(&mgr, &ce, &simplifier, &transformer);
    const ASTNode x = mgr.CreateSourceSymbol("incremental_repair_x",
                                            SourceSort::floatingPoint(5, 11));
    const ASTNode rm = rmConst(mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
    const ASTNode t = mgr.CreateTerm(FP_DIV, 16, ASTVec{rm, x, x});
    const ASTNode base = conj(mgr, {mgr.CreateNode(FP_ISNORMAL, x),
                                    mgr.CreateNode(FP_ISNORMAL, t)});
    const ASTNode wrong = mgr.CreateNode(
        NOT, mgr.CreateNode(FP_SMT_EQ, t, fpConst(mgr, 5, 11, 0x3c00)));
    ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(ASTVec{base}));
    EXPECT_EQ(SOLVER_UNSATISFIABLE, inc.checkSat(ASTVec{base, wrong}));
    EXPECT_EQ(SOLVER_SATISFIABLE, inc.checkSat(ASTVec{base}));
    EXPECT_EQ(SOLVER_UNSATISFIABLE, inc.checkSat(ASTVec{base, wrong}));
  }
}

TEST(FpAbstraction, nan_operand_value_lemma_pins_the_class_in_the_semantic_host)
{
  // mul(NaN, 1) is NaN and the candidate says 1. Under SMT-LIB equality
  // the operand's proxy may carry any payload, so the value lemma must cut
  // the same tuple with another payload as well; a bit-precise host defines
  // its proxies bit-for-bit and pins the payload it saw.
  for (bool bitPrecise : {false, true})
  {
    CandidateFixture f;
    if (bitPrecise)
      f.abstraction.useBitPreciseEqualities();
    const auto& app = f.operation(FP_MUL, 5, 11,
                                  symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                                  {0x7e01, 0x3c00}, 0x3c00);
    ASSERT_EQ(FpAbstraction::Outcome::Conflict,
              f.abstraction.checkCandidate(f.model));
    ASSERT_EQ(1u, f.abstraction.pendingLemmas().size());
    ASSERT_EQ(FpRuleId::REF_V1, f.abstraction.pendingRuleIds().at(0));
    const ASTNode lemma = f.abstraction.pendingLemmas().at(0);
    EXPECT_EQ(f.mgr.ASTFalse, f.model.ModelValueOfFormula(lemma));
    // The same tuple and result, with another NaN payload in the operand.
    // The model map refuses overwrites, so it is rebuilt.
    f.model.ClearCounterExampleMap();
    f.model.ClearComputeFormulaMap();
    f.model.InsertIntoCounterExampleMap(app.children[1],
                                        f.mgr.CreateBVConst(16, 0x7f55));
    f.model.InsertIntoCounterExampleMap(app.proxies[1],
                                        f.mgr.CreateBVConst(16, 0x7f55));
    f.model.InsertIntoCounterExampleMap(app.children[2],
                                        f.mgr.CreateBVConst(16, 0x3c00));
    f.model.InsertIntoCounterExampleMap(app.proxies[2],
                                        f.mgr.CreateBVConst(16, 0x3c00));
    f.model.InsertIntoCounterExampleMap(app.surrogate,
                                        f.mgr.CreateBVConst(16, 0x3c00));
    EXPECT_EQ(bitPrecise ? f.mgr.ASTTrue : f.mgr.ASTFalse,
              f.model.ModelValueOfFormula(lemma));
  }
}

TEST(FpAbstraction, invalid_mode_candidate_is_skipped_not_evaluated)
{
  // Only a popped unit's unconstrained mode proxy can hold a pattern that
  // is not a rounding-mode encoding; such a record is outside the active
  // closure, so the check neither evaluates nor refines it.
  for (unsigned pattern : {0u, 3u, 31u})
  {
    CandidateFixture f;
    f.abstraction.useBitPreciseEqualities();
    const auto& app = f.operation(FP_DIV, 5, 11, pattern, {0x3c00, 0x3c00},
                                  0x0000, true);
    EXPECT_EQ(FpAbstraction::Outcome::Consistent,
              f.abstraction.checkCandidate(f.model));
    EXPECT_EQ(1u, f.abstraction.statistics().skippedChecks);
    EXPECT_EQ(0u, f.abstraction.statistics().checks);
    EXPECT_EQ(0u, app.valueLemmas);
    EXPECT_FALSE(app.releasePending);
    EXPECT_TRUE(f.abstraction.pendingLemmas().empty());
  }
}

TEST(FpAbstraction, active_closure_filter_reads_only_armed_records)
{
  // Two records in one abstraction. With a closure holding only the first
  // armed, the second stands for a popped unit's record: it is neither read
  // nor refined, and its wrong surrogate does not disturb the verdict.
  // Disarmed, it is read and refuted as before.
  CandidateFixture f;
  f.mgr.UserFlags.fp_abstraction_ops = 1023;
  const SourceSort format = SourceSort::floatingPoint(5, 11);
  const ASTNode a = f.mgr.CreateSourceSymbol("closure_a", format);
  const ASTNode b = f.mgr.CreateSourceSymbol("closure_b", format);
  const ASTNode c = f.mgr.CreateSourceSymbol("closure_c", format);
  const ASTNode d = f.mgr.CreateSourceSymbol("closure_d", format);
  const ASTNode rm = rmConst(f.mgr, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode mul = f.mgr.CreateTerm(FP_MUL, 16, ASTVec{rm, a, b});
  const ASTNode div = f.mgr.CreateTerm(FP_DIV, 16, ASTVec{rm, c, d});
  f.abstraction.abstract(conj(f.mgr, {f.mgr.CreateNode(FP_ISNORMAL, mul),
                                      f.mgr.CreateNode(FP_ISNORMAL, div)}));
  ASSERT_EQ(2u, f.abstraction.applications().size());
  const auto& first = *f.abstraction.applications().at(0);
  const auto& second = *f.abstraction.applications().at(1);
  const auto& mulApp = first.kind == FP_MUL ? first : second;
  const auto& divApp = first.kind == FP_MUL ? second : first;
  ASSERT_EQ(FP_DIV, divApp.kind);
  const ASTNode one = f.mgr.CreateBVConst(16, 0x3c00);
  const ASTNode zero = f.mgr.CreateBVConst(16, 0);
  for (const ASTNode& s : {a, b, c, d})
    f.model.InsertIntoCounterExampleMap(s, one);
  for (const auto* app : {&mulApp, &divApp})
    for (size_t i = 1; i < app->proxies.size(); ++i)
      f.model.InsertIntoCounterExampleMap(app->proxies[i], one);
  // 1 * 1 = 1 is right; 1 / 1 = 0 is wrong.
  f.model.InsertIntoCounterExampleMap(mulApp.surrogate, one);
  f.model.InsertIntoCounterExampleMap(divApp.surrogate, zero);

  f.abstraction.setActiveClosure({mulApp.surrogate});
  EXPECT_EQ(FpAbstraction::Outcome::Consistent,
            f.abstraction.checkCandidate(f.model));
  EXPECT_EQ(1u, f.abstraction.statistics().checks);
  EXPECT_EQ(1u, f.abstraction.statistics().skippedChecks);
  EXPECT_EQ(1u, f.abstraction.statistics().inactiveSkips);
  EXPECT_EQ(0u, divApp.valueLemmas);
  EXPECT_TRUE(f.abstraction.pendingLemmas().empty());

  f.abstraction.disarmActiveClosure();
  EXPECT_EQ(FpAbstraction::Outcome::Conflict,
            f.abstraction.checkCandidate(f.model));
  EXPECT_EQ(3u, f.abstraction.statistics().checks);
  EXPECT_EQ(1u, divApp.valueLemmas);
}

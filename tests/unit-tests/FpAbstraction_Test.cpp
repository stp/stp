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

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpAbstractionRules.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"

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

} // namespace

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

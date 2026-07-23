/***********
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
**********************/

/*
 * Tests for Simplifier::SimplifyAndOrFormula (reached via SimplifyFormula on
 * boolean AND/OR/NOT inputs).
 *
 * The bulk of these are FIRING tests: each feeds a formula that a specific
 * simplification must transform, and asserts the concrete result. They are
 * written so that turning SimplifyAndOrFormula (or SimplifyNotFormula's
 * pushNeg handling) into a no-op makes them fail -- the inputs are built with
 * the hashing factory, so nothing simplifies them unless the pass does.
 *
 * checkFires() makes the "did something" explicit: the output must differ
 * from the input. Alongside these, a few soundness/idempotence checks and a
 * deterministic fuzzer guard the invariants that any future change to the
 * pass (e.g. taming the pushNeg re-simplification) must preserve:
 *   - soundness: the output is logically equivalent to the input;
 *   - idempotence: re-simplifying the output changes nothing.
 *
 * The Simplifier itself runs with the simplifying factory, as in the real
 * pipeline.
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <random>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: what the pass itself uses.
  NodeFactory* hf; // hashing factory: builds inputs without pre-simplifying.
  unsigned counter = 0;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    nf = &snf;
    hf = mgr.hashingNodeFactory;
  }

  ASTNode boolean()
  {
    return mgr.CreateSymbol(("b" + std::to_string(counter++)).c_str(), 0, 0);
  }

  // Formula builders (hashing factory: no pre-simplification, so the shape
  // the pass sees is exactly what we asked for).
  ASTNode Not(const ASTNode& a) { return hf->CreateNode(NOT, a); }
  ASTNode And(const ASTVec& c) { return hf->CreateNode(AND, c); }
  ASTNode Or(const ASTVec& c) { return hf->CreateNode(OR, c); }
  ASTNode And(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(AND, a, b);
  }
  ASTNode Or(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(OR, a, b);
  }

  // Run the real top-level formula simplifier.
  ASTNode run(const ASTNode& f)
  {
    SubstitutionMap sm(&mgr);
    Simplifier simp(&mgr, &sm);
    return simp.SimplifyFormula_TopLevel(f, false);
  }

  // A firing check: the pass must both produce `expected` AND change the
  // input. If SimplifyAndOrFormula were a no-op, `run(input)` would equal
  // `input`, so the EXPECT_NE fails.
  void checkFires(const ASTNode& input, const ASTNode& expected)
  {
    ASTNode out = run(input);
    EXPECT_EQ(out, expected) << "input:    " << input << "\nexpected: "
                             << expected << "\ngot:      " << out;
    EXPECT_NE(out, input) << "expected a simplification to fire on " << input;
  }

  void collectSymbols(const ASTNode& n, ASTNodeSet& out)
  {
    if (n.GetKind() == SYMBOL)
    {
      out.insert(n);
      return;
    }
    for (const auto& c : n)
      collectSymbols(c, out);
  }

  // Directly evaluate a ground boolean formula (AND/OR/NOT/TRUE/FALSE over
  // the assigned symbols). Simpler and more robust than round-tripping
  // through the bit-vector constant evaluator, which doesn't handle boolean
  // connectives.
  bool evalBool(const ASTNode& n, const std::map<ASTNode, bool>& asgn)
  {
    switch (n.GetKind())
    {
      case TRUE:
        return true;
      case FALSE:
        return false;
      case SYMBOL:
        return asgn.at(n);
      case NOT:
        return !evalBool(n[0], asgn);
      case AND:
        for (const auto& ch : n)
          if (!evalBool(ch, asgn))
            return false;
        return true;
      case OR:
        for (const auto& ch : n)
          if (evalBool(ch, asgn))
            return true;
        return false;
      default:
        ADD_FAILURE() << "evalBool: unexpected kind in boolean formula: " << n;
        return false;
    }
  }

  void checkEquivalent(const ASTNode& before, const ASTNode& after)
  {
    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());
    ASSERT_LE(syms.size(), 16u) << "too many variables to enumerate";

    const unsigned long combos = 1UL << syms.size();
    for (unsigned long c = 0; c < combos; c++)
    {
      std::map<ASTNode, bool> asgn;
      for (size_t i = 0; i < syms.size(); i++)
        asgn[syms[i]] = ((c >> i) & 1) != 0;
      ASSERT_EQ(evalBool(before, asgn), evalBool(after, asgn))
          << "meaning changed at assignment " << c << "\nbefore: " << before
          << "\nafter:  " << after;
    }
  }

  void checkSound(const ASTNode& f) { checkEquivalent(f, run(f)); }

  void checkIdempotent(const ASTNode& f)
  {
    ASTNode once = run(f);
    ASTNode twice = run(once);
    ASSERT_EQ(once, twice) << "not idempotent\ninput: " << f
                           << "\nonce:  " << once << "\ntwice: " << twice;
  }
};

/*===========================================================================
 * FIRING TESTS -- each fails if SimplifyAndOrFormula becomes a no-op.
 *=========================================================================*/

// child == FALSE annihilates an AND.
TEST(SimplifyAndOr, and_false_child_gives_false)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.And(a, c.mgr.ASTFalse), c.mgr.ASTFalse);
}

// child == TRUE annihilates an OR.
TEST(SimplifyAndOr, or_true_child_gives_true)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.Or(a, c.mgr.ASTTrue), c.mgr.ASTTrue);
}

// TRUE is the identity of AND and is dropped.
TEST(SimplifyAndOr, and_drops_true)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.And(a, c.mgr.ASTTrue), a);
}

// FALSE is the identity of OR and is dropped.
TEST(SimplifyAndOr, or_drops_false)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.Or(a, c.mgr.ASTFalse), a);
}

// Duplicate operands collapse.
TEST(SimplifyAndOr, and_dedups)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.And(a, a), a);
}

TEST(SimplifyAndOr, or_dedups)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.Or(a, a), a);
}

// x AND NOT x is a contradiction.
TEST(SimplifyAndOr, and_x_notx_is_false)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.And(a, c.Not(a)), c.mgr.ASTFalse);
}

// x OR NOT x is a tautology.
TEST(SimplifyAndOr, or_x_notx_is_true)
{
  Context c;
  ASTNode a = c.boolean();
  c.checkFires(c.Or(a, c.Not(a)), c.mgr.ASTTrue);
}

// Nested same-kind operators are flattened into one wide node.
TEST(SimplifyAndOr, and_flattens)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean();
  ASTNode nested = c.And(a, c.And(b, d)); // (and a (and b d))
  ASTNode out = c.run(nested);
  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_EQ(out.Degree(), 3u) << "nested AND was not flattened: " << out;
  EXPECT_NE(out, nested);
}

// De Morgan: NOT over an AND pushes the negation down to an OR. This is the
// pushNeg path -- a no-op there leaves the node as NOT(AND(...)).
TEST(SimplifyAndOr, not_and_becomes_or_demorgan)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Not(c.And(a, b));
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), OR) << "De Morgan did not fire: " << out;
  EXPECT_NE(out, input);
  c.checkEquivalent(input, out);
}

// De Morgan the other way: NOT over an OR becomes an AND.
TEST(SimplifyAndOr, not_or_becomes_and_demorgan)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Not(c.Or(a, b));
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), AND) << "De Morgan did not fire: " << out;
  EXPECT_NE(out, input);
  c.checkEquivalent(input, out);
}

/*===========================================================================
 * DRAMATIC COLLAPSES -- large formulas that reduce to a constant or a single
 * leaf. These show the pass doing real work: flattening pulls a buried
 * complement/annihilator up to where the AND/OR rules can collapse the whole
 * structure.
 *=========================================================================*/

// Left-nested chain (and v0 (and v1 (and ... (and v_{n-1} tail)))).
static ASTNode nestChain(Context& c, Kind k, const std::vector<ASTNode>& vs,
                         const ASTNode& tail)
{
  ASTNode acc = tail;
  for (size_t i = vs.size(); i-- > 0;)
    acc = c.hf->CreateNode(k, vs[i], acc);
  return acc;
}

// A deeply nested AND whose innermost operand is the complement of the
// outermost: (and a (and b (and c (and d (and e (not a)))))) -> FALSE.
// Flattening brings `a` and `not a` together; the contradiction collapses
// eight nested nodes to a single constant.
TEST(SimplifyAndOr, deep_and_buried_complement_is_false)
{
  Context c;
  std::vector<ASTNode> vs;
  for (int i = 0; i < 6; i++)
    vs.push_back(c.boolean());
  ASTNode f = nestChain(c, AND, vs, c.Not(vs[0]));
  c.checkFires(f, c.mgr.ASTFalse);
  c.checkSound(f);
}

// The OR dual: a buried tautology collapses everything to TRUE.
TEST(SimplifyAndOr, deep_or_buried_complement_is_true)
{
  Context c;
  std::vector<ASTNode> vs;
  for (int i = 0; i < 6; i++)
    vs.push_back(c.boolean());
  ASTNode f = nestChain(c, OR, vs, c.Not(vs[0]));
  c.checkFires(f, c.mgr.ASTTrue);
  c.checkSound(f);
}

// A balanced AND-tree with one complement buried in a far leaf:
// ((a & b) & (c & d)) & ((e & f) & (g & (not a)))  -> FALSE.
TEST(SimplifyAndOr, balanced_and_tree_complement_is_false)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean(), e = c.boolean();
  ASTNode g = c.boolean(), h = c.boolean(), i = c.boolean();
  ASTNode left = c.And(c.And(a, b), c.And(d, e));
  ASTNode right = c.And(c.And(g, h), c.And(i, c.Not(a)));
  ASTNode f = c.And(left, right);
  c.checkFires(f, c.mgr.ASTFalse);
  c.checkSound(f);
}

// Collapses to a single variable through nested contradiction/annihilator:
//   (and (or x (and y (not y))) (or x TRUE))
//     (and y (not y)) = FALSE ; (or x FALSE) = x ; (or x TRUE) = TRUE ;
//     (and x TRUE) = x.
TEST(SimplifyAndOr, nested_collapse_to_single_variable)
{
  Context c;
  ASTNode x = c.boolean(), y = c.boolean();
  ASTNode f = c.And(c.Or(x, c.And(y, c.Not(y))), c.Or(x, c.mgr.ASTTrue));
  c.checkFires(f, x);
  c.checkSound(f);
}

// The same variable repeated across nesting collapses to one occurrence:
//   (and a (and b (and a (and c a)))) -> (and a b c).
TEST(SimplifyAndOr, repeated_variable_across_nesting_dedups)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean();
  ASTNode f = c.And(a, c.And(b, c.And(a, c.And(d, a))));
  ASTNode out = c.run(f);
  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_EQ(out.Degree(), 3u) << "duplicates not removed: " << out;
  EXPECT_NE(out, f);
  c.checkSound(f);
}

// pushNeg path: NOT of a tautology collapses to FALSE.
//   not(or x (not x)) -> FALSE.
TEST(SimplifyAndOr, not_of_tautology_is_false)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Not(c.Or(x, c.Not(x))), c.mgr.ASTFalse);
}

// A big De Morgan cascade collapses under a top negation:
//   not( (not a) & (not b) & (not c) & a )  -- the AND is a contradiction
//   (a and not a), so the AND is FALSE and its negation is TRUE.
TEST(SimplifyAndOr, not_of_contradiction_is_true)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean();
  ASTNode inner = c.And({c.Not(a), c.Not(b), c.Not(d), a});
  c.checkFires(c.Not(inner), c.mgr.ASTTrue);
}

/*===========================================================================
 * SOUNDNESS / IDEMPOTENCE -- invariants a future change must preserve.
 *=========================================================================*/

TEST(SimplifyAndOr, double_negation_sound)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode f = c.Not(c.Not(c.And(a, b)));
  c.checkSound(f);
  c.checkIdempotent(f);
}

// The deeply nested NOT/AND/OR shape that makes the pass expensive.
TEST(SimplifyAndOr, nested_not_and_or_sound)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean(), e = c.boolean();
  ASTNode f = c.Not(c.And(c.Not(c.And(a, b)), c.Not(c.Or(d, e))));
  c.checkSound(f);
  c.checkIdempotent(f);
}

// Deterministic fuzz over nested NOT/AND/OR formulas.
struct Fuzzer
{
  Context& c;
  std::mt19937 rng;
  std::vector<ASTNode> vars;

  Fuzzer(Context& ctx, unsigned seed, unsigned numVars) : c(ctx), rng(seed)
  {
    for (unsigned i = 0; i < numVars; i++)
      vars.push_back(c.boolean());
  }

  ASTNode gen(unsigned depth)
  {
    std::uniform_int_distribution<int> pick(0, depth == 0 ? 2 : 6);
    switch (pick(rng))
    {
      case 0:
        return vars[std::uniform_int_distribution<size_t>(0, vars.size() - 1)(
            rng)];
      case 1:
        return c.mgr.ASTTrue;
      case 2:
        return c.mgr.ASTFalse;
      case 3:
        return c.Not(gen(depth - 1));
      default:
      {
        const Kind k = (pick(rng) & 1) ? AND : OR;
        const int arity = std::uniform_int_distribution<int>(2, 3)(rng);
        ASTVec children;
        for (int i = 0; i < arity; i++)
          children.push_back(gen(depth - 1));
        return c.hf->CreateNode(k, children);
      }
    }
  }
};

TEST(SimplifyAndOr, fuzz_sound_and_idempotent)
{
  Context c;
  Fuzzer f(c, /*seed=*/0xC0FFEE, /*numVars=*/4);
  for (int i = 0; i < 400; i++)
  {
    ASTNode formula = f.gen(/*depth=*/4);
    c.checkSound(formula);
    c.checkIdempotent(formula);
  }
}

} // namespace

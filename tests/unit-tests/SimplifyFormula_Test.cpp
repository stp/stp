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
  ASTNode Xor(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(XOR, a, b);
  }
  ASTNode Nand(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(NAND, a, b);
  }
  ASTNode Nor(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(NOR, a, b);
  }
  ASTNode Iff(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(IFF, a, b);
  }
  ASTNode Implies(const ASTNode& a, const ASTNode& b)
  {
    return hf->CreateNode(IMPLIES, a, b);
  }
  ASTNode Ite(const ASTNode& a, const ASTNode& b, const ASTNode& d)
  {
    return hf->CreateNode(ITE, a, b, d);
  }

  // Run the real top-level formula simplifier.
  ASTNode run(const ASTNode& f)
  {
    SubstitutionMap sm(&mgr);
    Simplifier simp(&mgr, &sm);
    return simp.SimplifyFormula_TopLevel(f, false);
  }

  // ... and with the negation the caller wants pushed inwards. Half of the
  // pass's memo key, and the half every arm chooses per operand: this is the
  // entry the arms below are exercised through in both polarities.
  ASTNode runNeg(const ASTNode& f)
  {
    SubstitutionMap sm(&mgr);
    Simplifier simp(&mgr, &sm);
    return simp.SimplifyFormula_TopLevel(f, true);
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
      case NAND:
        for (const auto& ch : n)
          if (!evalBool(ch, asgn))
            return true;
        return false;
      case NOR:
        for (const auto& ch : n)
          if (evalBool(ch, asgn))
            return false;
        return true;
      case XOR:
      {
        bool odd = false;
        for (const auto& ch : n)
          odd ^= evalBool(ch, asgn);
        return odd;
      }
      case IFF:
        return evalBool(n[0], asgn) == evalBool(n[1], asgn);
      case IMPLIES:
        return !evalBool(n[0], asgn) || evalBool(n[1], asgn);
      case ITE:
        return evalBool(n[0], asgn) ? evalBool(n[1], asgn)
                                    : evalBool(n[2], asgn);
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

    const uint64_t combos = UINT64_C(1) << syms.size();
    for (uint64_t c = 0; c < combos; c++)
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

  // Under pushNeg the pass is simplifying NOT(f), so the answer must mean the
  // opposite of the input at every assignment.
  void checkSoundNegated(const ASTNode& f)
  {
    const ASTNode out = runNeg(f);

    ASTNodeSet symSet;
    collectSymbols(f, symSet);
    collectSymbols(out, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());
    ASSERT_LE(syms.size(), 16u) << "too many variables to enumerate";

    const uint64_t combos = UINT64_C(1) << syms.size();
    for (uint64_t c = 0; c < combos; c++)
    {
      std::map<ASTNode, bool> asgn;
      for (size_t i = 0; i < syms.size(); i++)
        asgn[syms[i]] = ((c >> i) & 1) != 0;
      ASSERT_EQ(!evalBool(f, asgn), evalBool(out, asgn))
          << "pushNeg answer is not the negation, at assignment " << c
          << "\nbefore: " << f << "\nafter:  " << out;
    }
  }

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


// A deeply nested all-AND DAG with billions of root->leaf paths but only a
// handful of distinct nodes. Each level has one AND per node of the previous
// level, omitting that node, so every node is heavily shared. Built with the
// hashing factory (no flattening), this is a compact DAG whose tree expansion
// is enormous -- it checks that SimplifyAndOrFormula flattens DAG-aware (once
// per distinct node) rather than tree-expanding (which would never finish).
// Logically the whole thing is just the conjunction of all the variables.
TEST(SimplifyAndOr, deep_omit_one_and_dag)
{
  Context c;
  const int numVars = 20;
  const int numLevels = 7; // ~ 20 * 19^7 ~= 1.8e10 root->leaf paths

  std::vector<ASTNode> vars;
  for (int i = 0; i < numVars; i++)
    vars.push_back(c.boolean());

  std::vector<ASTNode> level = vars;
  for (int L = 0; L < numLevels; L++)
  {
    std::vector<ASTNode> next;
    for (size_t omit = 0; omit < level.size(); omit++)
    {
      ASTVec children;
      for (size_t j = 0; j < level.size(); j++)
        if (j != omit)
          children.push_back(level[j]);
      next.push_back(c.hf->CreateNode(AND, children));
    }
    level = next;
  }
  ASTNode top = c.hf->CreateNode(AND, ASTVec(level.begin(), level.end()));

  ASTNode out = c.run(top);
  // Flattening + dedup collapses the whole structure to AND(all variables).
  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_EQ(out.Degree(), static_cast<size_t>(numVars));
}


// As above, but every conjunction is expressed as NOT(OR(negated children)),
// so simplification must apply De Morgan (and eliminate double negations) at
// every one of the shared nodes to recover it. A billions-of-paths DAG that
// hammers the pushNeg path -- it must stay DAG-aware there too. Logically it
// is still just AND(all variables).
TEST(SimplifyAndOr, deep_omit_one_demorgan)
{
  Context c;
  const int numVars = 20;
  const int numLevels = 7; // ~ 20 * 19^7 ~= 1.8e10 root->leaf paths

  // AND(children) written as NOT(OR(!children)).
  auto andAsNotOr = [&](const ASTVec& children) {
    ASTVec negs;
    negs.reserve(children.size());
    for (const auto& ch : children)
      negs.push_back(c.hf->CreateNode(NOT, ch));
    return c.hf->CreateNode(NOT, c.hf->CreateNode(OR, negs));
  };

  std::vector<ASTNode> vars;
  for (int i = 0; i < numVars; i++)
    vars.push_back(c.boolean());

  std::vector<ASTNode> level = vars;
  for (int L = 0; L < numLevels; L++)
  {
    std::vector<ASTNode> next;
    for (size_t omit = 0; omit < level.size(); omit++)
    {
      ASTVec children;
      for (size_t j = 0; j < level.size(); j++)
        if (j != omit)
          children.push_back(level[j]);
      next.push_back(andAsNotOr(children));
    }
    level = next;
  }
  ASTNode top = andAsNotOr(ASTVec(level.begin(), level.end()));

  ASTNode out = c.run(top);
  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_EQ(out.Degree(), static_cast<size_t>(numVars));
}

/*===========================================================================
 * ARM TESTS
 *
 * SimplifyFormula used to dispatch to eight functions; each is now an arm of
 * one state machine, and the points where an arm used to call SimplifyFormula
 * are phases it has to resume at. The tests above reach two of those arms
 * (AND/OR and NOT); a fold that lost its resumption point in any of the other
 * six -- IFF's re-simplification of the side a constant left, ITE's of the
 * condition under (ite c false true) -- is invisible from here.
 *
 * So one test per arm, and each arm under both polarities, since pushNeg is
 * half the memo key and each arm chooses what to hand its operands.
 *=========================================================================*/

// IMPLIES, both polarities: SimplifyImpliesFormula.
TEST(SimplifyArms, implies_false_antecedent_is_true)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Implies(c.mgr.ASTFalse, x), c.mgr.ASTTrue);
}

TEST(SimplifyArms, implies_true_antecedent_is_consequent)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Implies(c.mgr.ASTTrue, x), x);
}

TEST(SimplifyArms, implies_same_is_true)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Implies(x, x), c.mgr.ASTTrue);
}

TEST(SimplifyArms, implies_negated_antecedent_becomes_or)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Implies(c.Not(a), b);
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), OR) << "the NOT was not absorbed: " << out;
  EXPECT_NE(out, input);
  c.checkEquivalent(input, out);
}

TEST(SimplifyArms, implies_pushneg_is_a_conjunction)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Implies(a, b);
  ASTNode out = c.runNeg(input);
  EXPECT_EQ(out.GetKind(), AND) << "NOT(a=>b) should be a conjunction: " << out;
  c.checkSoundNegated(input);
}

// IFF, including the fold that re-simplifies the surviving side negated.
TEST(SimplifyArms, iff_true_left_is_right)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(c.mgr.ASTTrue, x), x);
}

TEST(SimplifyArms, iff_true_right_is_left)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(x, c.mgr.ASTTrue), x);
}

TEST(SimplifyArms, iff_false_left_negates_right)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(c.mgr.ASTFalse, x), c.Not(x));
}

TEST(SimplifyArms, iff_false_right_negates_left)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(x, c.mgr.ASTFalse), c.Not(x));
}

// The fold is a second walk over the side that survived. Where that side is a
// compound the arm has already simplified at the opposite polarity, the walk
// answers from CheckSimplifyMap's second lookup -- the one that negates a
// pushNeg=false answer -- so what comes back is the negation wrapped around
// it rather than the De Morgan'd form. Recorded rather than asserted as
// desirable: the memo and that lookup are older than this state machine, and
// the arm behaved this way when it was SimplifyIffFormula.
TEST(SimplifyArms, iff_false_side_negates_the_survivor)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Iff(c.mgr.ASTFalse, c.And(a, b));
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), NOT) << "the survivor was not negated: " << out;
  c.checkEquivalent(input, out);
}

TEST(SimplifyArms, iff_same_is_true)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(x, x), c.mgr.ASTTrue);
}

TEST(SimplifyArms, iff_complement_is_false)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Iff(c.Not(x), x), c.mgr.ASTFalse);
}

TEST(SimplifyArms, iff_pushneg_sound)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  c.checkSoundNegated(c.Iff(a, b));
}

// The formula if-then-else, including its own fold.
TEST(SimplifyArms, ite_true_condition_is_then)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  c.checkFires(c.Ite(c.mgr.ASTTrue, a, b), a);
}

TEST(SimplifyArms, ite_false_condition_is_else)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  c.checkFires(c.Ite(c.mgr.ASTFalse, a, b), b);
}

TEST(SimplifyArms, ite_false_true_branches_negate_condition)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Ite(x, c.mgr.ASTFalse, c.mgr.ASTTrue), c.Not(x));
}

// ... by walking the condition again under pushNeg, which is why the arm
// folds rather than letting the factory build the NOT. A condition the arm
// has already simplified at pushNeg=false comes back through the same
// negating lookup as the IFF fold above, so the arm's comment about exposing
// more simplifications holds for a condition it has not seen before and not
// for one it has.
TEST(SimplifyArms, ite_false_true_negates_the_condition)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Ite(c.And(a, b), c.mgr.ASTFalse, c.mgr.ASTTrue);
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), NOT) << "the condition was not negated: " << out;
  c.checkEquivalent(input, out);
}

TEST(SimplifyArms, ite_pushneg_sound)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean();
  c.checkSoundNegated(c.Ite(a, b, d));
}

// XOR: SimplifyXorFormula, which under pushNeg negates its first operand.
TEST(SimplifyArms, xor_same_is_false)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Xor(x, x), c.mgr.ASTFalse);
}

TEST(SimplifyArms, xor_true_false_is_true)
{
  Context c;
  c.checkFires(c.Xor(c.mgr.ASTTrue, c.mgr.ASTFalse), c.mgr.ASTTrue);
}

TEST(SimplifyArms, xor_pushneg_sound)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  c.checkSoundNegated(c.Xor(a, b));
}

TEST(SimplifyArms, xor_nary_preserves_all_operands)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean(), d = c.boolean();
  ASTNode input = c.hf->CreateNode(XOR, ASTVec{a, b, d});
  ASTNode out = c.run(input);

  EXPECT_EQ(XOR, out.GetKind());
  EXPECT_EQ(3U, out.Degree());
  c.checkEquivalent(input, out);
  c.checkSoundNegated(input);
}

// NAND and NOR, whose implicit negation cancels with the caller's.
TEST(SimplifyArms, nand_of_true_is_the_negated_other)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Nand(c.mgr.ASTTrue, x), c.Not(x));
}

TEST(SimplifyArms, nor_of_false_is_the_negated_other)
{
  Context c;
  ASTNode x = c.boolean();
  c.checkFires(c.Nor(c.mgr.ASTFalse, x), c.Not(x));
}

TEST(SimplifyArms, nand_pushneg_is_the_conjunction)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode out = c.runNeg(c.Nand(a, b));
  EXPECT_EQ(out.GetKind(), AND) << "NOT(nand) should be the AND: " << out;
  c.checkSoundNegated(c.Nand(a, b));
}

TEST(SimplifyArms, nor_pushneg_is_the_disjunction)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode out = c.runNeg(c.Nor(a, b));
  EXPECT_EQ(out.GetKind(), OR) << "NOT(nor) should be the OR: " << out;
  c.checkSoundNegated(c.Nor(a, b));
}

// NOT: the arm counts the run above it and starts again from the parity.
TEST(SimplifyArms, not_run_of_three_is_one)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Not(c.Not(c.Not(c.And(a, b))));
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), OR) << "odd parity should De Morgan: " << out;
  c.checkEquivalent(input, out);
}

TEST(SimplifyArms, not_run_of_four_is_none)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode input = c.Not(c.Not(c.Not(c.Not(c.And(a, b)))));
  ASTNode out = c.run(input);
  EXPECT_EQ(out.GetKind(), AND) << "even parity should not De Morgan: " << out;
  c.checkEquivalent(input, out);
}

// Every arm, both polarities, on formulas that mix them.
struct AllKindsFuzzer
{
  Context& c;
  std::mt19937 rng;
  std::vector<ASTNode> vars;

  AllKindsFuzzer(Context& ctx, unsigned seed, unsigned numVars)
      : c(ctx), rng(seed)
  {
    for (unsigned i = 0; i < numVars; i++)
      vars.push_back(c.boolean());
  }

  ASTNode gen(unsigned depth)
  {
    std::uniform_int_distribution<int> pick(0, depth == 0 ? 2 : 11);
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
      case 4:
        return c.And(gen(depth - 1), gen(depth - 1));
      case 5:
        return c.Or(gen(depth - 1), gen(depth - 1));
      case 6:
        return c.Xor(gen(depth - 1), gen(depth - 1));
      case 7:
        return c.Nand(gen(depth - 1), gen(depth - 1));
      case 8:
        return c.Nor(gen(depth - 1), gen(depth - 1));
      case 9:
        return c.Iff(gen(depth - 1), gen(depth - 1));
      case 10:
        return c.Implies(gen(depth - 1), gen(depth - 1));
      default:
        return c.Ite(gen(depth - 1), gen(depth - 1), gen(depth - 1));
    }
  }
};

TEST(SimplifyArms, fuzz_every_connective_sound_in_both_polarities)
{
  Context c;
  AllKindsFuzzer f(c, /*seed=*/0x5EED, /*numVars=*/4);
  for (int i = 0; i < 400; i++)
  {
    ASTNode formula = f.gen(/*depth=*/3);
    c.checkSound(formula);
    c.checkSoundNegated(formula);
  }
}

} // namespace

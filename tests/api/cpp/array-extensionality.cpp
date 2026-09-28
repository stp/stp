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

// array-extensionality.cpp -- whole-array equality (extensional arrays)
// through the 3.x API. An equality between two array terms remains an opaque
// equality until the complete query is lowered at solve time, and the
// lemmas-on-demand procedure then decides it. The option array-equality
// replaces the 2.x 'x' flag: `on` forces the procedure on, `auto` (the
// default) engages it when an array equality is built, and `off` refuses such
// an equality with UNSUPPORTED.
//
// Most cases pin a specific behaviour of the extensionality checker -- how
// many equality records a solve holds, whether a verdict came through its
// lemma path -- which has no public reading, so they reach the engine through
// api_engine.hpp. Everything else goes through the public API.

#include "api_engine.hpp"

#include "stp/Extensionality/ExtensionalityContext.h"

#include <cstdint>
#include <map>
#include <string>
#include <vector>

// The engine's headers bring stp::Kind into the global namespace, so the
// API's Kind is written stp::api::Kind here.
using namespace stp::api;

namespace
{

// The checker these regressions ran on: array equality forced on (the 2.x 'x'
// flag), and the counterexample of every satisfiable answer built and checked
// against the input. 2.x forced that check ('d') on every checker; 3.x leaves
// check-sanity off by default, so it is asked for here.
Options checker_options()
{
  Options o;
  o.set_str("array-equality", "on");
  o.set_bool("check-sanity", true);
  return o;
}

// A definitional top-level equality (a symbol equated with an array term)
// substitutes away before abstraction ever sees it. The cases that pin the
// abstraction/checker path itself keep the equality there.
void keep_array_definitions(Solver& s)
{
  s.options().set_bool("disable-equality", true);
  EXPECT_FALSE(api_test::engine_flags(s).propagate_equalities);
}

// The automatic policy finds a small query affordable and instantiates it
// eagerly, emitting no lemma and retiring its records as it goes. The cases
// that observe lemmas or records pin the refinement arm.
void pin_refinement_arm(Solver& s)
{
  s.options().set_uint("array-ackermann-budget", 0);
  EXPECT_EQ(0u, api_test::engine_flags(s).array_eager_budget);
}

} // namespace

TEST(array_extensionality, positive_equality_unsat)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term i = tm.declare("i", bv4);

  // Publicly this remains equality, and internally ARRAY_EQ preserves both
  // operands until solve-boundary lowering.
  const Term eq = a == b;
  ASSERT_EQ(stp::api::Kind::EQUAL, eq.kind());
  ASSERT_EQ(stp::ARRAY_EQ, api_test::engine_node(eq).GetKind());

  // Repeated requests reuse the same proxy, in either operand order,
  // and a reflexive equality folds to true.
  ASSERT_EQ(eq.id(), (a == b).id());
  ASSERT_EQ(eq.id(), (b == a).id());
  ASSERT_TRUE((a == a).same_as(tm.mk_true()));

  s.add(eq);
  s.add(!(a[i] == b[i]));

  // a = b and a[i] != b[i]: unsat.
  ASSERT_TRUE(s.check_sat().is_unsat());
}

TEST(array_extensionality, disequality_sat_with_witness)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);

  s.add(!(a == b));

  // distinct arrays: satisfiable.
  ASSERT_TRUE(s.check_sat().is_sat());

  // The model exposes a concrete witness index where the two arrays differ:
  // a point both hold with different values, or -- zero-default completion --
  // a point one holds with a nonzero value that the other lacks.
  const Model m = s.model();
  const ArrayValue av = m.array_value(a), bv = m.array_value(b);
  EXPECT_EQ(0u, av.default_value().to_uint64());
  EXPECT_EQ(0u, bv.default_value().to_uint64());
  bool differ = false;
  for (const ArrayValue& side : {av, bv})
    for (const ArrayValue::Entry& e : side.entries())
      if (av.at(e.index).to_uint64() != bv.at(e.index).to_uint64())
        differ = true;
  ASSERT_TRUE(differ);
}

TEST(array_extensionality, write_congruence_unsat)
{
  // Equal writes at equal indices force equal values, with no explicit
  // read anywhere -- writes are treated as accesses.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
  const Term e1 = tm.declare("e1", bv8), e2 = tm.declare("e2", bv8);

  s.add(store(a, i, e1) == store(b, j, e2));
  s.add(i == j);
  s.add(!(e1 == e2));

  ASSERT_TRUE(s.check_sat().is_unsat());
}

TEST(array_extensionality, repeated_queries_do_not_leak_ite_records)
{
  // Regression for repeated solves over an array if-then-else: the
  // condition is UNRESOLVED, so simplification cannot fold the ITE
  // away and preparation must eliminate it into a fresh array with two
  // guarded equalities (paper section 4.1). The first solve creates
  // exactly the one user equality record plus those two; every
  // repeated solve reuses them through the persistent replacement
  // cache instead of minting a new generation. Both branches
  // contradict c, so the query is unsat only while both guarded
  // definitions are active -- a solve that lost either guard could
  // flip the verdict.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT);
  const Term p = tm.declare("p", tm.mk_bool_sort());
  const Term i = tm.declare("i", bv4);

  s.add(ite(p, a, b) == c);
  s.add(!(a[i] == c[i]));
  s.add(!(b[i] == c[i]));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  for (int solve = 0; solve < 4; solve++)
  {
    ASSERT_TRUE(s.check_sat().is_unsat()) << "solve " << solve;
    if (ext == nullptr)
      ext = bm.getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    // The user's equality and nothing else, on every solve. The
    // if-then-else is reasoned about directly by the checker's T rules,
    // so it costs one Boolean literal per solve rather than an array
    // variable, two equality records, two witness indices and four
    // virtual reads. Nothing accumulates because nothing is minted.
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }
}

TEST(array_extensionality, nested_ite_fixed_point_is_stable)
{
  // Nested array if-then-elses remain in the owned graph and are handled
  // directly by the T rules. They mint no equality records, and repeated
  // solves must rebuild the same one-record graph without accumulating
  // state.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT), d = tm.declare("d", arrT);
  const Term p = tm.declare("p", tm.mk_bool_sort());
  const Term q = tm.declare("q", tm.mk_bool_sort());
  const Term i = tm.declare("i", bv4);

  // (ite p (ite q a b) c) = d, with every leaf contradicting d at i:
  // unsat for all values of p and q.
  s.add(ite(p, ite(q, a, b), c) == d);
  for (const Term& leaf : {a, b, c})
    s.add(!(leaf[i] == d[i]));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  for (int solve = 0; solve < 3; solve++)
  {
    ASSERT_TRUE(s.check_sat().is_unsat()) << "solve " << solve;
    if (ext == nullptr)
      ext = bm.getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    // Both if-then-elses, nested, still cost no record at all.
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }
}

TEST(array_extensionality, second_solve_does_not_inherit_array_ite_state)
{
  // Two check-sat calls over Array (_ BitVec 10) (_ BitVec 1): the
  // first assumes an array equality whose right operand stacks writes
  // on an array-valued if-then-else, the second assumes that
  // if-then-else's own condition. Both are satisfiable.
  //
  // The old construction-time registry eliminated the if-then-else in the
  // first solve and cached its replacement. The second solve inherited that
  // replacement without a sound way to recover all of its defining guards;
  // model checking then failed while neither refinement path had a lemma to
  // add. The current design keeps the equality opaque through construction
  // and rebuilds all equality records and array-graph state from each solve's
  // completed root, so the second solve must inherit nothing.
  //
  // Found by fuzzing with murxla (--stp); delta-minimized.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv1 = tm.mk_bv_sort(1), bv10 = tm.mk_bv_sort(10);
  const Sort arrT = tm.mk_array_sort(bv10, bv1);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv10); // the chain's one symbolic index
  const Term v = tm.declare("v", bv1);  // and its one symbolic value
  const Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  const Term p = tm.mk_bv(10, 271), q = tm.mk_bv(10, 205), r = tm.mk_bv(10, 729);

  const Term base = store(a, p, v);
  // Signed 1-bit: bvsmod(v, v) is zero either way, so the condition
  // holds exactly when v is zero -- but nothing folds it away while
  // the query is being built.
  const Term cond = bvsle(bvsmod(v, v), v);
  Term chain = ite(cond, a, base);

  const Term writes[15][2] = {{i, v},    {i, v},    {q, v},    {p, v},
                              {r, zero}, {r, v},    {p, zero}, {p, v},
                              {q, v},    {i, v},    {r, v},    {i, v},
                              {q, v},    {i, v},    {p, one}};
  for (const auto& write : writes)
    chain = store(chain, write[0], write[1]);

  const Term eq = base == chain;
  ASSERT_EQ(stp::api::Kind::EQUAL, eq.kind());
  ASSERT_EQ(stp::ARRAY_EQ, api_test::engine_node(eq).GetKind());

  // A scope stands in for check-sat-assuming, as it did when this was
  // reduced: the assumption goes away with the pop, which is what makes
  // these two solves of two different formulas.
  s.push();
  s.add(eq);
  EXPECT_TRUE(s.check_sat().is_sat());
  s.pop();

  // The equality is out of the second formula. Its solve-local record and
  // graph must have been discarded rather than affecting this solve.
  s.push();
  s.add(cond);
  EXPECT_TRUE(s.check_sat().is_sat());
  s.pop();
}

TEST(array_extensionality, asserted_ite_condition_folds_before_fe03)
{
  // A condition asserted true, so preprocessing could fold ite(p,a,b)
  // to a. Section 4.1 elimination had to decide before that fold could
  // happen and charged two equality records for an if-then-else that
  // was about to disappear. Direct integration charges nothing either
  // way: the record count is the user's equality alone whether the
  // fold happens or not.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT);
  const Term p = tm.declare("p", tm.mk_bool_sort());
  const Term i = tm.declare("i", bv4);

  s.add(p);
  s.add(ite(p, a, b) == c);
  s.add(!(a[i] == c[i]));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  for (int solve = 0; solve < 2; solve++)
  {
    ASSERT_TRUE(s.check_sat().is_unsat()) << "solve " << solve;
    if (ext == nullptr)
      ext = bm.getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }
}

TEST(array_extensionality, preencoded_leaf_validation)
{
  // The lemma-leaf validator must reject every shape that would
  // otherwise make lemma encoding silently invent fresh, unconstrained
  // SAT variables for a term the candidate was never checked against.
  // The leaves are built through the API, on a manager that keeps every
  // term as built, and handed to the validator as the engine's nodes.
  TermManager tm = api_test::raw_manager();
  const Term s = tm.declare("s", tm.mk_bv_sort(4));
  const Term nine = tm.mk_bv(4, 9);
  const Term sum = bvadd(s, nine);

  const stp::ASTNode sym = api_test::engine_node(s);
  const stp::ASTNode cnst = api_test::engine_node(nine);
  const stp::ASTNode compound = api_test::engine_node(sum);
  ASSERT_EQ(stp::SYMBOL, sym.GetKind());
  ASSERT_EQ(stp::BVCONST, cnst.GetKind());
  ASSERT_EQ(stp::BVPLUS, compound.GetKind());

  stp::ToSATBase::ASTNodeToSATVar satVar;
  typedef stp::ExtensionalityContext EC;

  // constants need no encoding
  EXPECT_EQ(nullptr, EC::checkPreencodedBV(cnst, satVar));

  // a symbol with no SAT vector is an internal error, never a fresh
  // allocation
  EXPECT_NE(nullptr, EC::checkPreencodedBV(sym, satVar));

  // wrong-width vector
  satVar[sym] = std::vector<unsigned>(3, 7u);
  EXPECT_NE(nullptr, EC::checkPreencodedBV(sym, satVar));

  // full-width vector: valid
  satVar[sym] = std::vector<unsigned>(4, 7u);
  EXPECT_EQ(nullptr, EC::checkPreencodedBV(sym, satVar));

  // one unencoded-bit sentinel poisons the vector
  satVar[sym][2] = ~((unsigned)0);
  EXPECT_NE(nullptr, EC::checkPreencodedBV(sym, satVar));

  // compound terms are never legal lemma leaves
  EXPECT_NE(nullptr, EC::checkPreencodedBV(compound, satVar));
}

TEST(array_extensionality, array_model_entries_ascending)
{
  // The programmatic array model is deterministic -- one entry per
  // concrete index, ascending unsigned index order -- and stable
  // across repeated calls.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);

  // Observations at deliberately nonascending indices, plus a
  // disequality so a witness point is also published.
  const int idxs[] = {11, 3, 0, 7};
  for (int idx : idxs)
    s.add(a[tm.mk_bv(4, idx)] == tm.mk_bv(8, 16 + idx));
  s.add(!(a == b));

  ASSERT_TRUE(s.check_sat().is_sat());

  for (int round = 0; round < 2; round++)
  {
    const std::vector<ArrayValue::Entry> entries = s.model().array_value(a).entries();
    ASSERT_GE(entries.size(), 4u) << "round " << round;
    for (std::size_t x = 1; x < entries.size(); x++)
    {
      EXPECT_LT(entries[x - 1].index.to_uint64(), entries[x].index.to_uint64())
          << "round " << round << " position " << x;
    }
  }
}

TEST(array_extensionality, store_chain_equals_base_solved_by_rewrite)
{
  // An equality between a chain of writes and the chain's own base is
  // solved by rewriting into read equalities over the base: no
  // abstraction variable is minted, no record is created, and the
  // query never needs the refinement loop.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv4);
  const Term v = tm.declare("v", bv8);

  const Term eq = store(a, i, v) == a;
  // The node factory folds a single self-store to exactly
  // read(a, i) = v at creation, so no whole-array equality ever forms
  // and the extensionality context is never brought up.
  ASSERT_EQ(stp::api::Kind::EQUAL, eq.kind());
  ASSERT_EQ(stp::EQ, api_test::engine_node(eq).GetKind());

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  s.add(eq);
  s.add(!(a[i] == v));
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());
}

TEST(array_extensionality, store_chain_shadowed_write_is_unconstrained)
{
  // In store(store(a,i,w),i,v) = a the inner write is shadowed by the
  // outer write at the identical index term, so its value w is dropped
  // from the rewrite entirely: only read(a,i) = v is forced.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv4);
  const Term v = tm.declare("v", bv8), w = tm.declare("w", bv8);

  s.add(store(store(a, i, w), i, v) == a);
  s.add(!(w == a[i]));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  // w is unconstrained: satisfiable. (The factory collapses the shadowed
  // write and then folds the single self-store, so the extensionality
  // context is never brought up.)
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  // v is forced: contradicting read(a,i) = v flips the verdict.
  s.add(!(a[i] == v));
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());
}

TEST(array_extensionality, store_chain_guarded_inner_write)
{
  // With distinct index terms the inner write is guarded, not dropped:
  // store(store(a,j,w),i,v) = a forces read(a,j) = w whenever j != i.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
  const Term v = tm.declare("v", bv8), w = tm.declare("w", bv8);

  const Term eq = store(store(a, j, w), i, v) == a;
  // Two live writes are still one opaque equality here. Lowering rewrites it
  // to a conjunction whose inner conjunct is guarded by index equality.
  ASSERT_EQ(stp::api::Kind::EQUAL, eq.kind());
  ASSERT_EQ(stp::ARRAY_EQ, api_test::engine_node(eq).GetKind());

  s.add(eq);
  s.add(!(i == j));
  s.add(!(a[j] == w));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());
}

TEST(array_extensionality, store_chain_over_write_base)
{
  // The chain's base may itself be a write: hashing makes the two
  // occurrences of store(a,j,w) the same node, so the peel finds the
  // base one write down and the rewrite still applies.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
  const Term v = tm.declare("v", bv8), w = tm.declare("w", bv8);

  const Term b = store(a, j, w);
  s.add(store(b, i, v) == b);
  s.add(!(b[i] == v));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  // The factory's self-store fold applies whatever the base is -- here a
  // write -- so the extensionality context is never brought up.
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());
}

TEST(array_extensionality, lemma_atoms_fold_at_encoding)
{
  // Two write chains over the same base at provably distinct indices
  // (i and i+1), in swapped order, denied equal: unsatisfiable, and
  // only refinement lemmas can establish it. The write indices differ
  // by a constant offset from the same pointer, so the lemma encoder
  // decides those index comparisons from the defining terms instead
  // of building 32-bit equality circuits for the SAT solver to search
  // through.
  TermManager tm;
  Solver s(tm, checker_options());
  // Lemmas are the observation, so the refinement arm has to be the one
  // taken: the automatic policy would find a query this small affordable
  // and instantiate it eagerly instead, emitting none.
  pin_refinement_arm(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv32 = tm.mk_bv_sort(32);
  const Sort arrT = tm.mk_array_sort(bv32, bv8);

  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv32);
  Term idx[4];
  Term val[4];
  for (int k = 0; k < 4; k++)
  {
    idx[k] = bvadd(i, tm.mk_bv(32, k));
    val[k] = tm.declare("x" + std::to_string(k), bv8);
  }

  // The same four writes, applied in opposite orders.
  Term c1 = a;
  Term c2 = a;
  for (int k = 0; k < 4; k++)
  {
    c1 = store(c1, idx[k], val[k]);
    c2 = store(c2, idx[3 - k], val[3 - k]);
  }
  s.add(!(c1 == c2));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
  EXPECT_GT(ext->lemmaAtomsFolded, 0);
}

TEST(array_extensionality, equality_under_push_pops_away)
{
  // Activation follows the current assertion root. Popping the equality
  // removes its witness bundle from the next solve; reasserting the same
  // durable opaque term activates it again.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);
  // The record count is the observation, and the eager arm retires the
  // records as it instantiates them. Pin the refinement arm.
  pin_refinement_arm(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term zero = tm.mk_bv(4, 0);

  s.add(!(a[zero] == b[zero]));

  const stp::STPMgr& bm = api_test::engine_manager(tm);

  s.push();
  s.add(a == b);
  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  s.pop();
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(0u, ext->getActiveRecordCount());

  s.push();
  s.add(a == b);
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  s.pop();
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(0u, ext->getActiveRecordCount());
}

TEST(array_extensionality, equality_asserted_between_queries)
{
  // The first solve runs with an empty registry; the equality is
  // asserted only after its answer, and the second solve must
  // abstract, prepare, and refine it from scratch.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);

  s.add(i == j);
  s.add(!(a[i] == b[j]));
  ASSERT_TRUE(s.check_sat().is_sat()); // unrelated arrays differ

  s.add(a == b);
  ASSERT_TRUE(s.check_sat().is_unsat()); // congruence across a = b
}

TEST(array_extensionality, active_equalities_follow_assertions_and_query)
{
  TermManager tm;
  Solver s(tm, checker_options());
  // The record count is the observation, and the eager arm retires the
  // records as it instantiates them. Pin the refinement arm.
  pin_refinement_arm(s);

  const Sort bv1 = tm.mk_bv_sort(1);
  const Sort arrT = tm.mk_array_sort(bv1, bv1);
  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  const Term eq = a == b;

  s.add(a[zero] == b[zero]);
  s.add(a[one] == b[one]);

  const stp::STPMgr& bm = api_test::engine_manager(tm);

  // Merely retaining an opaque term neither creates a context nor activates
  // its witness bundle when it is absent from the completed solve root.
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(nullptr, bm.getExtensionalityIfAny());

  // The same term asked as an entailment is reachable through the negated
  // query. The complete one-bit domain makes the equality valid.
  ASSERT_TRUE(s.entails(eq).is_valid());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  // A later solve that omits the equality must not inherit its constraints.
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(0u, ext->getActiveRecordCount());
}

TEST(array_extensionality, opaque_equality_handle_uses_current_model_lowering)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv1 = tm.mk_bv_sort(1);
  const Sort arrT = tm.mk_array_sort(bv1, bv1);
  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term eq = a == b;

  s.push();
  s.add(eq);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(eq));
  s.pop();

  s.push();
  s.add(!eq);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(s.model().bool_value(eq));
  s.pop();
}

// An equality term the solve did not decide is answered from the model,
// not from an abstraction variable.
//
// Lowering can throw an equality away. Solving a write chain against
// its own base rewrites the equality instead of abstracting it, and
// drops the conjunct for a write an outer write to the same index
// shadows -- so an equality nested in that write's value goes with it.
// Its abstraction variable then enters no constraint and is never
// assigned, and reading the equality through it gave false, while the
// same model gave both arrays no cells at all and so printed them
// identically.
//
// Deciding it from the published cells cannot disagree with the model,
// because it is the model. Both arrays are unconstrained here, so both
// are the zero array, so they are equal.
TEST(array_extensionality, handle_for_a_discarded_equality_matches_the_model)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort idxT = tm.mk_bv_sort(3), elT = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(idxT, elT);
  const Term a = tm.declare("a", arrT);
  const Term p = tm.declare("p", arrT), q = tm.declare("q", arrT);
  const Term i = tm.declare("i", idxT), j = tm.declare("j", idxT);
  const Term v = tm.declare("v", elT), y = tm.declare("y", elT);

  const Term nested = p == q;
  const Term value = ite(nested, tm.mk_bv(4, 1), tm.mk_bv(4, 0));
  // store(store(store(a, i, value), j, y), i, v) = a. The outermost
  // write is to i as well, so the innermost write to i is shadowed and
  // its conjunct -- the only one mentioning `value` -- is dropped.
  Term chain = store(a, i, value);
  chain = store(chain, j, y);
  chain = store(chain, i, v);
  s.add(chain == a);

  ASSERT_TRUE(s.check_sat().is_sat());

  // Neither array carries a single cell, so the model makes them the
  // same array. Answering false here -- which is what an unassigned
  // abstraction variable produced -- contradicted the model in the same
  // breath as reporting it.
  const Model m = s.model();
  ASSERT_EQ(0u, m.array_value(p).size());
  ASSERT_EQ(0u, m.array_value(q).size());

  EXPECT_TRUE(m.bool_value(nested));
}

// The same invariant as handle_for_a_discarded_equality_matches_the_model,
// on the path that test now has to switch off: an equality with an
// unconstrained operand is settled by unconstrained elimination, which
// replaces it with a fresh boolean and defines the operand from it.
// Whatever that boolean comes out as, the arrays the model publishes
// have to say the same thing -- a reconstruction that forgot to make
// them differ in the false case, or that made them differ in the true
// case, would be reported here as a model contradicting itself.
// The equality was never part of any query. There is no lowering for it
// and never was, so this is the same path with no discarding involved:
// the answer still comes from the model, and still agrees with what the
// model says about the two arrays.
TEST(array_extensionality, handle_for_an_unasserted_equality_matches_the_model)
{
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort idxT = tm.mk_bv_sort(3), elT = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(idxT, elT);
  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term idx = tm.mk_bv(3, 1);

  // Only `a` is constrained, and only at one cell. `b` is untouched.
  s.add(a[idx] == tm.mk_bv(4, 5));
  ASSERT_TRUE(s.check_sat().is_sat());

  // a holds 5 at that cell and b completes to zero there, so they
  // differ -- and a equals itself whatever the model says.
  const Model m = s.model();
  const Term ab = a == b;
  EXPECT_FALSE(m.bool_value(ab));
  EXPECT_TRUE(m.bool_value(a == a));

  // Asking did not add cells to the model that the model API would
  // then report.
  EXPECT_EQ(0u, m.array_value(b).size());
}

// A cell no constraint ever mentioned is read while evaluating a
// lowering, and the value invented for it has to be the value the
// published model gives that cell.
//
// Every array equality here is a write chain against a base of its own
// chain, so lowering solves all six by rewriting: no abstraction
// variable, no record, no consistency checker behind any of them. They
// also sit in the untaken branch of an if-then-else whose condition is
// asserted, so preprocessing deletes them from the formula and the
// solver constrains none of the arrays -- yet the lowerings are still
// what the model answers an equality term with, and the post-solve
// audit compares each one against the contents the model publishes for
// its operands.
//
// The model completes an unobserved cell with zero: that is what the
// printer stores under the array, what Model::array_value reports, and
// what the checker compares contents with. Evaluation used to invent
// all-ones for such a cell instead, which made the lowering of
// store(store(x5,3,3), x6, x1) = store(x5,3,3) read false while the same
// model printed the two arrays identically. Found by fuzzing; the audit
// caught it and aborted a satisfiable query.
TEST(array_extensionality, unconstrained_cells_read_as_the_model_prints_them)
{
  TermManager tm;
  Solver s(tm, checker_options());
  // build the counterexample and audit it
  ASSERT_TRUE(s.options().get_bool("check-sanity"));

  const Sort bv3 = tm.mk_bv_sort(3);
  const Sort arrT = tm.mk_array_sort(bv3, bv3);

  const Term x1 = tm.declare("x1", bv3);
  const Term x2 = tm.declare("x2", tm.mk_bool_sort());
  const Term x5 = tm.declare("x5", arrT);
  const Term x6 = tm.declare("x6", bv3);
  const Term x8 = tm.declare("x8", bv3);
  const Term x9 = tm.declare("x9", bv3);
  const Term three = tm.mk_bv(3, 3);

  const Term c = store(x5, three, three);
  const Term a = store(c, x6, x1);
  const Term d = store(store(store(a, three, x1), x5[x1], three), x1, three);

  // (distinct a x5 c d): six pairs, each of them a write chain and a
  // base of that same chain.
  const Term operands[4] = {a, x5, c, d};
  std::vector<Term> pairs;
  for (int p = 0; p < 4; p++)
    for (int q = p + 1; q < 4; q++)
      pairs.push_back(!(operands[p] == operands[q]));
  ASSERT_EQ(6u, pairs.size());

  s.add(x2);
  s.add(!ite(x2, x8 == x9, and_(pairs)));

  // Satisfiable: x2 holds, so only x8 != x9 is required and the whole
  // distinct is dead.
  ASSERT_TRUE(s.check_sat().is_sat());

  // Nothing constrained x5, so the model prints it as the all-zero
  // array -- and a read of it must say zero too, at the index the
  // dropped equalities read it at.
  const Model m = s.model();
  EXPECT_EQ(0u, m.array_value(x5).size());
  EXPECT_EQ(0u, m.uint64_value(x5[x6]));

  // The equality terms agree with those contents in both directions:
  // store(x5,3,3) with a write of x1 at x6 on top is the same array when
  // x5 already holds x1 there, and neither is x5 itself, which holds
  // zero at index 3.
  EXPECT_TRUE(m.bool_value(a == c));
  EXPECT_FALSE(m.bool_value(a == x5));
  EXPECT_FALSE(m.bool_value(c == x5));
}

TEST(array_extensionality, active_checker_owns_complete_array_graph)
{
  // The contradiction lives in congruence across a = b, while unrelated
  // array c carries satisfiable constraints. Once the equality activates
  // the checker, both components belong to its complete graph; the unsat
  // verdict must come through its lemma path, pinned by the counter.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);
  // The verdict is pinned to the lemma path, so the refinement arm has to
  // be the one taken.
  pin_refinement_arm(s);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
  const Term k = tm.declare("k", bv4), l = tm.declare("l", bv4);

  s.add(a == b);
  s.add(i == j);
  s.add(!(a[i] == b[j]));
  s.add(c[k] == tm.mk_bv(8, 7));
  s.add(c[l] == tm.mk_bv(8, 9));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
}

TEST(array_extensionality, whole_graph_checker_publishes_mixed_sat_model)
{
  // v is forced to 42 through cross-array congruence over the true
  // equality and w to 5 through same-array congruence on disconnected c.
  // The concrete values pin complete-graph certification and publication,
  // not just the satisfiable verdict.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT);
  const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
  const Term k = tm.declare("k", bv4), l = tm.declare("l", bv4);
  const Term v = tm.declare("v", bv8), w = tm.declare("w", bv8);

  s.add(a == b);
  s.add(i == j);
  s.add(a[i] == tm.mk_bv(8, 42));
  s.add(b[j] == v);
  // Say k = l without a substitutable equality, so the two read
  // abstractions remain syntactically distinct until checker rule C.
  s.add(!bvult(k, l));
  s.add(!bvult(l, k));
  s.add(c[k] == tm.mk_bv(8, 5));
  s.add(c[l] == w);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(42u, m.uint64_value(v));
  EXPECT_EQ(5u, m.uint64_value(w));

  const ArrayValue cv = m.array_value(c);
  ASSERT_EQ(1u, cv.size());
  EXPECT_EQ(m.uint64_value(k), cv.entry(0).index.to_uint64());
  EXPECT_EQ(5u, cv.entry(0).element.to_uint64());
}

TEST(array_extensionality, flag_on_without_equalities_is_dormant)
{
  // With the option on but no array equality anywhere in the query,
  // the decision procedure must stay entirely dormant: no context is
  // ever created, and the solve is the option-off solve -- the same
  // verdict and the same model values, including for terms the
  // constraints leave free.
  std::uint64_t values[2][4];
  Verdict verdicts[2];
  std::map<std::uint64_t, std::uint64_t> entries[2];
  for (int flag = 0; flag < 2; flag++)
  {
    TermManager tm;
    Options o = checker_options();
    o.set_str("array-equality", flag ? "on" : "off");
    Solver s(tm, o);

    const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
    const Sort arrT = tm.mk_array_sort(bv4, bv8);

    const Term a = tm.declare("a", arrT);
    const Term i = tm.declare("i", bv4), j = tm.declare("j", bv4);
    const Term v = tm.declare("v", bv8);

    s.add(store(a, i, v)[j] == tm.mk_bv(8, 42));
    s.add(i == j);
    s.add(a[tm.mk_bv(4, 3)] == tm.mk_bv(8, 7));

    const Result r = s.check_sat();
    verdicts[flag] = r.verdict();
    // A model is read only after a satisfiable answer (anything else is
    // NO_MODEL), so the verdict is asserted before the model is read.
    ASSERT_TRUE(r.is_sat()) << "flag " << flag;
    const Model m = s.model();
    values[flag][0] = m.uint64_value(v);
    values[flag][1] = m.uint64_value(i);
    values[flag][2] = m.uint64_value(j);
    values[flag][3] = m.uint64_value(a[tm.mk_bv(4, 3)]);

    // Dormant array-model surface: with the option on but no equality
    // anywhere, the model's array entries come out of the sorted
    // extraction against a counterexample populated purely by classic
    // refinement. As a set of entries it must agree with the option-off
    // surface. (The API sorts every array value by index, so both are
    // ascending.)
    const std::vector<ArrayValue::Entry> es = m.array_value(a).entries();
    for (std::size_t x = 0; x < es.size(); x++)
    {
      entries[flag][es[x].index.to_uint64()] = es[x].element.to_uint64();
      if (x > 0)
      {
        EXPECT_LT(es[x - 1].index.to_uint64(), es[x].index.to_uint64());
      }
    }

    if (flag)
    {
      // No equality was ever abstracted, so no context exists at all.
      EXPECT_EQ(nullptr, api_test::engine_manager(tm).getExtensionalityIfAny());
    }
  }

  EXPECT_EQ(verdicts[0], verdicts[1]);
  EXPECT_EQ(Verdict::SAT, verdicts[0]);
  for (int k = 0; k < 4; k++)
  {
    EXPECT_EQ(values[0][k], values[1][k]) << "value " << k;
  }
  EXPECT_EQ(42u, values[0][0]);
  EXPECT_EQ(7u, values[0][3]);
  EXPECT_EQ(entries[0], entries[1]);
  EXPECT_EQ(1u, entries[0].count(3));
  EXPECT_EQ(7u, entries[0][3]);
}

TEST(array_extensionality, refinement_on_the_cadical_backend)
{
  // Refinement adds lemma clauses to the incremental solver over
  // variables it may already have eliminated; on the CaDiCaL backend
  // correctness rests on clause restoration (setFrozen is a
  // documented no-op there). A CaDiCaL upgrade with different restore
  // behavior would surface here, not in production. Skipped when the
  // backend is not compiled in.
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  TermManager tm;
  Options o = checker_options();
  // A backend is chosen at construction; one the build lacks is refused
  // there (OPTION_UNAVAILABLE), so a constructed solver runs on it.
  o.set_str("sat-backend", "cadical");
  Solver s(tm, o);
  ASSERT_EQ("cadical", s.options().get_str("sat-backend"));
  // Clause restoration is what is under test, so the round has to reach
  // refinement rather than be instantiated eagerly.
  pin_refinement_arm(s);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort arrT = tm.mk_array_sort(bv8, bv8);

  // The same two writes applied in opposite orders at provably
  // distinct indices: unsat, and only refinement lemmas can prove it.
  const Term a = tm.declare("a", arrT);
  const Term i = tm.declare("i", bv8);
  const Term i1 = bvadd(i, tm.mk_bv(8, 1));
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);

  const Term c1 = store(store(a, i, x), i1, y);
  const Term c2 = store(store(a, i1, y), i, x);
  s.add(!(c1 == c2));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ("cadical", s.statistics().str("sat.backend"));
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
}

TEST(array_extensionality, store_index_read_through_second_array_unsat)
{
  // Found by differential fuzzing (reported sat; the formula is
  // unsat). The store index k = x11[x9[x0]] reaches the equality
  // through a read of a second, unrelated array, and the asserted
  // x9[x0] = C lets preprocessing rewrite that read's index to the
  // constant C inside the recorded equality operand while the
  // original compound form survives in the rest of the formula. The
  // two occurrences of x11[C] were then abstracted as two independent
  // read variables outside the old equality cone. Certifying before
  // legacy refinement linked them let the consistency check place the
  // store and the read at different cells. Whole-graph ownership makes
  // their disagreement a checker conflict instead.
  //
  // Unsat by cases on x0 = k. If x0 = k, the equality forces
  // x9[x0] = x0, so x0 = C, and the assumed read of the overwrite
  // forces x0 = MIN, but C != MIN. If x0 != k, the equality forces
  // x9[x0] = x0 sdiv C, whose magnitude is at most |x0|/|C| < |C|,
  // so it can never equal C = x9[x0].
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort arrT = tm.mk_array_sort(bv8, bv8);

  const Term x0 = tm.declare("x0", bv8);
  const Term x5 = tm.declare("x5", arrT);
  const Term x9 = tm.declare("x9", arrT);
  const Term x11 = tm.declare("x11", arrT);
  const Term c = tm.mk_bv(8, 0x9C);    // -100
  const Term mins = tm.mk_bv(8, 0x80); // min signed

  const Term k = x11[x9[x0]];
  const Term q = bvsdiv(x0, c);

  s.add(x9[x0] == c);
  s.add(store(x9, x0, mins)[k] == x0);
  s.add(x9 == store(store(x5, x0, q), k, x0));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  // This input no longer reaches the divergence refusal it was reduced
  // from: constant bit propagation now writes every fully fixed node
  // back into the graph, not only the ones the top node does not depend
  // on, so both occurrences of x11[C] are rewritten alike and are
  // abstracted as one read. What is left here is the ordinary lemma
  // loop over the same formula, which still has to answer unsat.
  // unlinked_reads_are_owned_by_the_extensionality_checker covers the
  // formerly split ownership route directly.
}

TEST(array_extensionality, unlinked_reads_are_owned_by_the_extensionality_checker)
{
  // A regression built from the former name-divergence route rather
  // than reduced from a fuzz report.
  //
  // x11 is never equated to anything. Even so, an active equality solve
  // must put its reads in the same complete checker graph. i = j is said
  // as a pair of unsigned comparisons so that nothing substitutes one
  // index for the other and collapses x11[i] and x11[j] into a single
  // read. The recorded equality then stores at x11[i] while the read
  // goes through x11[j]: a candidate in which the two abstractions hold
  // different values must now be a rule-C conflict and produce an
  // extensionality lemma; it must never be handed to host refinement as
  // a scalar-name divergence.
  //
  // Unsat: i = j forces x11[i] = x11[j], so the read lands on the cell
  // the store just set to 1.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);
  // The conflict has to be raised as an extensionality lemma for the
  // ownership claim to mean anything, so pin the refinement arm.
  pin_refinement_arm(s);

  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort arrT = tm.mk_array_sort(bv8, bv8);

  const Term i = tm.declare("i", bv8), j = tm.declare("j", bv8);
  const Term x5 = tm.declare("x5", arrT);
  const Term x9 = tm.declare("x9", arrT);
  const Term x11 = tm.declare("x11", arrT);
  const Term one = tm.mk_bv(8, 1);

  s.add(!bvult(i, j));
  s.add(!bvult(j, i));

  s.add(x9 == store(x5, x11[i], one));
  s.add(!(x9[x11[j]] == one));

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_unsat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
}

TEST(array_extensionality, store_index_read_through_second_array_bv120_unsat)
{
  // The same defect as store_index_read_through_second_array_unsat,
  // as originally found: 120-bit words, and the contradictory
  // constraints arriving as assumptions inside a pushed scope. The
  // divisor's magnitude squared exceeds the signed range, so
  // x0 sdiv C = C has no solution, and C != MIN closes the x0 = k
  // case exactly as at width 8.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv120 = tm.mk_bv_sort(120);
  const Sort arrT = tm.mk_array_sort(bv120, bv120);

  const Term x0 = tm.declare("x0", bv120);
  const Term c = bvneg(tm.mk_bv(120, "36288689616474043440116267750740073", 10));
  const Term x5 = tm.declare("x5", arrT);
  const Term mins = tm.mk_bv_min_signed(120); // #b1 followed by 119 zeroes
  const Term x9 = tm.declare("x9", arrT);
  const Term x11 = tm.declare("x11", arrT);

  const Term t20 = bvsdiv(x0, c);
  const Term t21 = x9[x0];
  const Term t22 = x11[t21];
  const Term t73 = store(x9, x0, mins)[t22];
  const Term t84 = t73 == x0;
  const Term t111 = store(store(x5, x0, t20), t22, x0);
  const Term t132 = x9 == t111;
  const Term t134 = t21 == c;

  s.add(t134);

  // check-sat-assuming (t84 t132 t84 t84), as a scope of assertions
  s.push();
  s.add(t84);
  s.add(t132);
  s.add(t84);
  s.add(t84);
  ASSERT_TRUE(s.check_sat().is_unsat());
  s.pop();

  // The base assertion alone is satisfiable.
  ASSERT_TRUE(s.check_sat().is_sat());
}

TEST(array_extensionality, mixed_width_equality_dies_loudly)
{
  // An equality over arrays of different index widths cannot be
  // abstracted. It is refused at the public sort boundary rather than
  // built as a silently mistyped node that the solve would trip over
  // later. 2.x ended the process there; the API refuses the call with
  // a recoverable SORT_MISMATCH, and builds nothing.
  TermManager tm;
  Solver s(tm, checker_options());

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Term a = tm.declare("a", tm.mk_array_sort(bv4, bv8));
  const Term b = tm.declare("b", tm.mk_array_sort(bv8, bv8));

  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(a == b));
}

TEST(array_extensionality, flag_off_refuses_array_equality)
{
  // 2.x refused an equality between whole array terms unless the 'x' flag
  // was set, and the refusal ended the process. The API has no such gate:
  // under the default (array-equality = auto) the equality is built and
  // engages the procedure. The refusal is what array-equality = off asks
  // for, and it is a recoverable UNSUPPORTED at construction.
  {
    TermManager tm;
    Solver s(tm);
    const Sort arrT = tm.mk_array_sort(tm.mk_bv_sort(4), tm.mk_bv_sort(8));
    const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
    const Term eq = a == b;
    EXPECT_EQ(stp::api::Kind::EQUAL, eq.kind());
    EXPECT_EQ(stp::ARRAY_EQ, api_test::engine_node(eq).GetKind());
  }

  TermManager tm;
  Options o = checker_options();
  o.set_str("array-equality", "off");
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);

  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, (void)(a == b));

  // The check is specific to arrays: ordinary equality remains available
  // when the extension is switched off.
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term eq = x == y;
  EXPECT_EQ(stp::api::Kind::EQUAL, eq.kind());
}

TEST(array_extensionality, ite_replacement_survives_a_rewritten_condition)
{
  // Same property as repeated_queries_do_not_leak_ite_records above --
  // a repeated solve must not accumulate records for an if-then-else --
  // but with a condition preprocessing REWRITES.
  //
  // That is the difference between the two tests, and it is the whole
  // defect. Elimination runs after preprocessing, so it rebuilds the
  // if-then-else from an anchor the simplifier has already pushed the
  // read through, and keys the cache lookup on the *rewritten*
  // condition. Give preprocessing something to rewrite -- here
  // x <u 0x10 in the presence of x <u 0x08 -- and the lookup misses on
  // every later solve: a fresh array, two equality records, two witness
  // indices and four virtual reads leak per solve, and each is
  // re-conjoined into every solve after that. Solve cost becomes
  // quadratic in the number of solves.
  //
  // With the condition a plain Boolean symbol the lookup hits and the
  // count is stable, which is why the sibling test does not see it. The
  // unit tests cannot see it either: they drive preparation directly,
  // so no preprocessing runs between their two solves.
  //
  // Neither hazard exists now. There is no replacement, so there is no
  // key for a rewritten condition to miss: the if-then-else stays a
  // term and the checker reasons about it where it stands. The
  // condition being rewritten is exactly why it must be reified -- the
  // checker branches on the value the solver assigned to the name, not
  // on a re-reading of whatever the condition was normalised into.
  TermManager tm;
  Solver s(tm, checker_options());
  keep_array_definitions(s);
  // And for the same reason: all three arrays are used once, so
  // unconstrained elimination would collapse the if-then-else and then
  // the equality, minting no record for the checker to work on.
  s.options().set_bool("unconstrained-variable-elimination", false);
  EXPECT_FALSE(api_test::engine_flags(s).enable_unconstrained);

  const Sort bv8 = tm.mk_bv_sort(8), bv4 = tm.mk_bv_sort(4);
  const Sort arrT = tm.mk_array_sort(bv4, bv8);

  const Term a = tm.declare("a", arrT), b = tm.declare("b", arrT);
  const Term c = tm.declare("c", arrT);
  const Term x = tm.declare("x", bv8);

  // Undecided, so the if-then-else survives and must be eliminated,
  // but not a bare Boolean symbol either: preprocessing normalises the
  // comparison, and that rewritten form is what the rebuilt lookup key
  // is made of.
  const Term cond = bvult(x, tm.mk_bv(8, 0x10));
  s.add(ite(cond, a, b) == c);

  const stp::STPMgr& bm = api_test::engine_manager(tm);
  ASSERT_TRUE(s.check_sat().is_sat());
  stp::ExtensionalityContext* ext = bm.getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  // The user's equality, and nothing minted for the if-then-else.
  const std::size_t afterFirstSolve = ext->getRecords().size();
  EXPECT_EQ(1u, afterFirstSolve);

  // An assertion between the solves is what forces the second one to
  // prepare again rather than reuse the previous answer.
  const Term t = tm.declare("t", bv8);
  s.add(bvule(t, tm.mk_bv(8, 0xFE)));
  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(afterFirstSolve, ext->getRecords().size());
}

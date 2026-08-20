/***********
AUTHORS: Andrew Teylu

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

// C API front end for the array-equality feature: with the 'x' flag,
// vc_eqExpr over array operands remains an opaque equality until the complete
// query is lowered at solve time.  The lemmas-on-demand procedure then decides
// it; with the flag off, the pre-existing refusal behavior is preserved.

#include "stp/c_interface.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STP.h"
#include <gtest/gtest.h>
#include <map>

TEST(array_extensionality, positive_equality_unsat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);

  // Publicly this remains equality, and internally ARRAY_EQ preserves both
  // operands until solve-boundary lowering.
  Expr eq = vc_eqExpr(vc, a, b);
  ASSERT_EQ(EQ, getExprKind(eq));
  ASSERT_EQ(stp::ARRAY_EQ, static_cast<stp::ASTNode*>(eq)->GetKind());

  // Repeated requests reuse the same proxy, in either operand order,
  // and a reflexive equality folds to true.
  ASSERT_EQ(getExprID(eq), getExprID(vc_eqExpr(vc, a, b)));
  ASSERT_EQ(getExprID(eq), getExprID(vc_eqExpr(vc, b, a)));
  ASSERT_EQ(TRUE, getExprKind(vc_eqExpr(vc, a, a)));

  vc_assertFormula(vc, eq);
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                   vc_readExpr(vc, b, i))));

  // a = b and a[i] != b[i]: unsat, so FALSE is valid.
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

TEST(array_extensionality, disequality_sat_with_witness)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, a, b)));

  // distinct arrays: satisfiable, so FALSE is invalid.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The model exposes a concrete witness index where the two arrays
  // differ.
  Expr* aIdx;
  Expr* aVal;
  int aSize;
  vc_getCounterExampleArray(vc, a, &aIdx, &aVal, &aSize);
  Expr* bIdx;
  Expr* bVal;
  int bSize;
  vc_getCounterExampleArray(vc, b, &bIdx, &bVal, &bSize);

  bool differ = false;
  for (int x = 0; x < aSize && !differ; x++)
  {
    for (int y = 0; y < bSize; y++)
    {
      if (getBVUnsigned(aIdx[x]) == getBVUnsigned(bIdx[y]) &&
          getBVUnsigned(aVal[x]) != getBVUnsigned(bVal[y]))
      {
        differ = true;
        break;
      }
    }
  }
  // Zero-default completion: a point present in one model with a
  // nonzero value and absent from the other also distinguishes them.
  for (int x = 0; x < aSize && !differ; x++)
  {
    bool present = false;
    for (int y = 0; y < bSize; y++)
      if (getBVUnsigned(aIdx[x]) == getBVUnsigned(bIdx[y]))
        present = true;
    if (!present && getBVUnsigned(aVal[x]) != 0)
      differ = true;
  }
  for (int y = 0; y < bSize && !differ; y++)
  {
    bool present = false;
    for (int x = 0; x < aSize; x++)
      if (getBVUnsigned(aIdx[x]) == getBVUnsigned(bIdx[y]))
        present = true;
    if (!present && getBVUnsigned(bVal[y]) != 0)
      differ = true;
  }
  vc_deleteCounterExampleArray(aIdx, aVal, aSize);
  vc_deleteCounterExampleArray(bIdx, bVal, bSize);
  ASSERT_TRUE(differ);
  vc_Destroy(vc);
}

TEST(array_extensionality, write_congruence_unsat)
{
  // Equal writes at equal indices force equal values, with no explicit
  // read anywhere -- writes are treated as accesses.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);
  Expr e1 = vc_varExpr(vc, "e1", bv8);
  Expr e2 = vc_varExpr(vc, "e2", bv8);

  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_writeExpr(vc, a, i, e1), vc_writeExpr(vc, b, j, e2)));
  vc_assertFormula(vc, vc_eqExpr(vc, i, j));
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, e1, e2)));

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr p = vc_varExpr(vc, "p", vc_boolType(vc));
  Expr i = vc_varExpr(vc, "i", bv4);

  vc_assertFormula(vc, vc_eqExpr(vc, vc_iteExpr(vc, p, a, b), c));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                   vc_readExpr(vc, c, i))));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, b, i),
                                   vc_readExpr(vc, c, i))));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  for (int solve = 0; solve < 4; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
    if (ext == nullptr)
      ext = bm->getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    // The user's equality and nothing else, on every solve. The
    // if-then-else is reasoned about directly by the checker's T rules,
    // so it costs one Boolean literal per solve rather than an array
    // variable, two equality records, two witness indices and four
    // virtual reads. Nothing accumulates because nothing is minted.
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }

  vc_Destroy(vc);
}

TEST(array_extensionality, nested_ite_fixed_point_is_stable)
{
  // Nested array if-then-elses remain in the owned graph and are handled
  // directly by the T rules. They mint no equality records, and repeated
  // solves must rebuild the same one-record graph without accumulating
  // state.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr d = vc_varExpr(vc, "d", arrT);
  Expr p = vc_varExpr(vc, "p", vc_boolType(vc));
  Expr q = vc_varExpr(vc, "q", vc_boolType(vc));
  Expr i = vc_varExpr(vc, "i", bv4);

  // (ite p (ite q a b) c) = d, with every leaf contradicting d at i:
  // unsat for all values of p and q.
  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_iteExpr(vc, p, vc_iteExpr(vc, q, a, b), c), d));
  const Expr leaves[3] = {a, b, c};
  for (int x = 0; x < 3; x++)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, leaves[x], i),
                                     vc_readExpr(vc, d, i))));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  for (int solve = 0; solve < 3; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
    if (ext == nullptr)
      ext = bm->getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    // Both if-then-elses, nested, still cost no record at all.
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }

  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv1 = vc_bvType(vc, 1);
  Type bv10 = vc_bvType(vc, 10);
  Type arrT = vc_arrayType(vc, bv10, bv1);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv10); // the chain's one symbolic index
  Expr v = vc_varExpr(vc, "v", bv1);  // and its one symbolic value
  Expr zero = vc_bvConstExprFromInt(vc, 1, 0);
  Expr one = vc_bvConstExprFromInt(vc, 1, 1);
  Expr p = vc_bvConstExprFromInt(vc, 10, 271);
  Expr q = vc_bvConstExprFromInt(vc, 10, 205);
  Expr r = vc_bvConstExprFromInt(vc, 10, 729);

  Expr base = vc_writeExpr(vc, a, p, v);
  // Signed 1-bit: bvsmod(v, v) is zero either way, so the condition
  // holds exactly when v is zero -- but nothing folds it away while
  // the query is being built.
  Expr cond = vc_sbvLeExpr(vc, vc_sbvModExpr(vc, 1, v, v), v);
  Expr chain = vc_iteExpr(vc, cond, a, base);

  const Expr writes[15][2] = {{i, v},    {i, v},    {q, v},    {p, v},
                              {r, zero}, {r, v},    {p, zero}, {p, v},
                              {q, v},    {i, v},    {r, v},    {i, v},
                              {q, v},    {i, v},    {p, one}};
  for (int k = 0; k < 15; k++)
    chain = vc_writeExpr(vc, chain, writes[k][0], writes[k][1]);

  Expr eq = vc_eqExpr(vc, base, chain);
  ASSERT_EQ(EQ, getExprKind(eq));
  ASSERT_EQ(stp::ARRAY_EQ, static_cast<stp::ASTNode*>(eq)->GetKind());

  // STP has no assumption interface, so a scope stands in for
  // check-sat-assuming: the assumption goes away with the pop, which
  // is what makes these two solves of two different formulas.
  vc_push(vc);
  vc_assertFormula(vc, eq);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // 0 == INVALID == satisfiable
  vc_pop(vc);

  // The equality is out of the second formula. Its solve-local record and
  // graph must have been discarded rather than affecting this solve.
  vc_push(vc);
  vc_assertFormula(vc, cond);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  vc_Destroy(vc);
}

TEST(array_extensionality, asserted_ite_condition_folds_before_fe03)
{
  // A condition asserted true, so preprocessing could fold ite(p,a,b)
  // to a. Section 4.1 elimination had to decide before that fold could
  // happen and charged two equality records for an if-then-else that
  // was about to disappear. Direct integration charges nothing either
  // way: the record count is the user's equality alone whether the
  // fold happens or not.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr p = vc_varExpr(vc, "p", vc_boolType(vc));
  Expr i = vc_varExpr(vc, "i", bv4);

  vc_assertFormula(vc, p);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_iteExpr(vc, p, a, b), c));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                   vc_readExpr(vc, c, i))));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  stp::ExtensionalityContext* ext = nullptr;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  for (int solve = 0; solve < 2; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
    if (ext == nullptr)
      ext = bm->getExtensionalityIfAny();
    ASSERT_NE(nullptr, ext);
    EXPECT_EQ(1u, ext->getRecords().size()) << "solve " << solve;
  }

  vc_Destroy(vc);
}

TEST(array_extensionality, preencoded_leaf_validation)
{
  // The lemma-leaf validator must reject every shape that would
  // otherwise make lemma encoding silently invent fresh, unconstrained
  // SAT variables for a term the candidate was never checked against.
  stp::STPMgr mgr;
  stp::ToSATBase::ASTNodeToSATVar satVar;

  stp::ASTNode sym = mgr.CreateSymbol("s", 0, 4);
  stp::ASTNode cnst = mgr.CreateBVConst(4, 9);
  NodeFactory* hf = mgr.hashingNodeFactory;
  stp::ASTNode compound = hf->CreateTerm(stp::BVPLUS, 4, sym, cnst);

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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  // Observations at deliberately nonascending indices, plus a
  // disequality so a witness point is also published.
  const int idxs[] = {11, 3, 0, 7};
  for (int x = 0; x < 4; x++)
  {
    Expr rd = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 4, idxs[x]));
    vc_assertFormula(
        vc, vc_eqExpr(vc, rd, vc_bvConstExprFromInt(vc, 8, 16 + idxs[x])));
  }
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, a, b)));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  for (int round = 0; round < 2; round++)
  {
    Expr* aIdx;
    Expr* aVal;
    int aSize;
    vc_getCounterExampleArray(vc, a, &aIdx, &aVal, &aSize);
    ASSERT_GE(aSize, 4) << "round " << round;
    for (int x = 1; x < aSize; x++)
    {
      EXPECT_LT(getBVUnsigned(aIdx[x - 1]), getBVUnsigned(aIdx[x]))
          << "round " << round << " position " << x;
    }
    vc_deleteCounterExampleArray(aIdx, aVal, aSize);
  }

  vc_Destroy(vc);
}

TEST(array_extensionality, store_chain_equals_base_solved_by_rewrite)
{
  // An equality between a chain of writes and the chain's own base is
  // solved by rewriting into read equalities over the base: no
  // abstraction variable is minted, no record is created, and the
  // query never needs the refinement loop.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr v = vc_varExpr(vc, "v", bv8);

  Expr eq = vc_eqExpr(vc, vc_writeExpr(vc, a, i, v), a);
  // The node factory folds a single self-store to exactly
  // read(a, i) = v at creation, so no whole-array equality ever forms
  // and the extensionality context is never brought up.
  ASSERT_EQ(EQ, getExprKind(eq));
  ASSERT_EQ(stp::EQ, static_cast<stp::ASTNode*>(eq)->GetKind());

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  vc_assertFormula(vc, eq);
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), v)));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());
  vc_Destroy(vc);
}

TEST(array_extensionality, store_chain_shadowed_write_is_unconstrained)
{
  // In store(store(a,i,w),i,v) = a the inner write is shadowed by the
  // outer write at the identical index term, so its value w is dropped
  // from the rewrite entirely: only read(a,i) = v is forced.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr v = vc_varExpr(vc, "v", bv8);
  Expr w = vc_varExpr(vc, "w", bv8);

  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_writeExpr(vc, vc_writeExpr(vc, a, i, w), i, v),
                    a));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, w, vc_readExpr(vc, a, i))));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  // w is unconstrained: satisfiable. (The factory collapses the shadowed
  // write and then folds the single self-store, so the extensionality
  // context is never brought up.)
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  // v is forced: contradicting read(a,i) = v flips the verdict.
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), v)));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());
  vc_Destroy(vc);
}

TEST(array_extensionality, store_chain_guarded_inner_write)
{
  // With distinct index terms the inner write is guarded, not dropped:
  // store(store(a,j,w),i,v) = a forces read(a,j) = w whenever j != i.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);
  Expr v = vc_varExpr(vc, "v", bv8);
  Expr w = vc_varExpr(vc, "w", bv8);

  Expr eq = vc_eqExpr(
      vc, vc_writeExpr(vc, vc_writeExpr(vc, a, j, w), i, v), a);
  // Two live writes are still one opaque equality here. Lowering rewrites it
  // to a conjunction whose inner conjunct is guarded by index equality.
  ASSERT_EQ(EQ, getExprKind(eq));
  ASSERT_EQ(stp::ARRAY_EQ, static_cast<stp::ASTNode*>(eq)->GetKind());

  vc_assertFormula(vc, eq);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, i, j)));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, j), w)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());
  vc_Destroy(vc);
}

TEST(array_extensionality, store_chain_over_write_base)
{
  // The chain's base may itself be a write: hashing makes the two
  // occurrences of store(a,j,w) the same node, so the peel finds the
  // base one write down and the rewrite still applies.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);
  Expr v = vc_varExpr(vc, "v", bv8);
  Expr w = vc_varExpr(vc, "w", bv8);

  Expr b = vc_writeExpr(vc, a, j, w);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_writeExpr(vc, b, i, v), b));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, b, i), v)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  // The factory's self-store fold applies whatever the base is -- here a
  // write -- so the extensionality context is never brought up.
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());
  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv32 = vc_bvType(vc, 32);
  Type arrT = vc_arrayType(vc, bv32, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv32);
  Expr idx[4];
  Expr val[4];
  for (int k = 0; k < 4; k++)
  {
    idx[k] = vc_bvPlusExpr(vc, 32, i, vc_bvConstExprFromInt(vc, 32, k));
    char name[8];
    snprintf(name, sizeof(name), "x%d", k);
    val[k] = vc_varExpr(vc, name, bv8);
  }

  // The same four writes, applied in opposite orders.
  Expr c1 = a;
  Expr c2 = a;
  for (int k = 0; k < 4; k++)
  {
    c1 = vc_writeExpr(vc, c1, idx[k], val[k]);
    c2 = vc_writeExpr(vc, c2, idx[3 - k], val[3 - k]);
  }
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, c1, c2)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
  EXPECT_GT(ext->lemmaAtomsFolded, 0);
  vc_Destroy(vc);
}

TEST(array_extensionality, equality_under_push_pops_away)
{
  // Activation follows the current assertion root. Popping the equality
  // removes its witness bundle from the next solve; reasserting the same
  // durable opaque handle activates it again.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr zero = vc_bvConstExprFromInt(vc, 4, 0);

  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, zero),
                                   vc_readExpr(vc, b, zero))));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  vc_pop(vc);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0u, ext->getActiveRecordCount());

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  vc_pop(vc);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0u, ext->getActiveRecordCount());
  vc_Destroy(vc);
}

TEST(array_extensionality, equality_asserted_between_queries)
{
  // The first solve runs with an empty registry; the equality is
  // asserted only after its answer, and the second solve must
  // abstract, prepare, and refine it from scratch.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);

  vc_assertFormula(vc, vc_eqExpr(vc, i, j));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                   vc_readExpr(vc, b, j))));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // unrelated arrays differ

  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))); // congruence across a = b
  vc_Destroy(vc);
}

TEST(array_extensionality, active_equalities_follow_assertions_and_query)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv1 = vc_bvType(vc, 1);
  Type arrT = vc_arrayType(vc, bv1, bv1);
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr zero = vc_bvConstExprFromInt(vc, 1, 0);
  Expr one = vc_bvConstExprFromInt(vc, 1, 1);
  Expr eq = vc_eqExpr(vc, a, b);

  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, zero),
                                 vc_readExpr(vc, b, zero)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, one),
                                 vc_readExpr(vc, b, one)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;

  // Merely retaining an opaque handle neither creates a context nor activates
  // its witness bundle when it is absent from the completed solve root.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());

  // The same handle used as the query is reachable through NOT(query). The
  // complete one-bit domain makes the equality valid.
  ASSERT_EQ(1, vc_query(vc, eq));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(1u, ext->getActiveRecordCount());

  // A later solve that omits the equality must not inherit its constraints.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0u, ext->getActiveRecordCount());
  vc_Destroy(vc);
}

TEST(array_extensionality, opaque_equality_handle_uses_current_model_lowering)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv1 = vc_bvType(vc, 1);
  Type arrT = vc_arrayType(vc, bv1, bv1);
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr eq = vc_eqExpr(vc, a, b);

  vc_push(vc);
  vc_assertFormula(vc, eq);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, eq)));
  vc_pop(vc);

  vc_push(vc);
  vc_assertFormula(vc, vc_notExpr(vc, eq));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(FALSE, getExprKind(vc_getCounterExample(vc, eq)));
  vc_pop(vc);

  vc_Destroy(vc);
}

// A handle for an equality the solve did not decide is answered from
// the model, not from an abstraction variable.
//
// Lowering can throw an equality away. Solving a write chain against
// its own base rewrites the equality instead of abstracting it, and
// drops the conjunct for a write an outer write to the same index
// shadows -- so an equality nested in that write's value goes with it.
// Its abstraction variable then enters no constraint and is never
// assigned, and reading the handle through it gave false, while the
// same model gave both arrays no cells at all and so printed them
// identically.
//
// Deciding it from the published cells cannot disagree with the model,
// because it is the model. Both arrays are unconstrained here, so both
// are the zero array, so they are equal.
TEST(array_extensionality, handle_for_a_discarded_equality_matches_the_model)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type idxT = vc_bvType(vc, 3), elT = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, idxT, elT);
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr p = vc_varExpr(vc, "p", arrT);
  Expr q = vc_varExpr(vc, "q", arrT);
  Expr i = vc_varExpr(vc, "i", idxT);
  Expr j = vc_varExpr(vc, "j", idxT);
  Expr v = vc_varExpr(vc, "v", elT);
  Expr y = vc_varExpr(vc, "y", elT);

  Expr nested = vc_eqExpr(vc, p, q);
  Expr value = vc_iteExpr(vc, nested, vc_bvConstExprFromInt(vc, 4, 1),
                          vc_bvConstExprFromInt(vc, 4, 0));
  // store(store(store(a, i, value), j, y), i, v) = a. The outermost
  // write is to i as well, so the innermost write to i is shadowed and
  // its conjunct -- the only one mentioning `value` -- is dropped.
  Expr chain = vc_writeExpr(vc, a, i, value);
  chain = vc_writeExpr(vc, chain, j, y);
  chain = vc_writeExpr(vc, chain, i, v);
  vc_assertFormula(vc, vc_eqExpr(vc, chain, a));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // Neither array carries a single cell, so the model makes them the
  // same array. Answering false here -- which is what an unassigned
  // abstraction variable produced -- contradicted the model in the same
  // breath as reporting it.
  Expr *indices, *values;
  int size = -1;
  vc_getCounterExampleArray(vc, p, &indices, &values, &size);
  ASSERT_EQ(0, size);
  vc_getCounterExampleArray(vc, q, &indices, &values, &size);
  ASSERT_EQ(0, size);

  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, nested)));

  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type idxT = vc_bvType(vc, 3), elT = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, idxT, elT);
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr idx = vc_bvConstExprFromInt(vc, 3, 1);

  // Only `a` is constrained, and only at one cell. `b` is untouched.
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, idx),
                                 vc_bvConstExprFromInt(vc, 4, 5)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // a holds 5 at that cell and b completes to zero there, so they
  // differ -- and a equals itself whatever the model says.
  Expr ab = vc_eqExpr(vc, a, b);
  EXPECT_EQ(FALSE, getExprKind(vc_getCounterExample(vc, ab)));
  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, vc_eqExpr(vc, a, a))));

  // Asking did not add cells to the model that the model API would
  // then report.
  Expr *indices, *values;
  int size = -1;
  vc_getCounterExampleArray(vc, b, &indices, &values, &size);
  EXPECT_EQ(0, size);

  vc_Destroy(vc);
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
// what the model surface answers an equality handle with, and the
// post-solve audit compares each one against the contents the model
// publishes for its operands.
//
// The model completes an unobserved cell with zero: that is what the
// printer stores under the array, what vc_getCounterExampleArray
// reports, and what the checker compares contents with. Evaluation used
// to invent all-ones for such a cell instead, which made the lowering of
// store(store(x5,3,3), x6, x1) = store(x5,3,3) read false while the same
// model printed the two arrays identically. Found by fuzzing; the audit
// caught it and aborted a satisfiable query.
TEST(array_extensionality, unconstrained_cells_read_as_the_model_prints_them)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  vc_setFlag(vc, 'd'); // build the counterexample and audit it

  Type bv3 = vc_bvType(vc, 3);
  Type arrT = vc_arrayType(vc, bv3, bv3);

  Expr x1 = vc_varExpr(vc, "x1", bv3);
  Expr x2 = vc_varExpr(vc, "x2", vc_boolType(vc));
  Expr x5 = vc_varExpr(vc, "x5", arrT);
  Expr x6 = vc_varExpr(vc, "x6", bv3);
  Expr x8 = vc_varExpr(vc, "x8", bv3);
  Expr x9 = vc_varExpr(vc, "x9", bv3);
  Expr three = vc_bvConstExprFromInt(vc, 3, 3);

  Expr c = vc_writeExpr(vc, x5, three, three);
  Expr a = vc_writeExpr(vc, c, x6, x1);
  Expr d = vc_writeExpr(
      vc,
      vc_writeExpr(vc, vc_writeExpr(vc, a, three, x1),
                   vc_readExpr(vc, x5, x1), three),
      x1, three);

  // (distinct a x5 c d): six pairs, each of them a write chain and a
  // base of that same chain.
  Expr operands[4] = {a, x5, c, d};
  Expr pairs[6];
  int n = 0;
  for (int p = 0; p < 4; p++)
    for (int q = p + 1; q < 4; q++)
      pairs[n++] = vc_notExpr(vc, vc_eqExpr(vc, operands[p], operands[q]));

  vc_assertFormula(vc, x2);
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_iteExpr(vc, x2, vc_eqExpr(vc, x8, x9),
                                    vc_andExprN(vc, pairs, 6))));

  // Satisfiable: x2 holds, so only x8 != x9 is required and the whole
  // distinct is dead.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // Nothing constrained x5, so the model prints it as the all-zero
  // array -- and a read of it must say zero too, at the index the
  // dropped equalities read it at.
  Expr *indices, *values;
  int size = -1;
  vc_getCounterExampleArray(vc, x5, &indices, &values, &size);
  EXPECT_EQ(0, size);
  EXPECT_EQ(0, getBVUnsignedLongLong(
                   vc_getCounterExample(vc, vc_readExpr(vc, x5, x6))));

  // The equality handles agree with those contents in both directions:
  // store(x5,3,3) with a write of x1 at x6 on top is the same array when
  // x5 already holds x1 there, and neither is x5 itself, which holds
  // zero at index 3.
  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, vc_eqExpr(vc, a, c))));
  EXPECT_EQ(FALSE, getExprKind(vc_getCounterExample(vc, vc_eqExpr(vc, a, x5))));
  EXPECT_EQ(FALSE, getExprKind(vc_getCounterExample(vc, vc_eqExpr(vc, c, x5))));

  vc_Destroy(vc);
}

TEST(array_extensionality, active_checker_owns_complete_array_graph)
{
  // The contradiction lives in congruence across a = b, while unrelated
  // array c carries satisfiable constraints. Once the equality activates
  // the checker, both components belong to its complete graph; the unsat
  // verdict must come through its lemma path, pinned by the counter.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);
  Expr k = vc_varExpr(vc, "k", bv4);
  Expr l = vc_varExpr(vc, "l", bv4);

  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  vc_assertFormula(vc, vc_eqExpr(vc, i, j));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                   vc_readExpr(vc, b, j))));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, k),
                                 vc_bvConstExprFromInt(vc, 8, 7)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, l),
                                 vc_bvConstExprFromInt(vc, 8, 9)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
  vc_Destroy(vc);
}

TEST(array_extensionality, whole_graph_checker_publishes_mixed_sat_model)
{
  // v is forced to 42 through cross-array congruence over the true
  // equality and w to 5 through same-array congruence on disconnected c.
  // The concrete values pin complete-graph certification and publication,
  // not just the satisfiable verdict.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr i = vc_varExpr(vc, "i", bv4);
  Expr j = vc_varExpr(vc, "j", bv4);
  Expr k = vc_varExpr(vc, "k", bv4);
  Expr l = vc_varExpr(vc, "l", bv4);
  Expr v = vc_varExpr(vc, "v", bv8);
  Expr w = vc_varExpr(vc, "w", bv8);

  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  vc_assertFormula(vc, vc_eqExpr(vc, i, j));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i),
                                 vc_bvConstExprFromInt(vc, 8, 42)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, b, j), v));
  // Say k = l without a substitutable equality, so the two read
  // abstractions remain syntactically distinct until checker rule C.
  vc_assertFormula(vc, vc_notExpr(vc, vc_bvLtExpr(vc, k, l)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_bvLtExpr(vc, l, k)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, k),
                                 vc_bvConstExprFromInt(vc, 8, 5)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, l), w));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(42u, getBVUnsigned(vc_getCounterExample(vc, v)));
  EXPECT_EQ(5u, getBVUnsigned(vc_getCounterExample(vc, w)));

  Expr* cIdx;
  Expr* cVal;
  int cSize = 0;
  vc_getCounterExampleArray(vc, c, &cIdx, &cVal, &cSize);
  ASSERT_EQ(1, cSize);
  EXPECT_EQ(getBVUnsigned(vc_getCounterExample(vc, k)), getBVUnsigned(cIdx[0]));
  EXPECT_EQ(5u, getBVUnsigned(cVal[0]));
  vc_deleteCounterExampleArray(cIdx, cVal, cSize);
  vc_Destroy(vc);
}

TEST(array_extensionality, flag_on_without_equalities_is_dormant)
{
  // With the option on but no array equality anywhere in the query,
  // the decision procedure must stay entirely dormant: no context is
  // ever created, and the solve is the flag-off solve -- the same
  // verdict and the same model values, including for terms the
  // constraints leave free.
  unsigned values[2][4];
  int verdicts[2];
  std::map<unsigned, unsigned> entries[2];
  for (int flag = 0; flag < 2; flag++)
  {
    VC vc = vc_createValidityChecker();
    if (flag)
      vc_setFlag(vc, 'x');

    Type bv8 = vc_bvType(vc, 8);
    Type bv4 = vc_bvType(vc, 4);
    Type arrT = vc_arrayType(vc, bv4, bv8);

    Expr a = vc_varExpr(vc, "a", arrT);
    Expr i = vc_varExpr(vc, "i", bv4);
    Expr j = vc_varExpr(vc, "j", bv4);
    Expr v = vc_varExpr(vc, "v", bv8);

    vc_assertFormula(
        vc, vc_eqExpr(vc,
                      vc_readExpr(vc, vc_writeExpr(vc, a, i, v), j),
                      vc_bvConstExprFromInt(vc, 8, 42)));
    vc_assertFormula(vc, vc_eqExpr(vc, i, j));
    vc_assertFormula(
        vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 4, 3)),
                      vc_bvConstExprFromInt(vc, 8, 7)));

    verdicts[flag] = vc_query(vc, vc_falseExpr(vc));
    values[flag][0] = getBVUnsigned(vc_getCounterExample(vc, v));
    values[flag][1] = getBVUnsigned(vc_getCounterExample(vc, i));
    values[flag][2] = getBVUnsigned(vc_getCounterExample(vc, j));
    values[flag][3] = getBVUnsigned(vc_getCounterExample(
        vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 4, 3))));

    // Dormant array-model surface: with the option on but no equality
    // anywhere, vc_getCounterExampleArray runs its sorted extraction
    // against a counterexample populated purely by classic refinement.
    // As a set of entries it must agree with the option-off surface
    // (the ascending order is the one deliberate difference).
    Expr* idxE;
    Expr* valE;
    int size = 0;
    vc_getCounterExampleArray(vc, a, &idxE, &valE, &size);
    for (int x = 0; x < size; x++)
    {
      entries[flag][getBVUnsigned(idxE[x])] = getBVUnsigned(valE[x]);
      if (flag && x > 0)
      {
        EXPECT_LT(getBVUnsigned(idxE[x - 1]), getBVUnsigned(idxE[x]));
      }
    }
    vc_deleteCounterExampleArray(idxE, valE, size);

    stp::STPMgr* bm = ((stp::STP*)vc)->bm;
    if (flag)
    {
      // No equality was ever abstracted, so no context exists at all.
      EXPECT_EQ(nullptr, bm->getExtensionalityIfAny());
    }
    vc_Destroy(vc);
  }

  EXPECT_EQ(verdicts[0], verdicts[1]);
  EXPECT_EQ(0, verdicts[0]); // satisfiable
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
  VC vc = vc_createValidityChecker();
  if (!vc_supportsCadical(vc))
  {
    vc_Destroy(vc);
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  }
  vc_setFlag(vc, 'x');
  ASSERT_TRUE(vc_useCadical(vc));

  Type bv8 = vc_bvType(vc, 8);
  Type arrT = vc_arrayType(vc, bv8, bv8);

  // The same two writes applied in opposite orders at provably
  // distinct indices: unsat, and only refinement lemmas can prove it.
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr i = vc_varExpr(vc, "i", bv8);
  Expr i1 = vc_bvPlusExpr(vc, 8, i, vc_bvConstExprFromInt(vc, 8, 1));
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr y = vc_varExpr(vc, "y", bv8);

  Expr c1 = vc_writeExpr(vc, vc_writeExpr(vc, a, i, x), i1, y);
  Expr c2 = vc_writeExpr(vc, vc_writeExpr(vc, a, i1, y), i, x);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, c1, c2)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type arrT = vc_arrayType(vc, bv8, bv8);

  Expr x0 = vc_varExpr(vc, "x0", bv8);
  Expr x5 = vc_varExpr(vc, "x5", arrT);
  Expr x9 = vc_varExpr(vc, "x9", arrT);
  Expr x11 = vc_varExpr(vc, "x11", arrT);
  Expr c = vc_bvConstExprFromLL(vc, 8, 0x9C);    // -100
  Expr mins = vc_bvConstExprFromLL(vc, 8, 0x80); // min signed

  Expr k = vc_readExpr(vc, x11, vc_readExpr(vc, x9, x0));
  Expr q = vc_sbvDivExpr(vc, 8, x0, c);

  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, x9, x0), c));
  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_readExpr(vc, vc_writeExpr(vc, x9, x0, mins), k),
                    x0));
  vc_assertFormula(
      vc, vc_eqExpr(vc, x9,
                    vc_writeExpr(vc, vc_writeExpr(vc, x5, x0, q), k, x0)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  // This input no longer reaches the divergence refusal it was reduced
  // from: constant bit propagation now writes every fully fixed node
  // back into the graph, not only the ones the top node does not depend
  // on, so both occurrences of x11[C] are rewritten alike and are
  // abstracted as one read. What is left here is the ordinary lemma
  // loop over the same formula, which still has to answer unsat.
  // unlinked_reads_are_owned_by_the_extensionality_checker covers the
  // formerly split ownership route directly.
  vc_Destroy(vc);
}

TEST(array_extensionality,
     unlinked_reads_are_owned_by_the_extensionality_checker)
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;

  Type bv8 = vc_bvType(vc, 8);
  Type arrT = vc_arrayType(vc, bv8, bv8);

  Expr i = vc_varExpr(vc, "i", bv8);
  Expr j = vc_varExpr(vc, "j", bv8);
  Expr x5 = vc_varExpr(vc, "x5", arrT);
  Expr x9 = vc_varExpr(vc, "x9", arrT);
  Expr x11 = vc_varExpr(vc, "x11", arrT);
  Expr one = vc_bvConstExprFromLL(vc, 8, 1);

  vc_assertFormula(vc, vc_notExpr(vc, vc_bvLtExpr(vc, i, j)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_bvLtExpr(vc, j, i)));

  vc_assertFormula(
      vc, vc_eqExpr(vc, x9,
                    vc_writeExpr(vc, x5, vc_readExpr(vc, x11, i), one)));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(
                             vc, vc_readExpr(vc, x9, vc_readExpr(vc, x11, j)),
                             one)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_GT(ext->lemmasEmitted, 0);
  vc_Destroy(vc);
}

TEST(array_extensionality, store_index_read_through_second_array_bv120_unsat)
{
  // The same defect as store_index_read_through_second_array_unsat,
  // as originally found: 120-bit words, and the contradictory
  // constraints arriving as assumptions inside a pushed scope. The
  // divisor's magnitude squared exceeds the signed range, so
  // x0 sdiv C = C has no solution, and C != MIN closes the x0 = k
  // case exactly as at width 8.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv120 = vc_bvType(vc, 120);
  Type arrT = vc_arrayType(vc, bv120, bv120);

  Expr x0 = vc_varExpr(vc, "x0", bv120);
  Expr c = vc_bvUMinusExpr(
      vc, vc_bvConstExprFromDecStr(vc, 120,
                                   "36288689616474043440116267750740073"));
  Expr x5 = vc_varExpr(vc, "x5", arrT);
  Expr mins = vc_bvConstExprFromStr(
      vc, "10000000000000000000000000000000000000000000000000000000000000000"
          "0000000000000000000000000000000000000000000000000000000");
  Expr x9 = vc_varExpr(vc, "x9", arrT);
  Expr x11 = vc_varExpr(vc, "x11", arrT);

  Expr t20 = vc_sbvDivExpr(vc, 120, x0, c);
  Expr t21 = vc_readExpr(vc, x9, x0);
  Expr t22 = vc_readExpr(vc, x11, t21);
  Expr t73 = vc_readExpr(vc, vc_writeExpr(vc, x9, x0, mins), t22);
  Expr t84 = vc_eqExpr(vc, t73, x0);
  Expr t111 =
      vc_writeExpr(vc, vc_writeExpr(vc, x5, x0, t20), t22, x0);
  Expr t132 = vc_eqExpr(vc, x9, t111);
  Expr t134 = vc_eqExpr(vc, t21, c);

  vc_assertFormula(vc, t134);

  // check-sat-assuming (t84 t132 t84 t84), as a scope of assertions
  vc_push(vc);
  vc_assertFormula(vc, t84);
  vc_assertFormula(vc, t132);
  vc_assertFormula(vc, t84);
  vc_assertFormula(vc, t84);
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  // The base assertion alone is satisfiable.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

TEST(array_extensionality, mixed_width_equality_dies_loudly)
{
  // vc_eqExpr over arrays of different index widths cannot be abstracted.
  // Reject it at the public sort boundary rather than building a silently
  // mistyped node that the solve would trip over later.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, bv4, bv8));
  Expr b = vc_varExpr(vc, "b", vc_arrayType(vc, bv8, bv8));

  EXPECT_DEATH(vc_eqExpr(vc, a, b), "requires operands of the same sort");
  vc_Destroy(vc);
}

TEST(array_extensionality, flag_off_refuses_array_equality)
{
  // The C API constructs nodes through STPMgr rather than Cpp_interface.
  // Refusal therefore belongs in the common node-factory path; otherwise
  // this front end can still build an unsupported, unconstrained EQ node.
  VC vc = vc_createValidityChecker();

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  EXPECT_DEATH(vc_eqExpr(vc, a, b),
               "STP cannot decide equality between whole array terms");

  // The central check is specific to arrays: ordinary equality remains
  // available when the extension is disabled.
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr y = vc_varExpr(vc, "y", bv8);
  Expr eq = vc_eqExpr(vc, x, y);
  EXPECT_EQ(EQ, getExprKind(eq));
  vc_Destroy(vc);
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
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');
  // A definitional top-level equality (a symbol equated with an array
  // term) now substitutes away before abstraction ever sees it. This
  // test pins the abstraction/checker path itself, so keep the
  // equality there.
  static_cast<stp::STP*>(vc)->bm->UserFlags.propagate_equalities = false;
  // And for the same reason: all three arrays are used once, so
  // unconstrained elimination would collapse the if-then-else and then
  // the equality, minting no record for the checker to work on.
  static_cast<stp::STP*>(vc)->bm->UserFlags.enable_unconstrained = false;

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr c = vc_varExpr(vc, "c", arrT);
  Expr x = vc_varExpr(vc, "x", bv8);

  // Undecided, so the if-then-else survives and must be eliminated,
  // but not a bare Boolean symbol either: preprocessing normalises the
  // comparison, and that rewritten form is what the rebuilt lookup key
  // is made of.
  Expr cond = vc_bvLtExpr(vc, x, vc_bvConstExprFromLL(vc, 8, 0x10));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_iteExpr(vc, cond, a, b), c));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  // The user's equality, and nothing minted for the if-then-else.
  const size_t afterFirstSolve = ext->getRecords().size();
  EXPECT_EQ(1u, afterFirstSolve);

  // An assertion between the solves is what forces the second one to
  // prepare again rather than reuse the previous answer.
  Expr t = vc_varExpr(vc, "t", bv8);
  vc_assertFormula(vc, vc_bvLeExpr(vc, t, vc_bvConstExprFromLL(vc, 8, 0xFE)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_EQ(afterFirstSolve, ext->getRecords().size());
  vc_Destroy(vc);
}

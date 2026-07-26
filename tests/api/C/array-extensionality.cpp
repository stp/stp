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
// vc_eqExpr over array operands returns a fresh Boolean abstraction
// variable and the lemmas-on-demand procedure decides the query; with
// the flag off, the pre-existing warn-and-return-EQ behavior is
// preserved.

#include "stp/c_interface.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STP.h"
#include <gtest/gtest.h>

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

  // The minted equality is an ordinary Boolean symbol, not an EQ node.
  Expr eq = vc_eqExpr(vc, a, b);
  ASSERT_EQ(SYMBOL, getExprKind(eq));

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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);

  // Only the construction-time equality was minted so far.
  ASSERT_EQ(1u, ext->getRecords().size());

  for (int solve = 0; solve < 4; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
    // user record + exactly two guarded-ITE records, on every solve
    EXPECT_EQ(3u, ext->getRecords().size()) << "solve " << solve;
  }

  vc_Destroy(vc);
}

TEST(array_extensionality, nested_ite_fixed_point_is_stable)
{
  // A nested array if-then-else with unresolved conditions reaches the
  // elimination fixed point once -- one user record plus two records
  // per eliminated ITE -- and repeated solves reuse all of them.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  ASSERT_EQ(1u, ext->getRecords().size());

  for (int solve = 0; solve < 3; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
    // 1 construction + 2 per eliminated ITE (outer and inner)
    EXPECT_EQ(5u, ext->getRecords().size()) << "solve " << solve;
  }

  vc_Destroy(vc);
}

TEST(array_extensionality, asserted_ite_condition_folds_before_fe03)
{
  // Companion coverage for permitted simplification: with the
  // condition asserted true, ordinary preprocessing folds ite(p,a,b)
  // to a before preparation ever sees it, so no guarded equalities are
  // created and the registry keeps only the user's record.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);

  for (int solve = 0; solve < 2; solve++)
  {
    ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc))) << "solve " << solve;
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
  // A single write rewrites to exactly read(a, i) = v.
  ASSERT_EQ(EQ, getExprKind(eq));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());

  vc_assertFormula(vc, eq);
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), v)));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0u, ext->getRecords().size());
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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());

  // w is unconstrained: satisfiable.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // v is forced: contradicting read(a,i) = v flips the verdict.
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), v)));
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0u, ext->getRecords().size());
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
  // Two live writes rewrite to a conjunction, with the inner conjunct
  // guarded by the index equality with the outer write.
  ASSERT_EQ(AND, getExprKind(eq));

  vc_assertFormula(vc, eq);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, i, j)));
  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, vc_readExpr(vc, a, j), w)));

  stp::STPMgr* bm = ((stp::STP*)vc)->bm;
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(0u, ext->getRecords().size());

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_GT(ext->lemmasEmitted, 0);
  EXPECT_GT(ext->lemmaAtomsFolded, 0);
  vc_Destroy(vc);
}

TEST(array_extensionality, equality_under_push_pops_away)
{
  // A record minted under a pushed scope survives the pop in the
  // persistent registry, and every later solve re-conjoins its
  // witness bundle. The bundle is satisfiability-preserving (fresh
  // witness symbols, otherwise unconstrained; a true proxy satisfies
  // the witness clause), so the pop must recover sat -- and
  // re-asserting the same equality reuses the record, with no second
  // one minted, and flips the verdict back.
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

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

  vc_pop(vc);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, a, b));
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);
  EXPECT_EQ(1u, ext->getRecords().size());
  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_pop(vc);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
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

TEST(array_extensionality, interleaves_with_classic_read_refinement)
{
  // One query, two refinement machines: the contradiction lives in
  // the equality cone (congruence across a = b), while the unrelated
  // array c carries satisfiable constraints that classic lazy read
  // refinement owns. Reads of a and b are exempt from the classic
  // read axioms, so the unsat verdict must come through an equality
  // lemma -- pinned by the emission counter -- with c's machinery
  // interleaved in the same loop.
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
  stp::ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  ASSERT_NE(nullptr, ext);

  ASSERT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_GT(ext->lemmasEmitted, 0);
  vc_Destroy(vc);
}

TEST(array_extensionality, mixed_sat_model_satisfies_both_machines)
{
  // Satisfiable only when both machines police the same assignment:
  // v is forced to 42 through cross-array congruence over the true
  // equality, w to 5 through same-array congruence on c under classic
  // refinement. The concrete model values pin the cooperation, not
  // just the verdict.
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
  vc_assertFormula(vc, vc_eqExpr(vc, k, l));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, k),
                                 vc_bvConstExprFromInt(vc, 8, 5)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, c, l), w));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(42u, getBVUnsigned(vc_getCounterExample(vc, v)));
  EXPECT_EQ(5u, getBVUnsigned(vc_getCounterExample(vc, w)));
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
}

TEST(array_extensionality, flag_off_preserves_eq_node)
{
  // Default-off: an array equality still builds an ordinary EQ node
  // (with the existing warning), exactly as before.
  VC vc = vc_createValidityChecker();

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  Expr eq = vc_eqExpr(vc, a, b);
  ASSERT_EQ(EQ, getExprKind(eq));
  vc_Destroy(vc);
}

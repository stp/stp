/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// The blaster's two backends, driven over the same formulas.
//
// The comparison is by *function*, never by node count or node id. The two
// packages build different graphs on purpose -- ours orders operands before
// applying the folding rules, so it lands on a slightly smaller AIG -- and a
// test that pinned the counts would be pinning that difference rather than
// the blasting. What has to agree is what the circuit computes.
//
// Six input bits, so a truth table is one 64-bit word and "same function" is
// one comparison.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BBNodeManagerLit.h"
#include "stp/ToSat/BitBlaster.h"

#include "aig/aig/aig.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string>
#include <vector>

using namespace stp;

namespace
{

const uint64_t INPUT_TT[6] = {
    0xAAAAAAAAAAAAAAAAull, 0xCCCCCCCCCCCCCCCCull, 0xF0F0F0F0F0F0F0F0ull,
    0xFF00FF00FF00FF00ull, 0xFFFF0000FFFF0000ull, 0xFFFFFFFF00000000ull};

// Simulate the in-house AIG. Ids ascend and fanins are always below their
// node, so one forward sweep does it.
uint64_t litTruthTable(const aig::Manager& m, aig::Lit top,
                       const std::map<unsigned, uint64_t>& inputs)
{
  std::vector<uint64_t> tt(m.nodeCount(), 0);
  for (aig::Node n = 1; n < m.nodeCount(); ++n)
  {
    if (m.isCi(n))
    {
      const auto it = inputs.find(n);
      tt[n] = it == inputs.end() ? 0 : it->second;
    }
    else
    {
      const aig::Lit a = m.fanin0(n), b = m.fanin1(n);
      const uint64_t va =
          aig::isNeg(a) ? ~tt[aig::nodeOf(a)] : tt[aig::nodeOf(a)];
      const uint64_t vb =
          aig::isNeg(b) ? ~tt[aig::nodeOf(b)] : tt[aig::nodeOf(b)];
      tt[n] = va & vb;
    }
  }
  if (aig::isConst(top))
    return top == aig::LIT_TRUE ? ~0ull : 0ull;
  const uint64_t v = tt[aig::nodeOf(top)];
  return aig::isNeg(top) ? ~v : v;
}

// The same for ABC's. Aig_ManForEachObj walks in id order, and ABC keeps
// fanins below their node too.
uint64_t abcTruthTable(Aig_Man_t* p, Aig_Obj_t* top,
                       const std::map<int, uint64_t>& inputs)
{
  std::map<int, uint64_t> tt;
  Aig_Obj_t* obj;
  int i;
  tt[Aig_ObjId(Aig_ManConst1(p))] = ~0ull;
  Aig_ManForEachObj(p, obj, i)
  {
    if (Aig_ObjIsCi(obj))
    {
      const auto it = inputs.find(Aig_ObjId(obj));
      tt[Aig_ObjId(obj)] = it == inputs.end() ? 0 : it->second;
    }
    else if (Aig_ObjIsAnd(obj))
    {
      const uint64_t a = tt[Aig_ObjId(Aig_ObjFanin0(obj))];
      const uint64_t b = tt[Aig_ObjId(Aig_ObjFanin1(obj))];
      tt[Aig_ObjId(obj)] = (Aig_ObjFaninC0(obj) ? ~a : a) &
                           (Aig_ObjFaninC1(obj) ? ~b : b);
    }
  }
  const uint64_t v = tt[Aig_ObjId(Aig_Regular(top))];
  return Aig_IsComplement(top) ? ~v : v;
}

// Blast `form` through both backends and require that they compute the same
// function of the same inputs.
//
// The input correspondence is not assumed: it is read out of each manager's
// own symbol map, so a backend that numbered its inputs differently would be
// compared correctly and would fail only if its circuit really differed.
void expectSameFunction(STPMgr& mgr, const ASTNode& form,
                        const std::string& what)
{
  SubstitutionMap subsAig(&mgr), subsLit(&mgr);
  Simplifier simpAig(&mgr, &subsAig), simpLit(&mgr, &subsLit);

  BBNodeManagerAIG aigMgr;
  BitBlasterAIG bbAig(&aigMgr, &simpAig, mgr.defaultNodeFactory,
                      &mgr.UserFlags);
  BBNodeManagerLit litMgr;
  BitBlasterLit bbLit(&litMgr, &simpLit, mgr.defaultNodeFactory,
                      &mgr.UserFlags);

  const BBNodeAIG topAig = bbAig.BBForm(form);
  const BBNodeLit topLit = bbLit.BBForm(form);

  // The two symbol maps have to name the same bits, in the same order, or
  // the CNF's varOfCi(ordinal) would mean different things on the two
  // backends. Assign each bit its truth-table column by walking them
  // together.
  std::map<int, uint64_t> abcInputs;
  std::map<unsigned, uint64_t> litInputs;
  unsigned column = 0;

  auto itA = aigMgr.symbolToBBNode.begin();
  auto itL = litMgr.symbolToBBNode.begin();
  for (; itA != aigMgr.symbolToBBNode.end(); ++itA, ++itL)
  {
    ASSERT_NE(itL, litMgr.symbolToBBNode.end()) << what;
    ASSERT_EQ(itA->first, itL->first) << what;
    ASSERT_EQ(itA->second.size(), itL->second.size()) << what;

    for (size_t i = 0; i < itA->second.size(); i++)
    {
      const bool nullA = itA->second[i].IsNull();
      ASSERT_EQ(nullA, itL->second[i].IsNull()) << what << " bit " << i;
      if (nullA)
        continue;

      // Same input ordinal on both sides. This is what the CNF seam relies
      // on, and it holds because the blaster mints the inputs in one order.
      ASSERT_EQ(aigMgr.ciOrdinal(itA->second[i]),
                litMgr.ciOrdinal(itL->second[i]))
          << what << " bit " << i;

      ASSERT_LT(column, 6u) << what << ": too many input bits for one word";
      abcInputs[Aig_ObjId(Aig_Regular(itA->second[i].n))] = INPUT_TT[column];
      litInputs[aig::nodeOf(itL->second[i].n)] = INPUT_TT[column];
      column++;
    }
  }
  ASSERT_EQ(itL, litMgr.symbolToBBNode.end()) << what;

  const uint64_t a = abcTruthTable(aigMgr.aigMgr, topAig.n, abcInputs);
  const uint64_t l = litTruthTable(litMgr.mgr, topLit.n, litInputs);
  EXPECT_EQ(a, l) << what << ": the two backends disagree";
}

} // namespace

// One formula per bit-vector operator the blaster has a circuit for, over
// two three-bit symbols. Three bits is enough to reach every branch of the
// adders, the shifters and the multiplier that width-independent code has,
// and small enough that the whole function fits in one word.
TEST(BitBlasterLit, AgreesWithTheAIGBackend)
{
  STPMgr mgr;

  const ASTNode x = mgr.CreateSymbol("x", 0, 3);
  const ASTNode y = mgr.CreateSymbol("y", 0, 3);
  const ASTNode three = mgr.CreateBVConst(3, 3);
  const ASTNode one = mgr.CreateBVConst(3, 1);

  const struct
  {
    const char* name;
    ASTNode form;
  } cases[] = {
      {"eq", mgr.CreateNode(EQ, x, y)},
      {"plus", mgr.CreateNode(EQ, mgr.CreateTerm(BVPLUS, 3, x, y), three)},
      {"sub", mgr.CreateNode(EQ, mgr.CreateTerm(BVSUB, 3, x, y), one)},
      {"mult", mgr.CreateNode(EQ, mgr.CreateTerm(BVMULT, 3, x, y), three)},
      {"div", mgr.CreateNode(EQ, mgr.CreateTerm(BVDIV, 3, x, y), one)},
      {"mod", mgr.CreateNode(EQ, mgr.CreateTerm(BVMOD, 3, x, y), one)},
      {"and", mgr.CreateNode(EQ, mgr.CreateTerm(BVAND, 3, x, y), one)},
      {"or", mgr.CreateNode(EQ, mgr.CreateTerm(BVOR, 3, x, y), one)},
      {"xor", mgr.CreateNode(EQ, mgr.CreateTerm(BVXOR, 3, x, y), one)},
      {"uminus", mgr.CreateNode(EQ, mgr.CreateTerm(BVUMINUS, 3, x), y)},
      {"not", mgr.CreateNode(EQ, mgr.CreateTerm(BVNOT, 3, x), y)},
      {"lt", mgr.CreateNode(BVLT, x, y)},
      {"le", mgr.CreateNode(BVLE, x, y)},
      {"slt", mgr.CreateNode(BVSLT, x, y)},
      {"sle", mgr.CreateNode(BVSLE, x, y)},
      {"shl", mgr.CreateNode(EQ, mgr.CreateTerm(BVLEFTSHIFT, 3, x, y), one)},
      {"shr", mgr.CreateNode(EQ, mgr.CreateTerm(BVRIGHTSHIFT, 3, x, y), one)},
      {"ashr", mgr.CreateNode(EQ, mgr.CreateTerm(BVSRSHIFT, 3, x, y), one)},
      {"extract",
       mgr.CreateNode(EQ, mgr.CreateTerm(BVEXTRACT, 1, x, mgr.CreateBVConst(32, 2),
                                         mgr.CreateBVConst(32, 2)),
                      mgr.CreateBVConst(1, 1))},
      {"concat", mgr.CreateNode(EQ, mgr.CreateTerm(BVCONCAT, 6, x, y),
                                mgr.CreateBVConst(6, 9))},
      {"sx", mgr.CreateNode(EQ, mgr.CreateTerm(BVSX, 6, x, mgr.CreateBVConst(32, 6)),
                            mgr.CreateBVConst(6, 63))},
      {"ite", mgr.CreateNode(EQ, mgr.CreateTerm(ITE, 3, mgr.CreateNode(BVLT, x, y),
                                                x, y),
                             one)},
      {"logical-not", mgr.CreateNode(NOT, mgr.CreateNode(EQ, x, y))},
      {"nested", mgr.CreateNode(
                     AND, mgr.CreateNode(BVLT, x, y),
                     mgr.CreateNode(EQ, mgr.CreateTerm(BVPLUS, 3, x, y), three))},
  };

  for (const auto& c : cases)
    ASSERT_NO_FATAL_FAILURE(expectSameFunction(mgr, c.form, c.name)) << c.name;
}

// The budget is the manager's, not ABC's: the literal backend has to raise
// the same exception at the same place, because every caller that sets a
// budget catches that one type.
TEST(BitBlasterLit, HonoursTheNodeBudget)
{
  STPMgr mgr;

  const ASTNode x = mgr.CreateSymbol("x", 0, 16);
  const ASTNode y = mgr.CreateSymbol("y", 0, 16);
  const ASTNode form =
      mgr.CreateNode(EQ, mgr.CreateTerm(BVMULT, 16, x, y),
                     mgr.CreateBVConst(16, 7));

  SubstitutionMap subs(&mgr);
  Simplifier simp(&mgr, &subs);
  BBNodeManagerLit litMgr;
  litMgr.nodeBudget = 10;
  BitBlasterLit bb(&litMgr, &simp, mgr.defaultNodeFactory, &mgr.UserFlags);

  bool thrown = false;
  try
  {
    bb.BBForm(form);
  }
  catch (const AIGBudgetExhausted& e)
  {
    thrown = true;
    EXPECT_GT(e.nodeCount, 10);
  }
  EXPECT_TRUE(thrown) << "a 16x16 multiplier is more than ten gates";
}

// Every gate kind the manager offers, at every arity it accepts.
//
// The formula-driven test above cannot reach all of them from bit-vector
// operators alone, and the ones it misses are where a transcription slip
// lives longest: breaking IMPLIES deliberately left that test green.
//
// NAND and IMPLIES look unreachable if you grep for CreateNode(NAND -- there
// is no such call. They arrive as a *variable* kind instead, from BBForm's
// pass-through of a formula node's own kind, so any AST carrying one reaches
// the manager. Both are therefore live, whatever a grep says.
TEST(BitBlasterLit, EveryGateKindMatches)
{
  const struct
  {
    Kind kind;
    unsigned lo, hi;
  } kinds[] = {{AND, 1, 5},  {OR, 1, 5},      {NAND, 1, 5}, {NOR, 1, 5},
               {XOR, 1, 5},  {NOT, 1, 1},     {IFF, 2, 2},  {IMPLIES, 2, 2},
               {ITE, 3, 3}};

  for (const auto& k : kinds)
  {
    for (unsigned arity = k.lo; arity <= k.hi; arity++)
    {
      BBNodeManagerAIG aigMgr;
      BBNodeManagerLit litMgr;

      std::vector<BBNodeAIG> aigKids;
      std::vector<BBNodeLit> litKids;
      std::map<int, uint64_t> abcInputs;
      std::map<unsigned, uint64_t> litInputs;
      for (unsigned i = 0; i < arity; i++)
      {
        aigKids.push_back(aigMgr.CreateFreshInput());
        litKids.push_back(litMgr.CreateFreshInput());
        abcInputs[Aig_ObjId(Aig_Regular(aigKids.back().n))] = INPUT_TT[i];
        litInputs[aig::nodeOf(litKids.back().n)] = INPUT_TT[i];
      }

      const BBNodeAIG a = aigMgr.CreateNode(k.kind, aigKids);
      const BBNodeLit l = litMgr.CreateNode(k.kind, litKids);

      EXPECT_EQ(abcTruthTable(aigMgr.aigMgr, a.n, abcInputs),
                litTruthTable(litMgr.mgr, l.n, litInputs))
          << _kind_names[k.kind] << " at arity " << arity;
    }
  }
}

// Four bytes, which is the reason this backend exists at all.
TEST(BitBlasterLit, TheHandleIsOneLiteral)
{
  EXPECT_EQ(sizeof(BBNodeLit), 4u);
  EXPECT_TRUE(BBNodeLit().IsNull());
  EXPECT_FALSE(BBNodeLit(aig::LIT_TRUE).IsNull());
  EXPECT_NE(BBNodeLit(aig::LIT_TRUE), BBNodeLit(aig::LIT_FALSE));
}

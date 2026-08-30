/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// The Gia backend against the ABC-Aig backend, driven over the same formulas.
//
// The comparison is by *function*, never by node count or node id, for the
// reason BitBlasterLit_Test gives and one more that is specific to this pair:
// Gia_ManHashAnd orders its two operands before hashing and ABC's Aig_And
// does not, so the two build measurably different graphs for the same
// formula. A test that pinned counts would be pinning that.
//
// Six input bits, so a truth table is one 64-bit word and "same function" is
// one comparison.
//
// The last two tests are about the seam rather than the gates. They exist
// because this backend's inputs are not objects 1..nCi -- see ToCNFGia -- and
// that is the one property of it that could go wrong silently.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BBNodeManagerGia.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/ToCNFGia.h"

#include "aig/aig/aig.h"
#include "aig/gia/gia.h"

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

// Simulate a Gia. Gia_ManAppendAnd only ever takes literals of objects that
// already exist, so fanins are below their node and one forward sweep does
// it -- the same invariant the in-house package has, and the same reason
// ToCNFGia can mark a cone without recursing.
uint64_t giaTruthTable(Gia_Man_t* p, int topLit,
                       const std::map<int, uint64_t>& inputs)
{
  std::vector<uint64_t> tt(Gia_ManObjNum(p), 0);
  for (int id = 1; id < Gia_ManObjNum(p); id++)
  {
    Gia_Obj_t* const obj = Gia_ManObj(p, id);
    if (Gia_ObjIsCi(obj))
    {
      const auto it = inputs.find(id);
      tt[id] = it == inputs.end() ? 0 : it->second;
    }
    else if (Gia_ObjIsAnd(obj))
    {
      const uint64_t a = tt[Gia_ObjFaninId0(obj, id)];
      const uint64_t b = tt[Gia_ObjFaninId1(obj, id)];
      tt[id] = (Gia_ObjFaninC0(obj) ? ~a : a) & (Gia_ObjFaninC1(obj) ? ~b : b);
    }
  }
  if (Abc_Lit2Var(topLit) == 0) // the constant node carries both constants
    return topLit == 1 ? ~0ull : 0ull;
  const uint64_t v = tt[Abc_Lit2Var(topLit)];
  return Abc_LitIsCompl(topLit) ? ~v : v;
}

// The same for ABC's Aig. Aig_ManForEachObj walks in id order, and ABC keeps
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
      tt[Aig_ObjId(obj)] =
          (Aig_ObjFaninC0(obj) ? ~a : a) & (Aig_ObjFaninC1(obj) ? ~b : b);
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
  SubstitutionMap subsAig(&mgr), subsGia(&mgr);
  Simplifier simpAig(&mgr, &subsAig), simpGia(&mgr, &subsGia);

  BBNodeManagerAIG aigMgr;
  BitBlasterAIG bbAig(&aigMgr, &simpAig, mgr.defaultNodeFactory,
                      &mgr.UserFlags);
  BBNodeManagerGia giaMgr;
  BitBlasterGia bbGia(&giaMgr, &simpGia, mgr.defaultNodeFactory,
                      &mgr.UserFlags);

  const BBNodeAIG topAig = bbAig.BBForm(form);
  const BBNodeGia topGia = bbGia.BBForm(form);

  // The two symbol maps have to name the same bits, in the same order, or
  // the CNF's varOfCi(ordinal) would mean different things on the two
  // backends. Assign each bit its truth-table column by walking them
  // together.
  std::map<int, uint64_t> abcInputs;
  std::map<int, uint64_t> giaInputs;
  unsigned column = 0;

  auto itA = aigMgr.symbolToBBNode.begin();
  auto itG = giaMgr.symbolToBBNode.begin();
  for (; itA != aigMgr.symbolToBBNode.end(); ++itA, ++itG)
  {
    ASSERT_NE(itG, giaMgr.symbolToBBNode.end()) << what;
    ASSERT_EQ(itA->first, itG->first) << what;
    ASSERT_EQ(itA->second.size(), itG->second.size()) << what;

    for (size_t i = 0; i < itA->second.size(); i++)
    {
      const bool nullA = itA->second[i].IsNull();
      ASSERT_EQ(nullA, itG->second[i].IsNull()) << what << " bit " << i;
      if (nullA)
        continue;

      // Same input ordinal on both sides. This is what the CNF seam relies
      // on, and it holds because the blaster mints the inputs in one order.
      ASSERT_EQ(aigMgr.ciOrdinal(itA->second[i]),
                giaMgr.ciOrdinal(itG->second[i]))
          << what << " bit " << i;

      ASSERT_LT(column, 6u) << what << ": too many input bits for one word";
      abcInputs[Aig_ObjId(Aig_Regular(itA->second[i].n))] = INPUT_TT[column];
      giaInputs[Abc_Lit2Var(itG->second[i].n)] = INPUT_TT[column];
      column++;
    }
  }
  ASSERT_EQ(itG, giaMgr.symbolToBBNode.end()) << what;

  const uint64_t a = abcTruthTable(aigMgr.aigMgr, topAig.n, abcInputs);
  const uint64_t g = giaTruthTable(giaMgr.giaMgr, topGia.n, giaInputs);
  EXPECT_EQ(a, g) << what << ": the two backends disagree";
}

// Is `clauses` satisfied by `assignment`, a bitmask indexed by variable?
bool satisfies(const CNF& cnf, uint32_t assignment)
{
  for (uint64_t c = 0; c < cnf.clauseCount(); c++)
  {
    bool ok = false;
    for (const int* l = cnf.clauseBegin(c); l != cnf.clauseEnd(c) && !ok; ++l)
    {
      // 2*variable + negated, which is both ABC's encoding and this class's.
      const uint32_t var = (uint32_t)(*l) >> 1;
      const bool negated = (*l & 1) != 0;
      const bool value = ((assignment >> var) & 1u) != 0;
      ok = (value != negated);
    }
    if (!ok)
      return false;
  }
  return true;
}

} // namespace

// One formula per bit-vector operator the blaster has a circuit for, over
// two three-bit symbols. Three bits is enough to reach every branch of the
// adders, the shifters and the multiplier that width-independent code has,
// and small enough that the whole function fits in one word.
TEST(BitBlasterGia, AgreesWithTheAIGBackend)
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
       mgr.CreateNode(EQ,
                      mgr.CreateTerm(BVEXTRACT, 1, x, mgr.CreateBVConst(32, 2),
                                     mgr.CreateBVConst(32, 2)),
                      mgr.CreateBVConst(1, 1))},
      {"concat", mgr.CreateNode(EQ, mgr.CreateTerm(BVCONCAT, 6, x, y),
                                mgr.CreateBVConst(6, 9))},
      {"sx", mgr.CreateNode(EQ,
                            mgr.CreateTerm(BVSX, 6, x, mgr.CreateBVConst(32, 6)),
                            mgr.CreateBVConst(6, 63))},
      {"ite", mgr.CreateNode(
                  EQ,
                  mgr.CreateTerm(ITE, 3, mgr.CreateNode(BVLT, x, y), x, y),
                  one)},
      {"logical-not", mgr.CreateNode(NOT, mgr.CreateNode(EQ, x, y))},
      {"nested",
       mgr.CreateNode(
           AND, mgr.CreateNode(BVLT, x, y),
           mgr.CreateNode(EQ, mgr.CreateTerm(BVPLUS, 3, x, y), three))},
  };

  for (const auto& c : cases)
    ASSERT_NO_FATAL_FAILURE(expectSameFunction(mgr, c.form, c.name)) << c.name;
}

// Every gate kind the manager offers, at every arity it accepts.
//
// The formula-driven test above cannot reach all of them from bit-vector
// operators alone, and the ones it misses are where a transcription slip
// lives longest.
//
// XOR, IFF and ITE are the ones to watch here in particular. The Aig manager
// needs orderedAigExor and orderedAigMux because Aig_Exor and Aig_Mux2 build
// two nodes inside one argument list, where the evaluation order is
// unspecified; Gia_ManHashXor and Gia_ManHashMux assign their intermediates
// in separate statements, so this backend calls them directly. That is a
// claim about ABC's source, and this is what checks it still computes the
// right function.
TEST(BitBlasterGia, EveryGateKindMatches)
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
      BBNodeManagerGia giaMgr;

      std::vector<BBNodeAIG> aigKids;
      std::vector<BBNodeGia> giaKids;
      std::map<int, uint64_t> abcInputs;
      std::map<int, uint64_t> giaInputs;
      for (unsigned i = 0; i < arity; i++)
      {
        aigKids.push_back(aigMgr.CreateFreshInput());
        giaKids.push_back(giaMgr.CreateFreshInput());
        abcInputs[Aig_ObjId(Aig_Regular(aigKids.back().n))] = INPUT_TT[i];
        giaInputs[Abc_Lit2Var(giaKids.back().n)] = INPUT_TT[i];
      }

      const BBNodeAIG a = aigMgr.CreateNode(k.kind, aigKids);
      const BBNodeGia g = giaMgr.CreateNode(k.kind, giaKids);

      EXPECT_EQ(abcTruthTable(aigMgr.aigMgr, a.n, abcInputs),
                giaTruthTable(giaMgr.giaMgr, g.n, giaInputs))
          << _kind_names[k.kind] << " at arity " << arity;
    }
  }
}

// The budget is the manager's, not ABC's: every backend has to raise the same
// exception at the same place, because every caller that sets a budget
// catches that one type.
TEST(BitBlasterGia, HonoursTheNodeBudget)
{
  STPMgr mgr;

  const ASTNode x = mgr.CreateSymbol("x", 0, 16);
  const ASTNode y = mgr.CreateSymbol("y", 0, 16);
  const ASTNode form = mgr.CreateNode(
      EQ, mgr.CreateTerm(BVMULT, 16, x, y), mgr.CreateBVConst(16, 7));

  SubstitutionMap subs(&mgr);
  Simplifier simp(&mgr, &subs);
  BBNodeManagerGia giaMgr;
  giaMgr.nodeBudget = 10;
  BitBlasterGia bb(&giaMgr, &simp, mgr.defaultNodeFactory, &mgr.UserFlags);

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

// Four bytes, and a null that stays recognisable under negation. Gia literals
// are non-negative, so null is negative and `^1` of it still is -- otherwise
// a negated null would alias literal 0 or 1, which are the two constants.
TEST(BitBlasterGia, TheHandleIsOneLiteral)
{
  EXPECT_EQ(sizeof(BBNodeGia), 4u);
  EXPECT_TRUE(BBNodeGia().IsNull());
  EXPECT_TRUE(BBNodeGia(BBNodeGia().n ^ 1).IsNull());
  EXPECT_FALSE(BBNodeGia(0).IsNull());
  EXPECT_FALSE(BBNodeGia(1).IsNull());
  EXPECT_NE(BBNodeGia(0), BBNodeGia(1));
}

// The premise ToCNFGia is written against, pinned so that it is a measurement
// rather than a belief: this manager's inputs are *not* objects 1..nCi.
//
// Gia_ManFromAig appends every input before any gate, so the converted path
// gets that layout for free and derive_cnf_mf's comment relies on it.
// CreateSymbol mints an input the first time a symbol bit is touched, so here
// they land interleaved. If this test ever fails, the reasoning in ToCNFGia
// about what survives Mf's coarsening no longer has anything to bite on and
// should be re-read rather than deleted.
TEST(BitBlasterGia, InputsLandInterleavedWithGates)
{
  STPMgr mgr;

  // y is not mentioned until after x + x has been built, so its input cannot
  // be among the first objects.
  const ASTNode x = mgr.CreateSymbol("x", 0, 8);
  const ASTNode y = mgr.CreateSymbol("y", 0, 8);
  const ASTNode form = mgr.CreateNode(
      AND,
      mgr.CreateNode(EQ, mgr.CreateTerm(BVPLUS, 8, x, x),
                     mgr.CreateBVConst(8, 6)),
      mgr.CreateNode(EQ, mgr.CreateTerm(BVMULT, 8, y, y),
                     mgr.CreateBVConst(8, 9)));

  SubstitutionMap subs(&mgr);
  Simplifier simp(&mgr, &subs);
  BBNodeManagerGia giaMgr;
  BitBlasterGia bb(&giaMgr, &simp, mgr.defaultNodeFactory, &mgr.UserFlags);
  bb.BBForm(form);

  Gia_Man_t* const p = giaMgr.giaMgr;
  int firstAnd = -1, behind = 0;
  for (int id = 1; id < Gia_ManObjNum(p); id++)
  {
    Gia_Obj_t* const o = Gia_ManObj(p, id);
    if (Gia_ObjIsAnd(o) && firstAnd < 0)
      firstAnd = id;
    if (Gia_ObjIsCi(o) && firstAnd >= 0)
      behind++;
  }
  EXPECT_GT(behind, 0) << "inputs are all ahead of the gates, so this backend "
                          "no longer exercises the case ToCNFGia is written "
                          "for";
}

// The whole seam, end to end and by brute force: does the variable the CNF
// hands back for input k actually carry input k's value?
//
// This is the one thing about this backend that could be wrong silently. Mf
// coarsens the graph before mapping and derives the CNF over that copy, whose
// object ids do not match ours; what makes reading pVarNums by our own id
// sound is that Mf_ManDeriveCnf rebuilds the array against the original,
// bridging by input ordinal. Nothing about that is visible from the outside,
// so it is checked rather than assumed.
//
// The circuit is built through the manager rather than the blaster, so that
// it stays small enough to enumerate every assignment of every CNF variable,
// and with an input minted after a gate so the interleaved layout is the one
// under test. The CNF asserts its output, so it is satisfiable for exactly
// the input assignments that make the circuit true.
TEST(BitBlasterGia, CnfNamesTheRightVariableForEachInput)
{
  BBNodeManagerGia giaMgr;

  // (a & b) ^ (c | !a), with c minted after the first gate.
  const BBNodeGia a = giaMgr.CreateFreshInput();
  const BBNodeGia b = giaMgr.CreateFreshInput();
  const BBNodeGia ab = giaMgr.CreateNode(AND, a, b);
  const BBNodeGia c = giaMgr.CreateFreshInput();
  const BBNodeGia rhs =
      giaMgr.CreateNode(OR, c, giaMgr.CreateNode(NOT, a));
  const BBNodeGia top = giaMgr.CreateNode(XOR, ab, rhs);

  ASSERT_EQ(giaMgr.ciOrdinal(a), 0);
  ASSERT_EQ(giaMgr.ciOrdinal(b), 1);
  ASSERT_EQ(giaMgr.ciOrdinal(c), 2);

  // What the circuit computes, read off the graph before the CNF exists.
  std::map<int, uint64_t> inputs;
  inputs[Abc_Lit2Var(a.n)] = INPUT_TT[0];
  inputs[Abc_Lit2Var(b.n)] = INPUT_TT[1];
  inputs[Abc_Lit2Var(c.n)] = INPUT_TT[2];
  const uint64_t expected = giaTruthTable(giaMgr.giaMgr, top.n, inputs);

  UserDefinedFlags uf;
  uf.cnf_effort = UserDefinedFlags::CNF_EFFORT_GIA_LOW;
  ToSATBase::ASTNodeToSATVar nodeToVars;
  CNF cnf;
  ToCNFGia(uf).toCNF(top, cnf, nodeToVars, false, giaMgr);

  ASSERT_EQ(cnf.ciCount(), 3u);
  const uint32_t va = cnf.varOfCi(0), vb = cnf.varOfCi(1),
                 vc = cnf.varOfCi(2);
  ASSERT_NE(va, 0u);
  ASSERT_NE(vb, 0u);
  ASSERT_NE(vc, 0u);
  ASSERT_LT(va, cnf.varCount());
  ASSERT_LT(vb, cnf.varCount());
  ASSERT_LT(vc, cnf.varCount());
  ASSERT_TRUE(va != vb && vb != vc && va != vc) << "inputs share a variable";

  // Enumerate. Variable 0 does not exist, so bit 0 of the mask is unused.
  ASSERT_LT(cnf.varCount(), 24u) << "too large to enumerate; shrink the test";
  ASSERT_FALSE(cnf.hasEmptyClause());

  for (unsigned pattern = 0; pattern < 8; pattern++)
  {
    // Column `pattern` of the three input truth tables is one assignment.
    const bool wa = ((INPUT_TT[0] >> pattern) & 1ull) != 0;
    const bool wb = ((INPUT_TT[1] >> pattern) & 1ull) != 0;
    const bool wc = ((INPUT_TT[2] >> pattern) & 1ull) != 0;
    const bool want = ((expected >> pattern) & 1ull) != 0;

    bool found = false;
    for (uint32_t m = 0; m < (1u << cnf.varCount()) && !found; m++)
    {
      if ((((m >> va) & 1u) != 0) != wa)
        continue;
      if ((((m >> vb) & 1u) != 0) != wb)
        continue;
      if ((((m >> vc) & 1u) != 0) != wc)
        continue;
      found = satisfies(cnf, m);
    }

    EXPECT_EQ(found, want)
        << "assignment a=" << wa << " b=" << wb << " c=" << wc
        << ": the CNF is " << (found ? "" : "un") << "satisfiable but the "
        << "circuit says " << want;
  }
}

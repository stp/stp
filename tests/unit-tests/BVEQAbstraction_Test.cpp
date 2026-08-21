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

#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/BVAbstractionRefiner.h"

#include <gtest/gtest.h>

#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

class BVEQAbstractionTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* factory;

  void SetUp() override { factory = mgr.defaultNodeFactory; }

  ASTNode makeSymbol(const char* name, unsigned width)
  {
    return mgr.CreateSymbol(name, 0, width);
  }
};

// A candidate is only an assignment of the query once every abstraction in it
// has been checked against the operands it stands for. Refinement checks them
// by reading the operands' bits out of one map from node to SAT variables, and
// the four tests below hand it a map that cannot answer: an operand missing
// altogether, an operand with fewer bits than the record claims, an operand
// with a bit that never reached the CNF, and a comparison with no input of its
// own. None of the four can arise -- the blaster registers everything it
// abstracts, the widths are the same node's, and both lowerings carry the
// whole registry across -- but each used to be treated as though the
// abstraction had been checked and found consistent, which for an
// over-approximation means certified: a record nothing can contradict lets the
// search satisfy the query by giving the abstraction whatever value suits it,
// and an unsatisfiable query comes back sat.
//
// Reading the bits regardless is no better: past the end of the vector is an
// out-of-bounds read, and ~0u is a variable the backend does not have.
class NoModelSolver : public SATSolver
{
public:
  bool okay() const override { return true; }
  // Every abstraction reads as false, which is a candidate like any other.
  uint8_t modelValue(uint32_t) const override { return false_literal(); }
  uint32_t newVar() override { return next++; }
  uint32_t nVars() const override { return next; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals&) override { return true; }
  bool solveInternal(bool&) override { return true; }

private:
  uint32_t next = 1;
};

// A backend that records what STP does to it: the model is scripted per
// variable (anything unscripted reads false), every added clause is kept
// decoded, and setFrozen calls land in a set. Variables number from zero so
// ToSATAIG::CallSAT's fresh-solver assertion holds and add_cnf_to_solver can
// allocate the CNF's variables here.
class RecordingSolver : public SATSolver
{
public:
  std::map<uint32_t, bool> model;
  // Each clause as (variable, negated) pairs, in push order.
  std::vector<std::vector<std::pair<uint32_t, bool>>> clauses;
  std::set<uint32_t> frozen;
  uint32_t newVarCalls = 0;

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t v) const override
  {
    auto it = model.find(v);
    return (it != model.end() && it->second) ? true_literal()
                                             : false_literal();
  }
  uint32_t newVar() override
  {
    newVarCalls++;
    return next++;
  }
  uint32_t nVars() const override { return next; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  void setFrozen(uint32_t v) override { frozen.insert(v); }
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

  // TRUE when the scripted model falsifies every literal of some recorded
  // clause -- that clause rules the model out. Only clauses written
  // entirely over scripted variables count: a clause naming a variable the
  // model does not script (a fresh Tseitin helper, say) constrains the
  // helper, not the candidate. A literal (var, negated) is false exactly
  // when the scripted value equals its negation flag.
  bool someClauseBlocksModel() const
  {
    for (const auto& clause : clauses)
    {
      bool blocked = !clause.empty();
      for (const auto& lit : clause)
      {
        auto it = model.find(lit.first);
        if (it == model.end() || it->second != lit.second)
        {
          blocked = false;
          break;
        }
      }
      if (blocked)
        return true;
    }
    return false;
  }

protected:
  bool addClauseInternal(const vec_literals& ps) override
  {
    std::vector<std::pair<uint32_t, bool>> clause;
    for (int i = 0; i < ps.size(); i++)
      clause.push_back({SATSolver::var(ps[i]), SATSolver::sign(ps[i])});
    clauses.push_back(clause);
    return true;
  }
  bool solveInternal(bool&) override { return true; }

private:
  uint32_t next = 0;
};

// Refinement writes clauses over the records' own variables and the
// operands' bits in later solve calls, so every one of them has to be
// frozen before a simplifying backend's first solve can eliminate it. A
// ~0u entry is the pre-solve "not there yet" state and must be skipped,
// not handed to the backend as a variable index.
TEST_F(BVEQAbstractionTest, FreezeVariablesCoversEveryLemmaVariable)
{
  ASTNode x = makeSymbol("fz_x", 4);
  ASTNode y = makeSymbol("fz_y", 4);
  ASTNode sum = factory->CreateTerm(BVPLUS, 4, x, y);

  BVAbstractionRefiner refiner(&mgr);

  BVEQAbstraction eq;
  eq.eqNode = factory->CreateNode(EQ, x, y);
  eq.abstractionSATVar = 5;
  eq.leftSymbol = x;
  eq.rightSymbol = y;
  eq.width = 4;
  refiner.equalities().push_back(eq);

  // Harvested with no variable yet: legal before the first solve, skipped.
  BVEQAbstraction pending = eq;
  pending.abstractionSATVar = BV_ABSTRACTION_NO_VAR;
  refiner.equalities().push_back(pending);

  BVTermAbstraction term;
  term.termNode = sum;
  term.opKind = BVPLUS;
  term.operands[0] = x;
  term.operands[1] = y;
  term.numOperands = 2;
  term.width = 4;
  refiner.terms().push_back(term);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, BV_ABSTRACTION_NO_VAR, 23};
  bits[sum] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  refiner.freezeVariables(solver, bits);

  const std::set<uint32_t> expected = {5,  10, 11, 12, 13, 20,
                                       21, 23, 30, 31, 32, 33};
  EXPECT_EQ(expected, solver.frozen);
}

// A partial prefix says nothing to a candidate that called the equality
// false over agreeing bits: every prefix clause is conditioned on the
// Boolean being true, so the identical candidate could come back round
// after round until the definition completed, one full solve per doubling
// of the prefix. Such a round must also emit a clause the candidate
// violates -- the definition's consequence at the candidate's own value:
// if both sides hold that value, the equality is true.
TEST_F(BVEQAbstractionTest, SaidUnequalRoundBlocksTheCandidate)
{
  mgr.UserFlags.bv_eq_refine_width = 1;

  ASTNode x = makeSymbol("cb_x", 4);
  ASTNode y = makeSymbol("cb_y", 4);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 5;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 4;
  refiner.equalities().push_back(record);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, 22, 23};

  RecordingSolver solver;
  // The candidate: the abstraction says unequal, while both operands hold
  // 0b0101. Nothing in a one-bit prefix can contradict that.
  solver.model[5] = false;
  solver.model[10] = true;
  solver.model[11] = false;
  solver.model[12] = true;
  solver.model[13] = false;
  solver.model[20] = true;
  solver.model[21] = false;
  solver.model[22] = true;
  solver.model[23] = false;

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  // The prefix still grew -- the blocking clause is in addition to the
  // definition's progress, not instead of it.
  EXPECT_EQ(1u, refiner.equalities()[0].refinedBits);
  EXPECT_FALSE(refiner.equalities()[0].defined);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// A defined equality's Boolean is exact, so transitivity chains are free
// to run through it. The word-level phase used to leave defined records
// out, which broke exactly the chains that mature first: a conflict whose
// path crossed one fell through to the bit-level scan and was rediscovered
// a definition at a time. Here x=y is already defined and true, y=z is
// asserted true, x!=z is asserted -- one congruence clause refutes the
// candidate without touching a bit, which the untouched refinedBits of the
// disequality's record is the witness for.
TEST_F(BVEQAbstractionTest, CongruenceChainsRunThroughDefinedEqualities)
{
  ASTNode x = makeSymbol("cc_x", 4);
  ASTNode y = makeSymbol("cc_y", 4);
  ASTNode z = makeSymbol("cc_z", 4);

  BVAbstractionRefiner refiner(&mgr);

  BVEQAbstraction xy;
  xy.eqNode = factory->CreateNode(EQ, x, y);
  xy.abstractionSATVar = 5;
  xy.leftSymbol = x;
  xy.rightSymbol = y;
  xy.width = 4;
  xy.defined = true;
  xy.refinedBits = 4;
  refiner.equalities().push_back(xy);

  BVEQAbstraction yz;
  yz.eqNode = factory->CreateNode(EQ, y, z);
  yz.abstractionSATVar = 6;
  yz.leftSymbol = y;
  yz.rightSymbol = z;
  yz.width = 4;
  refiner.equalities().push_back(yz);

  BVEQAbstraction xz;
  xz.eqNode = factory->CreateNode(EQ, x, z);
  xz.abstractionSATVar = 7;
  xz.leftSymbol = x;
  xz.rightSymbol = z;
  xz.width = 4;
  refiner.equalities().push_back(xz);

  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>{10, 11, 12, 13};
  bits[y] = std::vector<unsigned>{20, 21, 22, 23};
  bits[z] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  // Unscripted bit variables read false, so all three operands hold zero:
  // every record is bit-level consistent or Case-B, and only the chain
  // through the defined x=y refutes the candidate at word level.
  solver.model[5] = true;
  solver.model[6] = true;
  solver.model[7] = false;

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(0u, refiner.equalities()[2].refinedBits);
  EXPECT_FALSE(refiner.equalities()[2].defined);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

// A blocking round on a multiplication is one clause per result bit and
// nothing else: both operands' variables come out of the registry -- the
// blaster proxies constants too, pinning them by biconditionals -- so
// refinement has no variables to mint. It used to mint a fresh pinned
// vector for a constant operand on every round of the enumeration.
TEST_F(BVEQAbstractionTest, BlockingRoundReusesTheRegisteredConstant)
{
  ASTNode a = makeSymbol("mc_a", 4);
  ASTNode three = mgr.CreateBVConst(4, 3);
  ASTNode product = factory->CreateTerm(BVMULT, 4, a, three);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = product;
  record.opKind = BVMULT;
  record.operands[0] = a;
  record.operands[1] = three;
  record.numOperands = 2;
  record.width = 4;
  refiner.terms().push_back(record);

  ToSATBase::ASTNodeToSATVar bits;
  bits[a] = std::vector<unsigned>{10, 11, 12, 13};
  bits[three] = std::vector<unsigned>{20, 21, 22, 23};
  bits[product] = std::vector<unsigned>{30, 31, 32, 33};

  RecordingSolver solver;
  // a = 2 and the proxies hold the constant's own value 3, as their
  // biconditionals force; the abstraction's result reads 0 where 2 * 3
  // is 6, so the round owes a blocking lemma. Every variable is scripted
  // explicitly, so the clause check below can evaluate whole clauses.
  const bool scripted[12] = {false, true, false, false,  // a = 0b0010
                             true,  true, false, false,  // proxies = 0b0011
                             false, false, false, false}; // result = 0
  for (unsigned i = 0; i < 4; i++)
  {
    solver.model[10 + i] = scripted[i];
    solver.model[20 + i] = scripted[4 + i];
    solver.model[30 + i] = scripted[8 + i];
  }

  EXPECT_EQ(1u, refiner.refine(solver, bits));
  EXPECT_EQ(1u, refiner.terms()[0].blockedRounds);
  EXPECT_FALSE(refiner.terms()[0].defined);
  EXPECT_EQ(0u, solver.newVarCalls);
  EXPECT_TRUE(solver.someClauseBlocksModel());
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityWhoseOperandsAreNotEncoded)
{
  ASTNode x = makeSymbol("nb_x", 8);
  ASTNode y = makeSymbol("nb_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  refiner.equalities().push_back(record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar empty;
  EXPECT_DEATH(refiner.refine(solver, empty), "did not encode");
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityRecordedWiderThanItsOperands)
{
  ASTNode x = makeSymbol("nw_x", 8);
  ASTNode y = makeSymbol("nw_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  refiner.equalities().push_back(record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>(4, 2); // four bits for an eight-bit record
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "recorded wider");
}

TEST_F(BVEQAbstractionTest, RefusesAnEqualityBitThatNeverReachedTheCNF)
{
  ASTNode x = makeSymbol("nc_x", 8);
  ASTNode y = makeSymbol("nc_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVEQAbstraction record;
  record.eqNode = factory->CreateNode(EQ, x, y);
  record.abstractionSATVar = 1;
  record.leftSymbol = x;
  record.rightSymbol = y;
  record.width = 8;
  refiner.equalities().push_back(record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  std::vector<unsigned> partial(8, 2);
  partial[7] = BV_ABSTRACTION_NO_VAR;
  bits[x] = partial;
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "never reached the CNF");
}

TEST_F(BVEQAbstractionTest, RefusesAnAdditionWhoseOperandsAreNotEncoded)
{
  ASTNode x = makeSymbol("na_x", 8);
  ASTNode y = makeSymbol("na_y", 8);
  ASTNode sum = factory->CreateTerm(BVPLUS, 8, x, y);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = sum;
  record.opKind = BVPLUS;
  record.operands[0] = x;
  record.operands[1] = y;
  record.numOperands = 2;
  record.width = 8;
  refiner.terms().push_back(record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  // The abstraction's own result bits are there; the operands it stands for
  // are not, which is the half the scan reads to decide whether the candidate
  // contradicts it.
  bits[sum] = std::vector<unsigned>(8, 4);
  EXPECT_DEATH(refiner.refine(solver, bits), "did not encode");
}

TEST_F(BVEQAbstractionTest, RefusesAComparisonWithNoInputOfItsOwn)
{
  ASTNode x = makeSymbol("nk_x", 8);
  ASTNode y = makeSymbol("nk_y", 8);

  BVAbstractionRefiner refiner(&mgr);
  BVTermAbstraction record;
  record.termNode = factory->CreateNode(BVSLT, x, y);
  record.opKind = BVSLT;
  record.operands[0] = x;
  record.operands[1] = y;
  record.numOperands = 2;
  record.width = 8;
  // condSATVar left at BV_ABSTRACTION_NO_VAR: the comparison's answer has
  // nowhere to be read from, so nothing about this candidate can be checked.
  refiner.terms().push_back(record);

  NoModelSolver solver;
  ToSATBase::ASTNodeToSATVar bits;
  bits[x] = std::vector<unsigned>(8, 2);
  bits[y] = std::vector<unsigned>(8, 3);
  EXPECT_DEATH(refiner.refine(solver, bits), "no input carrying its answer");
}

} // namespace

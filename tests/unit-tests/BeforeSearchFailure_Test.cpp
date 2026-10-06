/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Oct, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"

#include <gtest/gtest.h>

#include <memory>
#include <string>

// A before-search callback (ToSATBase::setBeforeSearch) that returns false
// abandons the solve: runSolver records an internal solve failure and does
// not search. That is never a refutation. It used to become one on every
// check without an arithmetic coordinator: CallSAT_ResultCheck consulted the
// failure only when a coordinator was present, so the solver's "not
// satisfiable" fell through to UNSAT. And the failure outlived its solve: an
// encoder reused for a later solve (a refinement round, a persistent Real
// session) kept it and abandoned that solve as well.
//
// The batch pipeline builds its encoder per solve, so these tests drive
// CallSAT_ResultCheck directly with one of their own, exactly as STP does.

using namespace stp;

namespace
{

class BeforeSearchFailureTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* factory = nullptr;
  std::unique_ptr<STP> stp;
  std::unique_ptr<SATSolver> solver;
  std::unique_ptr<ToSATAIG> encoder;
  ASTNode formula;

  void SetUp() override
  {
    factory = mgr.defaultNodeFactory;
    stp.reset(new STP(&mgr));
    solver.reset(createSATSolver(mgr.UserFlags));
    encoder.reset(new ToSATAIG(&mgr, stp->arrayTransformer));
    formula = unsatProduct();
    mgr.clearUnknown();
  }

  // x * y = 13 with 1 < x, y < 256 over 16 bits: no overflow, and 13 is
  // prime, so the formula is UNSAT, and the encoder hands it to the SAT
  // backend (nothing simplifies it here).
  ASTNode unsatProduct()
  {
    ASTNode x = mgr.CreateSymbol("bsf_x", 0, 16);
    ASTNode y = mgr.CreateSymbol("bsf_y", 0, 16);
    ASTNode one = mgr.CreateBVConst(16, 1);
    ASTNode bound = mgr.CreateBVConst(16, 256);
    ASTNode thirteen = mgr.CreateBVConst(16, 13);
    ASTVec conjuncts;
    conjuncts.push_back(factory->CreateNode(
        EQ, factory->CreateTerm(BVMULT, 16, x, y), thirteen));
    conjuncts.push_back(factory->CreateNode(BVGT, x, one));
    conjuncts.push_back(factory->CreateNode(BVGT, y, one));
    conjuncts.push_back(factory->CreateNode(BVLT, x, bound));
    conjuncts.push_back(factory->CreateNode(BVLT, y, bound));
    return factory->CreateNode(AND, conjuncts);
  }

  SOLVER_RETURN_TYPE check(const ASTNode& input)
  {
    return stp->Ctr_Example->CallSAT_ResultCheck(*solver, input, formula,
                                                 formula, encoder.get(), false,
                                                 nullptr);
  }
};

TEST_F(BeforeSearchFailureTest, AbandonedSearchIsUnknownNotUnsat)
{
  unsigned calls = 0;
  encoder->setBeforeSearch([&calls]() {
    ++calls;
    return false;
  });
  const SOLVER_RETURN_TYPE result = check(formula);
  // The fixture must reach the SAT backend, or this proves nothing.
  ASSERT_EQ(1u, calls);
  EXPECT_NE(SOLVER_VALID, result);
  EXPECT_EQ(SOLVER_UNKNOWN, result);
  EXPECT_EQ(UnknownReason::Incomplete, mgr.getUnknownReason());
  EXPECT_NE(std::string::npos,
            mgr.getUnknownReasonDetail().find("before SAT search"))
      << mgr.getUnknownReasonDetail();
}

TEST_F(BeforeSearchFailureTest, FailureDoesNotOutliveItsSolve)
{
  encoder->setBeforeSearch([]() { return false; });
  EXPECT_NE(SOLVER_VALID, check(formula));
  // The callback went with its check. The encoder's next solve -- the way a
  // refinement round reuses it, with the CNF already in the backend --
  // searches, and refutes.
  mgr.clearUnknown();
  EXPECT_EQ(SOLVER_VALID, check(mgr.ASTTrue));
}

TEST_F(BeforeSearchFailureTest, ProceedingCallbackSearches)
{
  unsigned calls = 0;
  encoder->setBeforeSearch([&calls]() {
    ++calls;
    return true;
  });
  EXPECT_EQ(SOLVER_VALID, check(formula));
  ASSERT_EQ(1u, calls);
}

} // namespace

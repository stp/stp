/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// The word-level solver eliminates a variable by recording a
// replacement for it in the solver map. A float's format is per-node
// state that only a leaf, a floating-point-kind node or an array can
// hold (see ASTNode::canStoreFPFormat), so the bitvector terms the
// solver builds -- a fresh variable concatenated with the solved bits,
// a multiple of the right-hand side -- carry none, and eliminating a
// float-typed variable into one drops its format.
//
// That matters because the solver runs while the floating-point layer
// is still unlowered: FloatBlast comes after the size-reducing passes
// and reads an operation's format off its operands, which by then are
// the only thing that still says what sort they are. A float-typed
// variable rewritten into a concatenation left fp.isZero blasting
// against a format of (0, 0) -- a packed width of zero against a
// 64-bit operand -- and the blaster aborted:
//
//   symbolic_fp.cpp: blast_is_zero: Assertion
//     `expr.GetValueWidth() == size.packedWidth()' failed.
//
// The equations below are the shapes the solver knows how to take
// apart, over a float-typed variable. See
// fp-array-extensionality.cpp's
// float_cell_pinned_under_chain_equality_unsat for the fuzzer's query
// that produced the first of them.

#include "stp/Simplifier/BVSolver.h"
#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

const unsigned int EXP_WIDTH = 11;
const unsigned int SIG_WIDTH = 53;
const unsigned int FLOAT_WIDTH = EXP_WIDTH + SIG_WIDTH;

struct Fixture
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  SubstitutionMap sm;
  Simplifier simp;
  BVSolver solver;

  Fixture()
      : snf(*(mgr.hashingNodeFactory), mgr), sm(&mgr), simp(&mgr, &sm),
        solver(&mgr, &simp)
  {
    mgr.defaultNodeFactory = &snf;
  }

  // A Float64 variable, made the way the array transformer makes one
  // for a read of a float-element array: a symbol as wide as the
  // packed format, carrying that format.
  ASTNode floatVar(const char* name)
  {
    ASTNode f = mgr.CreateSymbol(name, 0, FLOAT_WIDTH);
    f.SetExpWidth(EXP_WIDTH);
    f.SetSigWidth(SIG_WIDTH);
    return f;
  }

  ASTNode extract(const ASTNode& term, unsigned int high, unsigned int low)
  {
    return mgr.CreateTerm(BVEXTRACT, high - low + 1, term,
                          mgr.CreateBVConst(32, high),
                          mgr.CreateBVConst(32, low));
  }

  // Whether the format survives solving: what an fp.isZero over `f`
  // reads as its operand, once the solver map has been applied, must
  // still be a Float64. That is exactly what the blaster asks the
  // operand for.
  void operandKeepsFormat(const ASTNode& f)
  {
    const ASTNode after = simp.applySubstitutionMap(mgr.CreateNode(FP_ISZERO, f));
    ASSERT_EQ(1u, after.Degree());
    EXPECT_EQ(EXP_WIDTH, after[0].GetExpWidth());
    EXPECT_EQ(SIG_WIDTH, after[0].GetSigWidth());
    EXPECT_EQ(FLOAT_WIDTH, after[0].GetValueWidth());
  }
};

} // namespace

// (= ((_ extract 51 0) f) #x0000000000000): a float's significand half
// pinned to a constant, which is what the extensional array
// procedure's NaN test leaves behind once the float it compares
// against is a known constant. Solving this renames f itself, to a
// fresh 12-bit variable concatenated with the solved 52 bits.
TEST(BVSolver, float_variable_survives_low_extract_equation)
{
  Fixture f;

  const ASTNode x = f.floatVar("x");
  const ASTNode eq = f.mgr.CreateNode(
      EQ, f.extract(x, SIG_WIDTH - 2, 0), f.mgr.CreateZeroConst(SIG_WIDTH - 1));

  f.solver.TopLevelBVSolve(eq, false);

  f.operandKeepsFormat(x);
}

// (= (bvmul #x3 f) #x0): an odd coefficient over the whole variable.
// Solving multiplies through by the coefficient's inverse, and
// replaces f by the product -- another term with no format.
TEST(BVSolver, float_variable_survives_odd_coefficient_equation)
{
  Fixture f;

  const ASTNode x = f.floatVar("x");
  const ASTNode product = f.mgr.CreateTerm(
      BVMULT, FLOAT_WIDTH, f.mgr.CreateBVConst(FLOAT_WIDTH, 3), x);
  const ASTNode eq =
      f.mgr.CreateNode(EQ, product, f.mgr.CreateZeroConst(FLOAT_WIDTH));

  f.solver.TopLevelBVSolve(eq, false);

  f.operandKeepsFormat(x);
}

// A whole float variable equated to a plain bitvector term. The term
// denotes the same 64 bits, but carries no format for the blaster to
// read, so it cannot stand in for the variable.
TEST(BVSolver, float_variable_survives_formatless_replacement)
{
  Fixture f;

  const ASTNode x = f.floatVar("x");
  const ASTNode bits = f.mgr.CreateSymbol("bits", 0, FLOAT_WIDTH);
  const ASTNode eq =
      f.mgr.CreateNode(EQ, x, f.mgr.CreateTerm(BVNOT, FLOAT_WIDTH, bits));

  f.solver.TopLevelBVSolve(eq, false);

  f.operandKeepsFormat(x);
}

// The same equations over a plain bitvector variable are still solved:
// the guard is about formats, and a non-float has none to lose.
TEST(BVSolver, plain_bitvector_variable_is_still_solved)
{
  Fixture f;

  const ASTNode x = f.mgr.CreateSymbol("x", 0, FLOAT_WIDTH);
  const ASTNode eq = f.mgr.CreateNode(
      EQ, f.extract(x, SIG_WIDTH - 2, 0), f.mgr.CreateZeroConst(SIG_WIDTH - 1));

  EXPECT_EQ(f.mgr.ASTTrue, f.solver.TopLevelBVSolve(eq, false));
  EXPECT_TRUE(f.simp.InsideSubstitutionMap(x));
}

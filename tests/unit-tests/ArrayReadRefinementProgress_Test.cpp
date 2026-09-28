// The ordinary array refinement loop must measure logical progress. Every
// invocation of getEquals builds fresh CNF, so solver growth alone cannot say
// whether the corresponding congruence axiom was new.

#include "stp/AbsRefineCounterExample/ArrayReadRefinementProgress.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Fixture
{
  STPMgr mgr;
  ASTNode i0;
  ASTNode i1;
  ASTNode v0;
  ASTNode v1;
  ToSATBase::ASTNodeToSATVar bindings;

  Fixture()
      : i0(mgr.CreateSymbol("progress_i0", 0, 4)),
        i1(mgr.CreateSymbol("progress_i1", 0, 4)),
        v0(mgr.CreateSymbol("progress_v0", 0, 8)),
        v1(mgr.CreateSymbol("progress_v1", 0, 8))
  {
    bind(i0, 0);
    bind(i1, 4);
    bind(v0, 8);
    bind(v1, 16);
  }

  void bind(const ASTNode& n, unsigned first)
  {
    std::vector<unsigned> vars;
    for (unsigned i = 0; i < n.GetValueWidth(); ++i)
      vars.push_back(first + i);
    bindings[n] = vars;
  }
};

TEST(ArrayReadRefinementProgress, ClaimsEachLogicalAxiomOnlyOncePerCheck)
{
  Fixture f;
  ArrayReadRefinementProgress progress;

  EXPECT_TRUE(progress.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));
  EXPECT_EQ(1u, progress.emittedAxiomCount());
  EXPECT_FALSE(progress.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));
  EXPECT_EQ(1u, progress.emittedAxiomCount());

  // Swapping only the values is a different implication and must not be
  // suppressed merely because it mentions the same four leaves.
  EXPECT_TRUE(progress.claim(f.i0, f.i1, f.v1, f.v0, f.bindings));
  EXPECT_EQ(2u, progress.emittedAxiomCount());
}

TEST(ArrayReadRefinementProgress, ANewCheckStartsANewTransaction)
{
  Fixture f;
  ArrayReadRefinementProgress first;
  ArrayReadRefinementProgress second;

  EXPECT_TRUE(first.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));
  EXPECT_FALSE(first.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));
  EXPECT_TRUE(second.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));
}

TEST(ArrayReadRefinementProgress, RejectsBindingChangesInsideOneCheck)
{
  Fixture f;
  ArrayReadRefinementProgress progress;
  ASSERT_TRUE(progress.claim(f.i0, f.i1, f.v0, f.v1, f.bindings));

  // A SAT rebuild or a throwaway remapping inside a refinement transaction
  // would make suppression unsound and repeated emission non-terminating.
  f.bind(f.v1, 100);
  EXPECT_DEATH(
      progress.claim(f.i0, f.i1, f.v0, f.v1, f.bindings),
      "changed an axiom leaf's SAT binding inside one check-sat");
}

} // namespace

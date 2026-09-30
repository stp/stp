// LICENSE: Please view LICENSE in the source root.

#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerLit.h"
#include "stp/ToSat/BitBlaster.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{
void expectEncoding(unsigned width, Kind kind, bool relational,
                    unsigned threshold = 0, bool enabled = true)
{
  STPMgr manager;
  if (threshold != 0)
    manager.UserFlags.division_by_constant_width = threshold;
  manager.UserFlags.division_by_constant = enabled;
  SubstitutionMap substitutions(&manager);
  Simplifier simplifier(&manager, &substitutions);
  BBNodeManagerLit nodes;
  BitBlasterLit blaster(&nodes, &simplifier, manager.defaultNodeFactory,
                       &manager.UserFlags);
  const ASTNode dividend =
      manager.CreateSourceSymbol("dividend", SourceSort::bitVector(width));
  const ASTNode divisor = manager.CreateBVConst(width, 11);
  const ASTNode term = manager.CreateTerm(kind, width, dividend, divisor);
  BBNodeOrderedSet<BBNodeLit> support;
  const auto bits = blaster.BBTerm(term, support);
  ASSERT_EQ(bits.size(), width);

  // A forward divider computes its answer from the dividend's bits alone.
  // A defining relation introduces anonymous quotient/remainder inputs whose
  // values SAT has to discover. Check that actual behavior, not gate counts.
  if (relational)
    EXPECT_GT(nodes.mgr.ciCount(), width);
  else
    EXPECT_EQ(nodes.mgr.ciCount(), width);
}
} // namespace

TEST(ConstantDivisionPolicy, intermediate_widths_keep_forward_propagation)
{
  for (Kind kind : {BVDIV, BVMOD})
    for (unsigned width : {63u, 64u, 97u, 127u})
      expectEncoding(width, kind, false);
}

TEST(ConstantDivisionPolicy, wide_division_keeps_compact_relation)
{
  for (Kind kind : {BVDIV, BVMOD})
    for (unsigned width : {128u, 129u, 256u})
      expectEncoding(width, kind, true);
}

TEST(ConstantDivisionPolicy, explicit_policy_overrides_remain_effective)
{
  for (Kind kind : {BVDIV, BVMOD})
  {
    expectEncoding(97, kind, true, 64);
    expectEncoding(128, kind, false, 256);
    expectEncoding(128, kind, false, 64, false);
  }
}

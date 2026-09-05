// Optional incremental policies remain separable from the correctness core.

#include "stp/Incremental/IncrementalPolicy.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

TEST(IncrementalPolicy, FullProfileEnablesOptionalPolicies)
{
  const IncrementalPolicy policy(false);
  EXPECT_FALSE(policy.coreOnly());
  EXPECT_TRUE(policy.crossLevelPropagation());
  EXPECT_TRUE(policy.semanticPreprocessing());
  EXPECT_TRUE(policy.firstSolveShortcuts());
  EXPECT_TRUE(policy.unitPromotion());
  EXPECT_TRUE(policy.adaptiveBackendConfiguration());
  EXPECT_TRUE(policy.aggregateLevelAssumptions());
  EXPECT_TRUE(policy.retractionSearchHints());
  EXPECT_TRUE(policy.rotateEncodingEpochForRelief());
}

TEST(IncrementalPolicy, CoreProfileKeepsOnlyRequiredResourcePolicy)
{
  const IncrementalPolicy policy(true);
  EXPECT_TRUE(policy.coreOnly());
  EXPECT_FALSE(policy.crossLevelPropagation());
  EXPECT_FALSE(policy.semanticPreprocessing());
  EXPECT_FALSE(policy.firstSolveShortcuts());
  EXPECT_FALSE(policy.unitPromotion());
  EXPECT_FALSE(policy.adaptiveBackendConfiguration());
  EXPECT_FALSE(policy.aggregateLevelAssumptions());
  EXPECT_FALSE(policy.retractionSearchHints());
  EXPECT_TRUE(policy.rotateEncodingEpochForRelief());
}

} // namespace

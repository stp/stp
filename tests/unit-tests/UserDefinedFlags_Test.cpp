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

#include "stp/STPManager/UserDefinedFlags.h"
#include <gtest/gtest.h>

#include <string>

// --disable-simplifications owns the whole stack: the bulk setter must
// switch all of it off.
TEST(UserDefinedFlags_Test, disable_simplifications_clears_flattening_stack)
{
  stp::UserDefinedFlags uf;
  uf.disableSimplifications();
  EXPECT_FALSE(uf.enable_flatten);
  EXPECT_FALSE(uf.enable_common_subsum);
  EXPECT_FALSE(uf.enable_pair_extract);
}

// A rewrite that defaults on has to be reachable by the same escape hatch as
// the rest: --disable-simplifications is how a wrong answer gets bisected down
// to a minimal pipeline, and a rewrite that survives it is never bisected out.
TEST(UserDefinedFlags_Test, disable_simplifications_clears_distinct_ordering)
{
  stp::UserDefinedFlags uf;
  EXPECT_TRUE(uf.distinct_ordering);
  uf.disableSimplifications();
  EXPECT_FALSE(uf.distinct_ordering);
}

TEST(UserDefinedFlags_Test, caller_model_request_is_derived_from_source_flags)
{
  stp::UserDefinedFlags uf;
  EXPECT_FALSE(uf.callerRequestedModel());

  uf.produce_models = true;
  EXPECT_TRUE(uf.callerRequestedModel());
  uf.produce_models = false;

  uf.request_counterexample = true;
  EXPECT_TRUE(uf.callerRequestedModel());
  uf.request_counterexample = false;

  uf.print_counterexample_flag = true;
  EXPECT_TRUE(uf.callerRequestedModel());
  uf.print_counterexample_flag = false;

  uf.check_counterexample_flag = true;
  EXPECT_TRUE(uf.callerRequestedModel());
}

TEST(UserDefinedFlags_Test, internal_model_consumer_is_a_separate_input)
{
  stp::UserDefinedFlags uf;
  EXPECT_FALSE(uf.callerRequestedModel());
  EXPECT_TRUE(uf.modelConstructionRequired(true));
#ifdef NDEBUG
  EXPECT_FALSE(uf.modelConstructionRequired(false));
#else
  EXPECT_TRUE(uf.modelConstructionRequired(false));
#endif
}

TEST(UserDefinedFlags_Test, every_bv_schema_group_round_trips_by_name)
{
  for (unsigned i = 0; i < stp::BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const stp::BVSchemaGroup group = static_cast<stp::BVSchemaGroup>(i);
    const uint32_t expected = stp::bvSchemaGroupBit(group);
    uint32_t parsed = 0;
    std::string error;
    ASSERT_TRUE(
        stp::parseBVSchemaGroups(stp::bvSchemaGroupName(group), parsed, error))
        << error;
    EXPECT_EQ(expected, parsed);
    EXPECT_EQ(stp::bvSchemaGroupName(group), stp::formatBVSchemaGroups(parsed));
    for (unsigned j = 0; j < stp::BV_SCHEMA_GROUP_COUNT; ++j)
      EXPECT_EQ(i == j, stp::bvSchemaGroupEnabled(
                            parsed, static_cast<stp::BVSchemaGroup>(j)));
  }
}
TEST(UserDefinedFlags_Test, bv_schema_group_aliases_and_lists_parse)
{
  uint32_t parsed = 123;
  std::string error;
  ASSERT_TRUE(stp::parseBVSchemaGroups("all", parsed, error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_ALL, parsed);
  EXPECT_EQ("all", stp::formatBVSchemaGroups(parsed));

  ASSERT_TRUE(stp::parseBVSchemaGroups("none", parsed, error));
  EXPECT_EQ(0u, parsed);
  EXPECT_EQ("none", stp::formatBVSchemaGroups(parsed));

  ASSERT_TRUE(
      stp::parseBVSchemaGroups(" mul-ref3, base, urem,base ", parsed, error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_QUALIFIED, parsed);
  // Formatting is canonical enum order, independent of input order.
  EXPECT_EQ("base,urem,mul-ref3", stp::formatBVSchemaGroups(parsed));

  ASSERT_TRUE(stp::parseBVSchemaGroups(
      "base,udiv,urem,mul6,mul8,quotient-one", parsed, error));
  EXPECT_EQ("base,udiv15,udiv-observed,urem,quotient-one-quot,"
            "quotient-one-rem,mul8,mul-ref3",
            stp::formatBVSchemaGroups(parsed));
}

TEST(UserDefinedFlags_Test, invalid_bv_schema_group_lists_are_atomic)
{
  const char* invalid[] = {"",        ",base",    "base,",    "base,,urem",
                           "unknown", "all,base", "base,none"};
  for (const char* text : invalid)
  {
    uint32_t parsed = 0x5a5u;
    std::string error;
    EXPECT_FALSE(stp::parseBVSchemaGroups(text, parsed, error)) << text;
    EXPECT_EQ(0x5a5u, parsed) << text;
    EXPECT_FALSE(error.empty()) << text;
  }
}

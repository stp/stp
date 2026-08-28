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

TEST(UserDefinedFlags_Test, bv_schema_groups_default_to_the_qualified_profile)
{
  stp::UserDefinedFlags uf;
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_QUALIFIED,
            uf.bv_term_abstraction_schema_groups);
  EXPECT_EQ("base,urem,mul-ref3",
            stp::formatBVSchemaGroups(uf.bv_term_abstraction_schema_groups));
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_DEFAULT_ROUNDS,
            uf.bv_term_abstraction_rounds);
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS,
            uf.bv_term_abstraction_rounds);
  // The broader catalogues are experiments a caller asks for by name, so no
  // group beyond the qualified three may reach a query that did not.
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(uf.bv_term_abstraction_schema_groups,
                                         stp::BVSchemaGroup::DIVREM_FULL));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(uf.bv_term_abstraction_schema_groups,
                                         stp::BVSchemaGroup::UDIV_OBSERVED));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(uf.bv_term_abstraction_schema_groups,
                                         stp::BVSchemaGroup::MUL8));
  EXPECT_FALSE(uf.bv_term_abstraction);
  EXPECT_TRUE(uf.bv_term_abstraction_schemas);
}

TEST(UserDefinedFlags_Test, named_bv_profiles_apply_mask_and_rounds_atomically)
{
  uint32_t mask = 0;
  unsigned rounds = 0;
  std::string error;
  ASSERT_TRUE(
      stp::parseBVTermAbstractionProfile("aggressive", mask, rounds, error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_AGGRESSIVE, mask);
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_AGGRESSIVE_ROUNDS, rounds);
  EXPECT_TRUE(
      stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::UDIV_OBSERVED));
  EXPECT_TRUE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::DIVREM_FULL));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::UDIV_TAIL));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::MUL_TAIL));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::ADD));
  EXPECT_FALSE(
      stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::QUOTIENT_THRESHOLDS));

  ASSERT_TRUE(
      stp::parseBVTermAbstractionProfile("broad", mask, rounds, error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD, mask);
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS, rounds);
  EXPECT_TRUE(
      stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::UDIV_OBSERVED));
  EXPECT_TRUE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::MUL8));
  EXPECT_TRUE(
      stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::DIVISOR_MAGNITUDE));
  EXPECT_FALSE(stp::bvSchemaGroupEnabled(mask, stp::BVSchemaGroup::DIVREM_FULL));

  ASSERT_TRUE(
      stp::parseBVTermAbstractionProfile("qualified", mask, rounds, error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_QUALIFIED, mask);
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS, rounds);

  mask = 0x5a5u;
  rounds = 7;
  EXPECT_FALSE(
      stp::parseBVTermAbstractionProfile("unknown", mask, rounds, error));
  EXPECT_EQ(0x5a5u, mask);
  EXPECT_EQ(7u, rounds);
  EXPECT_NE(std::string::npos,
            error.find("qualified, broad, or aggressive"));
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
      "base,udiv,urem,mul6,mul8,divisor-magnitude,quotient-one", parsed,
      error));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD, parsed);
  EXPECT_EQ("base,udiv15,udiv-observed,urem,quotient-one-quot,"
            "quotient-one-rem,divisor-magnitude,mul8,mul-ref3",
            stp::formatBVSchemaGroups(parsed));

  ASSERT_TRUE(stp::parseBVSchemaGroups("divrem-identity", parsed, error));
  EXPECT_EQ(stp::bvSchemaGroupBit(stp::BVSchemaGroup::DIVREM_FULL), parsed);
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

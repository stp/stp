/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
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
********************************************************************/

// The options this branch added that a C API client can now reach.
//
// Every one of them was reachable only by a query read from a file: a client
// driving STP through vc_* had no way to turn any of them on or off, and got
// whatever the defaults were. Each now has an ifaceflag_t that writes the same
// UserFlags field the CLI parser writes -- the two refinement profiles
// (--uf-narrow-results, --uf-inject-args), the eager congruence encoding
// (--uf-ackermann, --uf-ackermann-budget, --uf-lemmas-per-round,
// --uf-phase-hints), the declared-sort carrier (--uf-sort-width), the BV
// abstractions and what bounds them (--bv-eq-abstraction,
// --bv-abstraction-width, --bv-eq-refine-width, --bv-term-abstraction,
// --bv-term-abstraction-mult, --bv-term-abstraction-rounds), the distinct
// rewrite (--distinct-ordering) and the bit-blasting limit
// (--aig-node-budget). --uninterpreted-functions itself already had a route,
// through vc_setFlag(vc, 'u').
//
// The VC handle IS the stp::STP object, so reading the flags back off it is
// an honest probe for "did this reach the field the solver consults?" -- most
// of these change how a query is searched for rather than what it answers,
// and are otherwise invisible from outside.
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

// ifaceflag_t values are compiled into client binaries. Pin the complete
// published prefix explicitly: merely checking that the newest two are
// adjacent would not catch an insertion or reorder earlier in the enum.
static_assert(EXPRDELETE == 0, "published interface-flag ordinal changed");
static_assert(MS == 1, "published interface-flag ordinal changed");
static_assert(SMS == 2, "published interface-flag ordinal changed");
static_assert(CMS4 == 3, "published interface-flag ordinal changed");
static_assert(RISS == 4, "published interface-flag ordinal changed");
static_assert(MSP == 5, "published interface-flag ordinal changed");
static_assert(CADICAL == 6, "published interface-flag ordinal changed");
static_assert(INCREMENTAL_AUTO_ENGAGE_AT == 7,
              "published interface-flag ordinal changed");
static_assert(UF_NARROW_RESULTS == 8,
              "published interface-flag ordinal changed");
static_assert(UF_EQUALITY_INJECTIVITY == 9,
              "published interface-flag ordinal changed");
static_assert(UF_LEMMAS_PER_ROUND == 10,
              "published interface-flag ordinal changed");
static_assert(UF_ACKERMANN == 11, "published interface-flag ordinal changed");
static_assert(UF_ACKERMANN_BUDGET == 12,
              "published interface-flag ordinal changed");
static_assert(UF_PHASE_HINTS == 13, "published interface-flag ordinal changed");
static_assert(UF_SORT_WIDTH == 14, "published interface-flag ordinal changed");
static_assert(DISTINCT_ORDERING == 15,
              "published interface-flag ordinal changed");
static_assert(AIG_NODE_BUDGET == 16,
              "published interface-flag ordinal changed");
static_assert(BV_EQ_ABSTRACTION == 17,
              "published interface-flag ordinal changed");
static_assert(BV_ABSTRACTION_WIDTH == 18,
              "published interface-flag ordinal changed");
static_assert(BV_EQ_REFINE_WIDTH == 19,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION == 20,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_MULT == 21,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_ROUNDS == 22,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_SCHEMAS == 23,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_VALUE_DIVISOR == 24,
              "published interface-flag ordinal changed");
static_assert(BV_TERM_ABSTRACTION_INC_BITBLAST == 25,
              "published interface-flag ordinal changed");
static_assert(CNF_GENERATION_EFFORT == 26,
              "published interface-flag ordinal changed");
static_assert(INCREMENTAL_SCOPED_PREPROCESSING == 27,
              "published interface-flag ordinal changed");
static_assert(INCREMENTAL_PIECE_REWRITING == 28,
              "published interface-flag ordinal changed");
static_assert(CNF_AUTO_THRESHOLD == 29,
              "published interface-flag ordinal changed");
// The published prefix ends at CNF_AUTO_THRESHOLD. Everything this feature
// adds -- three interface flags and three profile ordinals -- is new in this
// series and deliberately NOT pinned here: nothing outside the tree has linked
// against it, so it stays free to be renumbered until it ships.
//
// The schema groups are not in that list because they are not ordinals at
// all. They are named, through vc_setSchemaGroups and vc_schemaGroupName, so
// that adding, renaming or merging a family costs nothing an installed header
// has committed to. What is worth checking is that the two spellings agree,
// and the round-trip test below does that.

namespace
{
const stp::UserDefinedFlags& flags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

stp::UserDefinedFlags& mutableFlags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

int errors = 0;
void countError(const char*)
{
  ++errors;
}
} // namespace

// The defaults a client inherits by not setting anything, which are the same
// ones the CLI captures into its --help text.
TEST(refinement_flags, DefaultsAreTheOnesTheCommandLineDocuments)
{
  VC vc = vc_createValidityChecker();
  EXPECT_TRUE(flags(vc).uf_narrow_results);
  EXPECT_FALSE(flags(vc).uf_inject_args);
  EXPECT_EQ(8u, flags(vc).uf_lemmas_per_round);
  EXPECT_EQ(stp::UserDefinedFlags::UFEagerMode::AUTO, flags(vc).uf_eager_mode);
  EXPECT_EQ(256u, flags(vc).uf_eager_budget);
  EXPECT_FALSE(flags(vc).uf_phase_hints);
  EXPECT_EQ(16u, flags(vc).uf_sort_width);
  EXPECT_TRUE(flags(vc).distinct_ordering);
  EXPECT_EQ(-1, flags(vc).aig_node_budget);
  EXPECT_FALSE(flags(vc).bv_eq_abstraction);
  EXPECT_EQ(64u, flags(vc).bv_abstraction_width);
  EXPECT_EQ(0u, flags(vc).bv_eq_refine_width);
  EXPECT_FALSE(flags(vc).bv_term_abstraction);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_divmod);
  EXPECT_EQ(stp::BV_TERM_ABSTRACTION_DEFAULT_ROUNDS,
            flags(vc).bv_term_abstraction_rounds);
  EXPECT_EQ(32u, flags(vc).bv_term_abstraction_rounds);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_schemas);
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_QUALIFIED,
            flags(vc).bv_term_abstraction_schema_groups);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_value_divisor);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_divmod_value_limit);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_inc_bitblast);
  vc_Destroy(vc);
}

// Each flag reaches its field, in both directions for the Boolean ones: a
// case that fell through to the default arm would abort rather than fail, so
// this pins the mapping and not merely that the enumerator is accepted.
TEST(refinement_flags, EachFlagReachesTheFieldTheCLIWrites)
{
  VC vc = vc_createValidityChecker();

  vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, 0);
  EXPECT_FALSE(flags(vc).uf_narrow_results);
  vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, 1);
  EXPECT_TRUE(flags(vc).uf_narrow_results);

  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 1);
  EXPECT_TRUE(flags(vc).uf_inject_args);
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 0);
  EXPECT_FALSE(flags(vc).uf_inject_args);

  // Any nonzero enables, as everywhere else in this call.
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 2);
  EXPECT_TRUE(flags(vc).uf_inject_args);
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 0);

  vc_setInterfaceFlags(vc, UF_PHASE_HINTS, 1);
  EXPECT_TRUE(flags(vc).uf_phase_hints);
  vc_setInterfaceFlags(vc, UF_PHASE_HINTS, 0);
  EXPECT_FALSE(flags(vc).uf_phase_hints);

  vc_setInterfaceFlags(vc, DISTINCT_ORDERING, 0);
  EXPECT_FALSE(flags(vc).distinct_ordering);
  vc_setInterfaceFlags(vc, DISTINCT_ORDERING, 1);
  EXPECT_TRUE(flags(vc).distinct_ordering);

  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  EXPECT_TRUE(flags(vc).bv_eq_abstraction);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 0);
  EXPECT_FALSE(flags(vc).bv_eq_abstraction);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_mult);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_divmod);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_divmod);

  // Naming DIV/MOD takes it out of the older switch's scope, and keeps it
  // out: a later MULT call moves multiplication and leaves division where
  // the caller put it.
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_divmod);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_mult);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_divmod);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_divmod);

  // Any nonzero enables, as everywhere else in this call.
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 2);
  EXPECT_TRUE(flags(vc).bv_eq_abstraction);

  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 1);
  EXPECT_EQ(1u, flags(vc).bv_abstraction_width);
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 0);
  EXPECT_EQ(0u, flags(vc).bv_abstraction_width);

  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 8);
  EXPECT_EQ(8u, flags(vc).bv_eq_refine_width);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 0);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_rounds);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 4);
  EXPECT_EQ(4u, flags(vc).bv_term_abstraction_rounds);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_SCHEMAS, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_schemas);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_SCHEMAS, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_schemas);

  EXPECT_EQ(1, vc_setSchemaGroups(vc, "all"));
  EXPECT_EQ(stp::BV_SCHEMA_GROUP_ALL,
            flags(vc).bv_term_abstraction_schema_groups);
  EXPECT_EQ(1, vc_setSchemaGroups(vc, "urem,mul-ref3"));
  EXPECT_EQ(stp::bvSchemaGroupBit(stp::BVSchemaGroup::UREM) |
                stp::bvSchemaGroupBit(stp::BVSchemaGroup::MUL_REF3),
            flags(vc).bv_term_abstraction_schema_groups);
  EXPECT_EQ(1, vc_setSchemaGroups(vc, "none"));
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_schema_groups);

  // Each profile on a checker of its own. This one has named a ceiling of
  // four above, and a profile no longer overwrites one the caller named --
  // see AProfileDoesNotOverwriteACeilingTheCallerNamed. What is under test
  // here is that both halves of the pair reach their fields, which needs a
  // caller that has not already settled one of them.
  {
    VC profiles = vc_createValidityChecker();
    vc_setInterfaceFlags(profiles, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_AGGRESSIVE,
              flags(profiles).bv_term_abstraction_schema_groups);
    EXPECT_EQ(stp::BV_TERM_ABSTRACTION_AGGRESSIVE_ROUNDS,
              flags(profiles).bv_term_abstraction_rounds);
    vc_setInterfaceFlags(profiles, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD,
              flags(profiles).bv_term_abstraction_schema_groups);
    EXPECT_EQ(stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS,
              flags(profiles).bv_term_abstraction_rounds);
    EXPECT_EQ(0u, flags(profiles).bv_term_abstraction_schema_groups &
                      stp::bvSchemaGroupBit(stp::BVSchemaGroup::DIVREM_FULL));
    vc_setInterfaceFlags(profiles, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_QUALIFIED);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_QUALIFIED,
              flags(profiles).bv_term_abstraction_schema_groups);
    EXPECT_EQ(stp::BV_TERM_ABSTRACTION_QUALIFIED_ROUNDS,
              flags(profiles).bv_term_abstraction_rounds);
    vc_Destroy(profiles);
  }
  EXPECT_EQ(4u, flags(vc).bv_term_abstraction_rounds);

  // Zero is a meaning of its own here too: do not scale, and leave the flat
  // ceiling above as the allowance.
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_VALUE_DIVISOR, 0);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_value_divisor);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_VALUE_DIVISOR, 16);
  EXPECT_EQ(16u, flags(vc).bv_term_abstraction_value_divisor);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT, 0);
  EXPECT_EQ(0u, flags(vc).bv_term_abstraction_divmod_value_limit);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT, 8);
  EXPECT_EQ(8u, flags(vc).bv_term_abstraction_divmod_value_limit);

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_INC_BITBLAST, 1);
  EXPECT_TRUE(flags(vc).bv_term_abstraction_inc_bitblast);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_INC_BITBLAST, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_inc_bitblast);

  // Zero is a meaning of its own for both of these, not an absence: install
  // every conflict the candidate exposes, and a budget of no gates at all.
  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, 0);
  EXPECT_EQ(0u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, 1);
  EXPECT_EQ(1u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 5000);
  EXPECT_EQ(5000, flags(vc).aig_node_budget);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 0);
  EXPECT_EQ(0, flags(vc).aig_node_budget);
  // -1 is the one negative value this budget takes, and it is the default:
  // no limit at all.
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, -1);
  EXPECT_EQ(-1, flags(vc).aig_node_budget);

  vc_setInterfaceFlags(vc, UF_ACKERMANN_BUDGET, 12);
  EXPECT_EQ(12u, flags(vc).uf_eager_budget);
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 5);
  EXPECT_EQ(5u, flags(vc).uf_sort_width);

  // The three modes, by ordinal, in the order --uf-ackermann names them.
  typedef stp::UserDefinedFlags::UFEagerMode Mode;
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 1);
  EXPECT_EQ(Mode::ON, flags(vc).uf_eager_mode);
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 2);
  EXPECT_EQ(Mode::OFF, flags(vc).uf_eager_mode);
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 0);
  EXPECT_EQ(Mode::AUTO, flags(vc).uf_eager_mode);

  vc_Destroy(vc);
}

// The command line resolves this pair by which options were given, not by
// where they appear; the C interface has to agree, or the same two settings
// mean two different things depending on which door a caller came through.
TEST(refinement_flags, TheDivModScopeResolvesTheSameWayInEitherOrder)
{
  for (int divModFirst = 0; divModFirst < 2; ++divModFirst)
  {
    VC vc = vc_createValidityChecker();
    if (divModFirst)
    {
      vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD, 0);
      vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
    }
    else
    {
      vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 1);
      vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD, 0);
    }
    EXPECT_TRUE(flags(vc).bv_term_abstraction_mult) << divModFirst;
    EXPECT_FALSE(flags(vc).bv_term_abstraction_divmod) << divModFirst;
    vc_Destroy(vc);
  }

  // And with nothing explicit about DIV/MOD, the older switch still covers
  // all three, which is what a command line written before the split meant.
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_MULT, 0);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_mult);
  EXPECT_FALSE(flags(vc).bv_term_abstraction_divmod);
  vc_Destroy(vc);
}

// A profile does not overwrite a ceiling the caller named, whichever order
// the two calls arrive in.
//
// A profile is an atomic mask/round pair, so applying one writes the round
// ceiling as well as the schema mask. That made the pair order-dependent:
// naming the ceiling and then choosing a profile silently discarded the
// ceiling, while doing the two the other way round kept it -- the same
// asymmetry bv_term_abstraction_divmod_explicit exists to remove between
// BV_TERM_ABSTRACTION_MULT and BV_TERM_ABSTRACTION_DIVMOD.
//
// The command line refuses --bv-term-abstraction-profile alongside
// --bv-term-abstraction-rounds outright, so it never had the question to
// answer. A C client configures over a sequence of calls and does, and both
// orders now give what the client asked for on each.
TEST(refinement_flags, AProfileDoesNotOverwriteACeilingTheCallerNamed)
{
  const unsigned broadRounds = stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS;
  ASSERT_NE(64u, broadRounds) << "pick a ceiling the profile does not set";

  // Ceiling first.
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 64);
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(64u, flags(vc).bv_term_abstraction_rounds);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD,
              flags(vc).bv_term_abstraction_schema_groups)
        << "the profile's mask half must still apply";
    vc_Destroy(vc);
  }

  // Profile first.
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 64);
    EXPECT_EQ(64u, flags(vc).bv_term_abstraction_rounds);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD,
              flags(vc).bv_term_abstraction_schema_groups);
    vc_Destroy(vc);
  }

  // A caller who never names one still gets the profile's own ceiling.
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(broadRounds, flags(vc).bv_term_abstraction_rounds);
    vc_Destroy(vc);
  }
}

// ... and it does not overwrite a group list the caller named either.
//
// A profile is one atomic mask/round pair, so its two halves should resolve by
// one rule. The ceiling half became first-wins when the ordering was fixed and
// the mask half was left last-writer-wins, which meant naming a ceiling before
// a profile kept the ceiling while naming a group list before a profile lost
// the list -- the same pair of calls meaning two different things depending on
// which half of it the caller had settled.
//
// First-wins for both. vc_setSchemaGroups is a caller spelling out families by
// name, which is as explicit as a ceiling is, and a profile that quietly
// discarded it would be the defect the ceiling rule exists to remove.
TEST(refinement_flags, AProfileDoesNotOverwriteAGroupListTheCallerNamed)
{
  const uint32_t named = stp::bvSchemaGroupBit(stp::BVSchemaGroup::UREM) |
                         stp::bvSchemaGroupBit(stp::BVSchemaGroup::MUL8);
  ASSERT_NE(stp::BV_SCHEMA_GROUP_BROAD, named)
      << "pick a list the profile does not select";

  // Group list first.
  {
    VC vc = vc_createValidityChecker();
    EXPECT_EQ(1, vc_setSchemaGroups(vc, "urem,mul8"));
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(named, flags(vc).bv_term_abstraction_schema_groups);
    EXPECT_EQ(stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS,
              flags(vc).bv_term_abstraction_rounds)
        << "the profile's ceiling half must still apply";
    vc_Destroy(vc);
  }

  // Profile first: a direct setter still wins, because the profile's mask was
  // not the caller naming one.
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(1, vc_setSchemaGroups(vc, "urem,mul8"));
    EXPECT_EQ(named, flags(vc).bv_term_abstraction_schema_groups);
    EXPECT_EQ(stp::BV_TERM_ABSTRACTION_BROAD_ROUNDS,
              flags(vc).bv_term_abstraction_rounds);
    vc_Destroy(vc);
  }

  // A caller who never names one still gets the profile's own mask.
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD,
              flags(vc).bv_term_abstraction_schema_groups);
    vc_Destroy(vc);
  }

  // A list the parser refuses is not a list the caller named, so a later
  // profile still applies its mask.
  {
    vc_registerErrorHandler(countError);
    errors = 0;
    VC vc = vc_createValidityChecker();
    EXPECT_EQ(0, vc_setSchemaGroups(vc, "urem,not-a-group"));
    EXPECT_EQ(1, errors);
    vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                         STP_BV_TERM_ABSTRACTION_PROFILE_BROAD);
    EXPECT_EQ(stp::BV_SCHEMA_GROUP_BROAD,
              flags(vc).bv_term_abstraction_schema_groups);
    vc_Destroy(vc);
    vc_registerErrorHandler(NULL);
  }
}

// A group list the parser refuses leaves the selection alone.
//
// The list is all-or-nothing on purpose: a caller that mistypes one name in a
// list of five should not end up running with a catalogue narrower than the
// one it asked for and no way to tell. `groups` is also the one string this
// interface parses, so a null pointer is refused rather than dereferenced.
TEST(refinement_flags, AnUnknownSchemaGroupNameIsRefused)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  EXPECT_EQ(1, vc_setSchemaGroups(vc, "base"));
  const uint32_t base = stp::bvSchemaGroupBit(stp::BVSchemaGroup::BASE);
  ASSERT_EQ(base, flags(vc).bv_term_abstraction_schema_groups);

  const char* refused[] = {"", "nonesuch", "urem,nonesuch", "all,urem",
                           "urem,,mul8", NULL};
  for (const char* value : refused)
  {
    EXPECT_EQ(0, vc_setSchemaGroups(vc, value))
        << "list [" << (value ? value : "(null)") << "]";
    EXPECT_EQ(base, flags(vc).bv_term_abstraction_schema_groups)
        << "list [" << (value ? value : "(null)") << "] changed the selection";
  }
  EXPECT_EQ((int)(sizeof(refused) / sizeof(refused[0])), errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(refinement_flags, InvalidBVProfileIsAtomic)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE,
                       STP_BV_TERM_ABSTRACTION_PROFILE_AGGRESSIVE);
  const uint32_t mask = flags(vc).bv_term_abstraction_schema_groups;
  const unsigned rounds = flags(vc).bv_term_abstraction_rounds;

  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, -1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PROFILE, 4);
  EXPECT_EQ(mask, flags(vc).bv_term_abstraction_schema_groups);
  EXPECT_EQ(rounds, flags(vc).bv_term_abstraction_rounds);
  EXPECT_EQ(2, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// Each group index must read its own counter and name -- not a neighbour's.
// Distinct values per slot are what makes an off-by-one visible; a uniform
// value would pass whatever the indexing did.
TEST(refinement_flags, EachSchemaGroupIndexReadsItsOwnCounterAndName)
{
  ASSERT_EQ(stp::BV_SCHEMA_GROUP_COUNT,
            static_cast<unsigned>(STP_BV_SCHEMA_GROUP_COUNT));

  VC vc = vc_createValidityChecker();
  for (unsigned i = 0; i < STP_BV_SCHEMA_GROUP_COUNT; ++i)
    mutableFlags(vc).coverage.bv_schema_group_lemmas[i] = 100 + i;

  for (unsigned i = 0; i < STP_BV_SCHEMA_GROUP_COUNT; ++i)
  {
    EXPECT_EQ(100u + i, vc_getSchemaGroupCounter(vc, i));
    EXPECT_STREQ(stp::bvSchemaGroupName(static_cast<stp::BVSchemaGroup>(i)),
                 vc_schemaGroupName(i));
  }
  vc_Destroy(vc);
}

// The name a breakdown reports has to be a name the selector accepts, and it
// has to select that group and no other.
//
// This is the whole contract now that the taxonomy is not in the header. The
// two calls are the only spellings of a group a C client ever sees, and if
// they drift apart a client that reads a breakdown and feeds one line of it
// back in gets a different family than the one it named. Checking it by
// round-trip rather than against a written-out table is what keeps a family
// added tomorrow covered without anyone remembering to add it here.
TEST(refinement_flags, EverySchemaGroupNameRoundTripsThroughTheSelector)
{
  VC vc = vc_createValidityChecker();
  for (unsigned i = 0; i < STP_BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const char* name = vc_schemaGroupName(i);
    ASSERT_TRUE(name != NULL) << "index " << i;
    EXPECT_EQ(1, vc_setSchemaGroups(vc, name)) << name;
    EXPECT_EQ(stp::bvSchemaGroupBit(static_cast<stp::BVSchemaGroup>(i)),
              flags(vc).bv_term_abstraction_schema_groups)
        << name << " does not select itself";
  }
  vc_Destroy(vc);
}

// An index past the end is a diagnostic and a zero, not an out-of-bounds read.
TEST(refinement_flags, AnOutOfRangeSchemaGroupIndexIsRefused)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  EXPECT_EQ(0u, vc_getSchemaGroupCounter(vc, STP_BV_SCHEMA_GROUP_COUNT));
  EXPECT_TRUE(vc_schemaGroupName(STP_BV_SCHEMA_GROUP_COUNT) == NULL);
  EXPECT_EQ(2, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(refinement_flags, ExactCostCountersReachTheCInterface)
{
  VC vc = vc_createValidityChecker();
  mutableFlags(vc).coverage.bv_exact_clauses = 1234;
  mutableFlags(vc).coverage.bv_exact_variables = 567;
  mutableFlags(vc).coverage.bv_exact_microseconds = 89;
  EXPECT_EQ(1234u, vc_getCounter(vc, STP_COUNTER_BV_EXACT_CLAUSES));
  EXPECT_EQ(567u, vc_getCounter(vc, STP_COUNTER_BV_EXACT_VARIABLES));
  EXPECT_EQ(89u, vc_getCounter(vc, STP_COUNTER_BV_EXACT_MICROSECONDS));
  vc_Destroy(vc);
}

// A negative value would wrap in every unsigned field below, silently
// disabling an abstraction or removing the limit the caller asked for. It is
// refused with a diagnostic and the field it would have wrecked is unchanged.
TEST(refinement_flags, ANegativeUnsignedValueIsRefusedAndLeavesTheFieldAlone)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 32);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 4);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, 12);

  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, -1);
  EXPECT_EQ(32u, flags(vc).bv_abstraction_width);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, -64);
  EXPECT_EQ(4u, flags(vc).bv_eq_refine_width);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_ROUNDS, -2);
  EXPECT_EQ(12u, flags(vc).bv_term_abstraction_rounds);
  // Set to something that is not the default first, so that "unchanged" and
  // "reset to the default" are different answers here.
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_VALUE_DIVISOR, 8);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_VALUE_DIVISOR, -3);
  EXPECT_EQ(8u, flags(vc).bv_term_abstraction_value_divisor);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT, 4);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_DIVMOD_VALUE_LIMIT, -3);
  EXPECT_EQ(4u, flags(vc).bv_term_abstraction_divmod_value_limit);

  vc_setInterfaceFlags(vc, UF_LEMMAS_PER_ROUND, -1);
  EXPECT_EQ(8u, flags(vc).uf_lemmas_per_round);
  vc_setInterfaceFlags(vc, UF_ACKERMANN_BUDGET, -1);
  EXPECT_EQ(256u, flags(vc).uf_eager_budget);
  EXPECT_EQ(7, errors);

  // The AIG budget is signed underneath and -1 is a value of its own there,
  // so only a value below it names nothing and only that is refused.
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 7);
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, -2);
  EXPECT_EQ(7, flags(vc).aig_node_budget);
  EXPECT_EQ(8, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// The declared-sort width is bounded at both ends, not merely at zero: a
// zero-width element is read as a Boolean by the legacy width checks, and a
// width past the ceiling overflows the word arithmetic underneath. Both are
// refused and leave the width as it was, so a client cannot reach either.
TEST(refinement_flags, TheSortWidthIsRefusedOutsideTheRangeTheCLITakes)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  const int outside[] = {-1, 0, 1025, 100000};
  for (const int bad : outside)
  {
    vc_setInterfaceFlags(vc, UF_SORT_WIDTH, bad);
    EXPECT_EQ(16u, flags(vc).uf_sort_width) << "width " << bad;
  }
  EXPECT_EQ(4, errors);

  // and the two ends that are inside it
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 1);
  EXPECT_EQ(1u, flags(vc).uf_sort_width);
  vc_setInterfaceFlags(vc, UF_SORT_WIDTH, 1024);
  EXPECT_EQ(1024u, flags(vc).uf_sort_width);
  EXPECT_EQ(4, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// UF_ACKERMANN names one of three modes. A value outside them names none, so
// it is refused rather than stored: the field is an enumeration, and the
// lowering tests it arm by arm.
TEST(refinement_flags, AnUnknownAckermannModeIsRefused)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC vc = vc_createValidityChecker();
  typedef stp::UserDefinedFlags::UFEagerMode Mode;
  vc_setInterfaceFlags(vc, UF_ACKERMANN, 1);
  ASSERT_EQ(Mode::ON, flags(vc).uf_eager_mode);
  const int outside[] = {-1, 3, 99};
  for (const int bad : outside)
  {
    vc_setInterfaceFlags(vc, UF_ACKERMANN, bad);
    EXPECT_EQ(Mode::ON, flags(vc).uf_eager_mode) << "mode " << bad;
  }
  EXPECT_EQ(3, errors);

  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// The AIG budget is the one option here that can change what a query answers,
// so what it answers is worth pinning: exceeding it ends the query without
// one, and at -1 -- no limit -- the same query is decided, which is what says
// the no-answer came from the budget and not from the query being hard. Which
// cause it was, and how the causes that share the verdict are told apart,
// belong to reason-unknown.cpp.
TEST(refinement_flags, TheAigBudgetEndsAQueryWithoutAnAnswer)
{
  for (int budget = -1; budget <= 50; budget += 51)
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, budget);
    Type bv = vc_bvType(vc, 32);
    Expr x = vc_varExpr(vc, "x", bv);
    Expr y = vc_varExpr(vc, "y", bv);
    vc_assertFormula(
        vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, x, y),
                      vc_bvConstExprFromInt(vc, 32, 0xffff)));
    vc_assertFormula(
        vc, vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(vc, 32, 1)));
    const int answer = vc_query(vc, vc_falseExpr(vc));
    if (budget == -1)
      EXPECT_EQ(0, answer) << "no limit, so the query is decided";
    else
      EXPECT_EQ(3, answer) << "budget " << budget;
    vc_Destroy(vc);
  }
}

// Narrowing is invisible from out here: it re-sorts the introduced result
// symbol the solver reasons about, and the model still reads back at the
// sort the declaration was made at.
TEST(refinement_flags, NarrowingChangesNeitherTheAnswerNorTheSortReadBack)
{
  for (int narrow = 0; narrow < 2; narrow++)
  {
    VC vc = vc_createValidityChecker();
    vc_setFlag(vc, 'u');
    vc_setInterfaceFlags(vc, UF_NARROW_RESULTS, narrow);
    ASSERT_EQ(narrow != 0, flags(vc).uf_narrow_results);

    Type bv8 = vc_bvType(vc, 8);
    Type domain[] = {bv8};
    const UFDeclHandle f =
        vc_declareUninterpretedFunction(vc, "f", domain, 1, bv8);
    ASSERT_NE(0u, f);

    Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
    Expr b = vc_varExpr(vc, "b", vc_bvType(vc, 8));
    Expr c = vc_varExpr(vc, "c", vc_bvType(vc, 8));
    const Expr aArg[] = {a};
    const Expr bArg[] = {b};
    const Expr cArg[] = {c};
    Expr fa = vc_applyUninterpretedFunction(vc, f, aArg, 1);
    Expr fb = vc_applyUninterpretedFunction(vc, f, bArg, 1);
    Expr fc = vc_applyUninterpretedFunction(vc, f, cArg, 1);
    ASSERT_NE(nullptr, fa);
    ASSERT_NE(nullptr, fb);
    ASSERT_NE(nullptr, fc);

    // Three results that must differ: two bits are enough to tell them apart,
    // where the declaration asked for eight.
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fa, fb)));
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fb, fc)));
    vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, fa, fc)));

    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

    // Whatever width the solver used, the declared one is what comes back.
    Expr value = vc_getUninterpretedFunctionValue(vc, fa);
    ASSERT_NE(nullptr, value);
    EXPECT_EQ(8, vc_getBVLength(vc, value));
    Expr other = vc_getUninterpretedFunctionValue(vc, fb);
    ASSERT_NE(nullptr, other);
    EXPECT_EQ(8, vc_getBVLength(vc, other));
    EXPECT_NE(getBVUnsigned(value), getBVUnsigned(other));

    vc_DeleteExpr(other);
    vc_DeleteExpr(value);
    vc_Destroy(vc);
  }
}

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// counter-enum-abi.cpp -- the published engine counters as 3.x
// statistics.
//
// 2.x published its counters as stp_counter_t ordinals, which callers compiled
// into their binaries and could then load a newer libstp against, so the
// published prefix had to stay fixed. 3.x keys every statistic by a stable
// dotted name (statistics.toml), read from Solver::statistics(): what must
// stay fixed is the name, its type and tier, and what it counts. The three
// ordinals 2.x pinned -- the UF applications lowered (15), the UF constraints
// installed (16) and the BV schema lemmas (17) -- are uf.applications_lowered,
// uf.constraints_installed and bv.schema_lemmas.

#include "api_common.hpp"

#include <cstdint>
#include <variant>

using namespace stp;

// The one enumeration the statistics surface publishes is the tier; its
// values are pinned and append-only like every 3.x enumeration.
static_assert(static_cast<int>(Tier::STABLE) == 0, "the published tier values changed");
static_assert(static_cast<int>(Tier::EXPERT) == 1, "the published tier values changed");
static_assert(static_cast<int>(Tier::DIAGNOSTIC) == 3, "the published tier values changed");

namespace
{

// The names the three published ordinals became.
const char* const PUBLISHED[] = {"uf.applications_lowered", "uf.constraints_installed",
                                 "bv.schema_lemmas"};

} // namespace

TEST(c_counter_enum_abi, PublishedCounterOrdinalsRemainStable)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true); // 'd', as vc_createValidityChecker set it
  Solver s(tm, o);

  // A fresh solver already reports every published counter: a uint64 of the
  // expert tier, at zero.
  const Statistics fresh = s.statistics();
  for (const char* name : PUBLISHED)
  {
    SCOPED_TRACE(name);
    ASSERT_TRUE(std::holds_alternative<std::uint64_t>(fresh.get(name)));
    EXPECT_EQ(fresh.uint64(name), 0u);
    EXPECT_EQ(fresh.tier(name), Tier::EXPERT);
  }
  // A name that was never published is refused, not read as zero.
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, fresh.get("uf.no_such_counter"));

  // What the UF counters count: three distinct applications of f that the
  // check has to lower (the orderings keep preprocessing from deciding the
  // problem) are three applications lowered and three congruence constraints,
  // one per pair.
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8), z = tm.declare("z", bv8);
  s.add(f(x) == 1);
  s.add(f(y) == 2);
  s.add(f(z) == 3);
  s.add(bvult(x, y));
  s.add(bvult(y, z));
  s.add(bvmul(x, z) == bvadd(y, 7));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Statistics after = s.statistics();
  EXPECT_EQ(after.uint64("uf.applications_lowered"), 3u);
  EXPECT_EQ(after.uint64("uf.constraints_installed"), 3u);
  // no bit-vector abstraction ran, so it added no schema lemma
  EXPECT_EQ(after.uint64("bv.schema_lemmas"), 0u);
  // the snapshot taken before the check is a value: it still reads zero
  EXPECT_EQ(fresh.uint64("uf.applications_lowered"), 0u);
}

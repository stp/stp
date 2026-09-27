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

// api3-persist-delete.cpp -- releasing a sort handle before its manager.
//
// With EXPRDELETE on, the 2.x default, the checker owned every Type, every
// vc_bvConstExprFromInt and every vc_fp* handle and released them from
// vc_Destroy. Deleting one early was allowed, so the checker had to forget it,
// and the destroy walk never read or freed it a second time (#1140). 3.x has
// one ownership rule: a sort or a term is a value that pins its manager, and
// destruction order is free. These cases release a sort early and check that
// the manager, a solver over it and the handles made afterwards are
// unaffected.

#include "api3_common.hpp"

#include <cstdint>
#include <map>
#include <optional>

using namespace stp;

namespace
{

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

// The sort goes before the solver and the manager, and they go in either
// order afterwards.
TEST(PersistDelete, DeletedTypeIsNotRevisitedByDestroy)
{
  std::optional<TermManager> tm(std::in_place);
  std::optional<Solver> s(std::in_place, *tm, checkerOptions());
  std::uint64_t id = 0;
  {
    const Sort bv8 = tm->mk_bv_sort(8);
    id = bv8.id();
  } // released first

  // Sorts are interned: the same sort made again is the one released.
  EXPECT_EQ(tm->mk_bv_sort(8).id(), id);
  s.reset();
  tm.reset();
}

// Enabling UF afterwards adopted the checker-owned handles into its registry
// by walking the same list, so a deleted one had to be gone from it already.
// In 3.x UF is the solver's uninterpreted-functions option ('u'), which never
// gates construction; a function over the released sort is declared and
// decided as usual.
TEST(PersistDelete, DeletedTypeIsNotAdoptedWhenUFIsEnabledLater)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  {
    const Sort bv8 = tm.mk_bv_sort(8);
    (void)bv8;
  }
  s.options().set("uninterpreted-functions", "on");
  EXPECT_EQ(s.options().get_str("uninterpreted-functions"), "on");

  const Sort bv8 = tm.mk_bv_sort(8);
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term x = tm.declare("x", bv8);
  s.add(f(x) == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(f(x)), 1u);
}

// The freed 2.x wrapper's address could be handed to a later checker-owned
// wrapper, and a stale entry must not make vc_Destroy free the new one twice.
// 3.x hands out no addresses: terms are hash-consed values whose ids are never
// reused, so the 256 distinct constants among a thousand requests are 256
// terms, an id never names two of them, and every id reads back its own term.
TEST(PersistDelete, DeletedSlotDoesNotAliasALaterWrapper)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  std::uint64_t released = 0;
  {
    const Sort bv8 = tm.mk_bv_sort(8);
    released = bv8.id();
  }

  std::map<std::uint64_t, std::uint64_t> value_of_id;
  for (unsigned i = 0; i < 1000; ++i)
  {
    const Term c = tm.mk_bv(8, i & 0xffu);
    const auto entry = value_of_id.emplace(c.id(), c.to_uint64()).first;
    EXPECT_EQ(entry->second, i & 0xffu) << "id " << c.id() << " names two values";
  }
  EXPECT_EQ(value_of_id.size(), 256u);
  for (const auto& [id, value] : value_of_id)
    EXPECT_EQ(tm.term_from_id(id).to_uint64(), value);
  EXPECT_EQ(tm.mk_bv_sort(8).id(), released);
}

// An early release leaves the checker usable, and the other handles keep their
// own lifetime either way.
TEST(PersistDelete, EarlyDeleteLeavesTheCheckerUsable)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  std::optional<Sort> bv8(tm.mk_bv_sort(8));
  const Term x = tm.declare("x", *bv8);
  bv8.reset();

  const Term one = tm.mk_bv(8, 1);
  const Term eq = x == one;
  EXPECT_TRUE(s.entails(eq).is_invalid()); // x = 1 is not valid
  // the term's sort did not go with the released handle
  EXPECT_EQ(x.sort().bv_size(), 8u);
}

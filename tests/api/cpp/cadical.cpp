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

// cadical.cpp -- driving CaDiCaL through the 3.x API: both ways of
// selecting it (the sat-backend entry by its typed setter, and in the
// command line's syntax), and then actually solving with it.
//
// A solver's backend is chosen when it is built (sat-backend is settable at
// construction only), so the selection is made in the Options the solver is
// constructed from, and the backend a solver runs is its statistics'
// sat.backend.

#include "api_common.hpp"

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

using namespace stp;

namespace
{

#ifdef USE_CADICAL
const bool cadical_available = true;
#else
const bool cadical_available = false;
#endif

#ifdef USE_MINISAT
const bool minisat_available = true;
#else
const bool minisat_available = false;
#endif

std::string backend_in_use(const Solver& s)
{
  return s.statistics().str("sat.backend");
}

// CaDiCaL, with the engine's model self-check (check-sanity) on, as every 2.x
// checker had it: a sat answer whose model does not satisfy the assertions is
// an INTERNAL error rather than a silent pass.
Options cadical_options()
{
  Options o;
  o.set_str("sat-backend", "cadical");
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

// Whether STP can offer CaDiCaL is a build-time property, and the API has to
// report it honestly either way: the backend probes, the capability map and
// the options that need the backend all agree with the build.
TEST(cadical, support_is_reported)
{
  EXPECT_EQ(has_sat_backend("cadical"), cadical_available);
  const std::vector<std::string> backends = sat_backends();
  EXPECT_EQ(std::find(backends.begin(), backends.end(), "cadical") != backends.end(),
            cadical_available);
  EXPECT_EQ(capabilities().count("sat.backend.cadical.version") == 1, cadical_available);
  EXPECT_EQ(Options().info("cadical-elim").supported, cadical_available);
}

// Selecting CaDiCaL succeeds exactly when the build has it. 2.x selected on a
// live checker, and a build with CaDiCaL could default to it, so the
// selection was only visible as a change after moving off it first. 3.x
// picks the backend when the solver is built: a solver built for CaDiCaL runs
// it, a build without it refuses the solver, and a live solver refuses to
// switch backends at all.
TEST(cadical, selected_by_use_cadical)
{
  TermManager tm;
  if (cadical_available)
  {
    Solver s(tm, cadical_options());
    EXPECT_EQ("cadical", s.options().get_str("sat-backend"));
    EXPECT_EQ("cadical", backend_in_use(s));
  }
  else
  {
    API_EXPECT_ERROR(ErrorCode::OPTION_UNAVAILABLE, Solver s(tm, cadical_options()));
  }

  Solver live(tm);
  const std::string before = backend_in_use(live);
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.options().set_str("sat-backend", "cadical"));
  EXPECT_EQ(before, backend_in_use(live));
}

// The same choice in the command line's syntax, which is how a caller that
// already builds its configuration as arguments reaches CaDiCaL.
TEST(cadical, selected_by_interface_flag)
{
  TermManager tm;
  Options o;
  // Move the selection somewhere else first, so the argument is observable
  // as a change and not just the default reasserting itself.
  o.set_str("sat-backend", "minisat");
  o.set_args({"--sat-backend=cadical"});
  EXPECT_EQ("cadical", o.get_str("sat-backend"));

  if (!cadical_available)
  {
    // 3.x refuses a backend the build lacks when the solver is built, rather
    // than selecting it and answering "not in use" afterwards.
    API_EXPECT_ERROR(ErrorCode::OPTION_UNAVAILABLE, Solver s(tm, o));
    return;
  }
  // CaDiCaL, and so none of MiniSat, simplifying MiniSat or CryptoMiniSat.
  Solver s(tm, o);
  EXPECT_EQ("cadical", backend_in_use(s));
}

// 2.x pinned the numbers of its backend selectors (ifaceflag_t: MS 1, SMS 2,
// CMS4 3, the retired RISS 4, MSP 5, CADICAL 6), because a caller compiled
// against an older header passes the same integers. 3.x selects backends by
// name: what must not change is the names the entry takes, and the ordinal of
// the stable entry that takes them.
TEST(cadical, interface_flag_values_are_unchanged)
{
  EXPECT_EQ(1, static_cast<int>(Option::SAT_BACKEND));
  EXPECT_EQ("sat-backend", Options::name_of(Option::SAT_BACKEND));
  const OptionInfo info = Options().info("sat-backend");
  EXPECT_EQ((std::vector<std::string>{"auto", "cryptominisat", "cadical", "minisat",
                                      "simplifying-minisat"}),
            info.values);
  EXPECT_EQ(Settable::CONSTRUCTION, info.settable);
}

// The other selectors still select their own backend: MiniSat (2.x's MS, and
// MSP, its second spelling) and simplifying MiniSat (SMS). 2.x moved the
// selection off CaDiCaL even in a build without MiniSat and then answered
// "not in use"; 3.x refuses a backend the build lacks when the solver is
// built.
TEST(cadical, other_interface_flags_still_select_their_own_solver)
{
  TermManager tm;
  for (const char* name : {"minisat", "simplifying-minisat"})
  {
    SCOPED_TRACE(name);
    EXPECT_EQ(has_sat_backend(name), minisat_available);
    Options o;
    o.set_str("sat-backend", name);
    if (minisat_available)
    {
      Solver s(tm, o);
      EXPECT_EQ(name, backend_in_use(s)); // and so not CaDiCaL
    }
    else
    {
      API_EXPECT_ERROR(ErrorCode::OPTION_UNAVAILABLE, Solver s(tm, o));
    }
  }
}

// A valid entailment and an invalid one, answered by CaDiCaL.
TEST(cadical, solves_valid_and_invalid_queries)
{
  if (!cadical_available)
    GTEST_SKIP() << "built without CaDiCaL";

  TermManager tm;
  Solver s(tm, cadical_options());

  const std::uint32_t width = 16;
  const Term x = tm.declare("x", tm.mk_bv_sort(width));
  const Term ten = tm.mk_bv(width, 10);

  // (x > 10) => (x > 5) holds for every x.
  EXPECT_TRUE(s.entails(implies(bvugt(x, ten), bvugt(x, tm.mk_bv(width, 5)))).is_valid());

  // The converse does not.
  EXPECT_TRUE(s.entails(implies(bvugt(x, tm.mk_bv(width, 5)), bvugt(x, ten))).is_invalid());
}

// A model produced while CaDiCaL is the backend, read back through the API
// and checked against the constraints it is supposed to satisfy.
TEST(cadical, produces_a_usable_counterexample)
{
  if (!cadical_available)
    GTEST_SKIP() << "built without CaDiCaL";

  TermManager tm;
  Options o = cadical_options();
  o.set_bool("produce-models", true); // construct models (the default)
  Solver s(tm, o);

  const std::uint32_t width = 32;
  const Term a = tm.declare("a", tm.mk_bv_sort(width));
  const Term b = tm.declare("b", tm.mk_bv_sort(width));
  const Term thousand = tm.mk_bv(width, 1000);
  const Term hundred = tm.mk_bv(width, 100);

  // a + b == 1000 with both operands in (100, 1000): satisfiable. Bounding
  // both below 1000 keeps the addition from wrapping, so the values read back
  // have to add up exactly.
  s.add(bvadd(a, b) == thousand);
  s.add(bvugt(a, hundred));
  s.add(bvugt(b, hundred));
  s.add(bvult(a, thousand));
  s.add(bvult(b, thousand));

  ASSERT_TRUE(s.check_sat().is_sat());

  const Model m = s.model();
  const std::uint64_t a_value = m.uint64_value(a);
  const std::uint64_t b_value = m.uint64_value(b);

  EXPECT_EQ(a_value + b_value, 1000u);
  EXPECT_GT(a_value, 100u);
  EXPECT_GT(b_value, 100u);
}

// Assertions that cannot be satisfied, decided by CaDiCaL.
TEST(cadical, reports_unsatisfiable_assertions)
{
  if (!cadical_available)
    GTEST_SKIP() << "built without CaDiCaL";

  TermManager tm;
  Solver s(tm, cadical_options());

  const std::uint32_t width = 8;
  const Term x = tm.declare("x", tm.mk_bv_sort(width));
  const Term five = tm.mk_bv(width, 5);

  s.add(bvugt(x, five));
  s.add(bvult(x, five));

  EXPECT_TRUE(s.check_sat().is_unsat());
}

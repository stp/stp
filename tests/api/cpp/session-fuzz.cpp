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

// session-fuzz.cpp -- random sessions of the API under its default options,
// each check held to what the session itself can confirm, so that no other
// solver is needed: a model satisfies every assertion and assumption, a core
// of assumptions is unsatisfiable again on its own, and a fresh solver over
// the same assertions and assumptions gives the same verdict.
//
// The sessions mix bit-vectors, arrays over them with constant arrays among
// them, an uninterpreted function, half-precision floats and Reals, with
// scopes pushed and popped and checks under assumptions: the default options
// then move a session between the batch and the incremental driver as it
// goes. A fixed set of seeds keeps the test bounded and its failures
// repeatable; SCOPED_TRACE names the seed and the operation.

#include "api_common.hpp"

#include <functional>
#include <random>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Session
{
  std::mt19937 rng;
  TermManager tm;
  Solver s{tm};
  Sort b8 = tm.mk_bv_sort(8), b4 = tm.mk_bv_sort(4), f16 = tm.mk_fp16_sort(),
       R = tm.mk_real_sort();
  Sort arr = tm.mk_array_sort(b4, b8);
  std::vector<Term> bv, ix, ar, fp, re, bl;
  Term f, K;

  explicit Session(unsigned seed) : rng(seed)
  {
    bv = {tm.declare("x", b8), tm.declare("y", b8)};
    ix = {tm.declare("i", b4), tm.declare("j", b4)};
    ar = {tm.declare("a", arr), tm.declare("b", arr)};
    fp = {tm.declare("u", f16), tm.declare("v", f16)};
    re = {tm.declare("r", R), tm.declare("t", R)};
    bl = {tm.declare("p", tm.mk_bool_sort()), tm.declare("q", tm.mk_bool_sort())};
    f = tm.declare("f", tm.mk_fun_sort({b8}, b8));
    K = tm.mk_const_array(arr, tm.mk_bv(8, pick(256)));
  }

  unsigned pick(unsigned n) { return rng() % n; }

  Term bitvector(int depth)
  {
    if (depth == 0 || pick(3) == 0)
      switch (pick(4))
      {
        case 0: return tm.mk_bv(8, pick(256));
        case 1: return select(ar[pick(2)], ix[pick(2)]);
        case 2: return select(K, ix[pick(2)]);
        default: return bv[pick(2)];
      }
    const Term a = bitvector(depth - 1), b = bitvector(depth - 1);
    switch (pick(7))
    {
      case 0: return bvadd(a, b);
      case 1: return bvmul(a, b);
      case 2: return bvxor(a, b);
      case 3: return f(a);
      case 4: return ite(bvult(a, b), a, b);
      case 5: return select(store(ar[pick(2)], ix[pick(2)], a), ix[pick(2)]);
      default: return bvlshr(a, tm.mk_bv(8, pick(8)));
    }
  }

  Term formula()
  {
    const RoundingMode rm = static_cast<RoundingMode>(pick(5));
    switch (pick(12))
    {
      case 0: return bitvector(2) == bitvector(2);
      case 1: return bvult(bitvector(2), bitvector(1));
      case 2:
        return store(ar[0], ix[pick(2)], bitvector(1)) == store(ar[1], ix[pick(2)], bitvector(1));
      case 3: return ar[pick(2)] == (pick(2) ? K : store(K, ix[pick(2)], bitvector(1)));
      case 4: return fp_lt(fp_add(rm, fp[0], fp[1]), fp[pick(2)]);
      case 5: return not_(fp_is_nan(fp_mul(rm, fp[0], fp[1])));
      case 6:
        return fp_eq(fp[0], tm.mk_fp(f16, RoundingMode::RNE, static_cast<double>(static_cast<int>(pick(9)) - 4)));
      case 7: return real_lt(real_add(re[0], tm.mk_real(static_cast<std::int64_t>(pick(5)))), re[1]);
      case 8:
        return real_le(real_mul(tm.mk_real(static_cast<std::int64_t>(pick(3)) + 1), re[1]),
                       tm.mk_real(static_cast<std::int64_t>(pick(20)) - 10));
      case 9: return implies(bl[pick(2)], bitvector(1) == bitvector(1));
      case 10: return or_(bl[0], not_(bl[1]));
      default: return real_lt(fp_to_real(fp[pick(2)]), re[pick(2)]);
    }
  }

  // One check and everything it can be held to.
  void check(const std::vector<Term>& assumptions)
  {
    const Result r = assumptions.empty() ? s.check_sat() : s.check_sat(assumptions);
    ASSERT_FALSE(r.is_unknown()) << r;
    if (r.is_sat())
    {
      const Model m = s.model();
      for (const Term& a : s.assertions())
        EXPECT_TRUE(m.bool_value(a)) << "the model falsifies the assertion " << a;
      for (const Term& a : assumptions)
        EXPECT_TRUE(m.bool_value(a)) << "the model falsifies the assumption " << a;
    }
    else if (!assumptions.empty())
    {
      const std::vector<Term> core = s.unsat_assumptions();
      EXPECT_TRUE(s.check_sat(core).is_unsat())
          << "a core of " << core.size() << " of " << assumptions.size()
          << " assumptions is satisfiable";
    }

    // The same question, asked of a solver that has seen nothing else.
    const std::vector<Term> assertions = s.assertions();
    Solver fresh(tm);
    for (const Term& a : assertions)
      fresh.add(a);
    for (const Term& a : assumptions)
      fresh.add(a);
    const Result again = fresh.check_sat();
    ASSERT_FALSE(again.is_unknown()) << again;
    EXPECT_EQ(r.is_sat(), again.is_sat()) << "the session answered " << r
                                           << ", a fresh solver " << again;
  }
};

TEST(SessionFuzz, default_option_sessions_agree_with_themselves)
{
  for (unsigned seed = 1; seed <= 40; ++seed)
  {
    Session x(seed);
    for (int op = 0; op < 20 && !::testing::Test::HasFatalFailure(); ++op)
    {
      SCOPED_TRACE("seed " + std::to_string(seed) + " operation " + std::to_string(op));
      const unsigned r = x.pick(10);
      if (r < 2)
        x.s.push();
      else if (r < 3 && x.s.level() > 0)
        x.s.pop();
      else if (r < 6)
        x.s.add(x.formula());
      else
      {
        std::vector<Term> assumptions;
        if (x.pick(2))
          for (int k = 0; k < 2; ++k)
            assumptions.push_back(x.pick(2) ? x.bl[x.pick(2)] : x.formula());
        x.check(assumptions);
      }
    }
    ASSERT_FALSE(::testing::Test::HasFatalFailure()) << "seed " << seed;
  }
}

} // namespace

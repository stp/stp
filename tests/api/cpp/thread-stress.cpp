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

// thread-stress.cpp -- managers on threads of their own, each deciding
// formulas under a different set of options at the same time.
//
// Each manager is used by one thread, as the API allows, so anything the
// threads share is the library's: the static tables and caches behind the
// options -- a CNF encoder's cache of cell encodings, ABC's rewriting
// library, the SAT backends' option tables. Two of those raced once, and only
// under the option that reaches them. Every thread's verdicts are compared
// with a sequential rerun of the same formulas, and every sat model has to
// satisfy its assertions; under ThreadSanitizer (the tsan job) the run is
// also checked for data races. The formula for (thread, index) is fixed by
// its seed, and the option sets are taken in turn so that every one of them
// runs concurrently with the others.

#include "api_common.hpp"

#include <atomic>
#include <cstdint>
#include <random>
#include <string>
#include <thread>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

using OptionSet = std::vector<std::pair<const char*, const char*>>;

const std::vector<OptionSet> kOptionSets = {
    {},
    {{"cnf-generation-effort", "very-low"}},
    {{"cnf-generation-effort", "high"}},
    {{"cnf-generation-effort", "very-high"}},
    {{"cnf-generation-effort", "new-low"}},
    {{"cnf-generation-effort", "new-medium"}},
    {{"cnf-generation-effort", "new-high"}},
    {{"cnf-generation-effort", "gia-low"}},
    {{"cnf-generation-effort", "gia-high"}},
    {{"cnf-generation-effort", "gia-very-high"}},
    {{"bv-term-abstraction", "true"}},
    {{"bv-eq-abstraction", "true"}},
    {{"fp-abstraction", "true"}},
    {{"incremental", "on"}},
    {{"disable-simplifications", "true"}},
    {{"array-equality", "on"}},
    {{"uf-ackermann", "on"}},
    {{"congruence-candidates", "true"}},
    {{"interval-sets", "true"}, {"linear-form", "true"}, {"merge-same", "true"}},
    {{"aig-core-simplification", "true"}},
    {{"aig-core-simplification", "true"}, {"ite-context-simplifications", "true"}},
    {{"skeleton-preproc", "true"}, {"embedded-constraints", "true"}},
    {{"bb.div-v3", "true"}, {"bb.div-v4", "true"}, {"bb.mult-v2", "true"}},
    {{"fp-domain-simplify", "true"}, {"fp-domain-row-bounds", "true"}},
    {{"array-index-hints", "decide"}},
};

// The option sets this build accepts: a set that names an entry the build
// cannot honour is left out rather than failed.
std::vector<Options> usable_option_sets()
{
  std::vector<Options> out;
  for (const OptionSet& set : kOptionSets)
  {
    try
    {
      Options o;
      for (const auto& [name, value] : set)
        o.set(name, value);
      o.resolve();
      out.push_back(o);
    }
    catch (const RecoverableError&)
    {
    }
  }
  return out;
}

// One formula of one of six families, decided under the given options.
// 's' or 'u' is the verdict, '?' an unknown, '!' a model that falsifies an
// assertion, 'E' an error.
char decide(unsigned seed, const Options& options)
{
  std::mt19937 rng(seed);
  TermManager tm;
  Solver s(tm, options);
  const auto bvs = [&](unsigned w, int n) {
    std::vector<Term> v;
    for (int i = 0; i < n; ++i)
      v.push_back(tm.declare("x" + std::to_string(i), tm.mk_bv_sort(w)));
    return v;
  };
  const auto grow = [&](std::vector<Term> pool, unsigned w, int steps) {
    for (int i = 0; i < steps; ++i)
    {
      const Term a = pool[rng() % pool.size()], b = pool[rng() % pool.size()];
      switch (rng() % 9)
      {
        case 0: pool.push_back(bvmul(a, b)); break;
        case 1: pool.push_back(bvadd(a, b)); break;
        case 2: pool.push_back(bvudiv(a, b)); break;
        case 3: pool.push_back(bvsrem(a, b)); break;
        case 4: pool.push_back(bvshl(a, b)); break;
        case 5: pool.push_back(bvlshr(a, b)); break;
        case 6: pool.push_back(ite(bvslt(a, b), a, bvsub(b, a))); break;
        case 7: pool.push_back(bvxor(a, bvnot(b))); break;
        default:
          pool.push_back(concat(extract(w / 2 - 1, 0, a), extract(w - 1, w / 2, b)));
          break;
      }
    }
    return pool;
  };
  try
  {
    switch (rng() % 6)
    {
      case 0: // bit-vector arithmetic
      {
        const unsigned w = 4 + 2 * (rng() % 6);
        const std::vector<Term> p = grow(bvs(w, 3), w, 10);
        s.add(p.back() == p[p.size() - 2]);
        s.add(bvugt(p[p.size() - 3], tm.mk_bv(w, rng() % (1u << w))));
        break;
      }
      case 1: // arrays, a constant array among them
      {
        const Sort as = tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(8));
        const Term a = tm.declare("a", as), b = tm.declare("b", as);
        const std::vector<Term> p = bvs(8, 3);
        const Term c = tm.mk_const_array(as, tm.mk_bv(8, rng() % 256));
        const Term a2 = store(store(a, p[0], p[1]), p[1], p[2]);
        const Term b2 = store(rng() % 2 ? b : c, p[2], p[0]);
        s.add(select(a2, p[2]) == select(b2, p[1]));
        s.add(rng() % 2 ? a2 == b2 : a2 != b2);
        s.add(bvult(select(a, p[0]), select(b, p[2])));
        break;
      }
      case 2: // floating point
      {
        const Sort f = rng() % 2 ? tm.mk_fp16_sort() : tm.mk_fp_sort(3, 4);
        const Term x = tm.declare("fx", f), y = tm.declare("fy", f), z = tm.declare("fz", f);
        const RoundingMode rm = static_cast<RoundingMode>(rng() % 5);
        Term t;
        switch (rng() % 6)
        {
          case 0: t = fp_add(rm, x, y); break;
          case 1: t = fp_mul(rm, x, y); break;
          case 2: t = fp_div(rm, x, y); break;
          case 3: t = fp_fma(tm.mk_rm(rm), x, y, z); break;
          case 4: t = fp_sqrt(tm.mk_rm(rm), x); break;
          default: t = fp_min(x, fp_max(y, z)); break;
        }
        s.add(fp_lt(t, z));
        s.add(not_(fp_is_nan(x)));
        if (rng() % 2)
          s.add(fp_eq(fp_sub(tm.mk_rm(rm), t, x), y));
        break;
      }
      case 3: // uninterpreted functions
      {
        const Sort bv = tm.mk_bv_sort(8);
        const Term f = tm.declare("f", tm.mk_fun_sort({bv}, bv));
        const Term g = tm.declare("g", tm.mk_fun_sort({bv, bv}, bv));
        const std::vector<Term> p = bvs(8, 3);
        s.add(f(p[0]) == g(p[1], p[2]));
        s.add(f(f(p[1])) != f(p[0]));
        s.add(g(p[0], f(p[2])) == bvadd(p[1], tm.mk_bv(8, rng() % 256)));
        if (rng() % 2)
          s.add(p[0] == p[1]);
        break;
      }
      case 4: // Reals
      {
        const Sort r = tm.mk_real_sort();
        const Term x = tm.declare("rx", r), y = tm.declare("ry", r), z = tm.declare("rz", r);
        s.add(real_lt(real_add(x, real_mul(tm.mk_real(static_cast<std::int64_t>(rng() % 7) - 3), y)), z));
        s.add(real_le(z, tm.mk_real(static_cast<std::int64_t>(rng() % 20) - 10, 3)));
        s.add(real_gt(real_sub(x, y), tm.mk_real(static_cast<std::int64_t>(rng() % 9) - 4)));
        break;
      }
      default: // a script, and checks in scopes
      {
        s.parse_smt2("(declare-fun p () (_ BitVec 8)) (declare-fun q () (_ BitVec 8))"
                     "(assert (bvult p q))");
        const Term p = *tm.symbol("p"), q = *tm.symbol("q");
        for (int k = 0; k < 3; ++k)
        {
          s.push();
          s.add(bvugt(bvmul(p, q), tm.mk_bv(8, rng() % 256)));
          (void)s.check_sat();
          if (rng() % 2)
            s.pop();
        }
        break;
      }
    }
    const Result r = s.check_sat();
    if (r.is_sat())
    {
      const Model m = s.model();
      for (const Term& a : s.assertions())
        if (!m.bool_value(a))
          return '!';
      return 's';
    }
    return r.is_unsat() ? 'u' : '?';
  }
  catch (const Error&)
  {
    return 'E';
  }
}

TEST(ThreadStress, managers_on_their_own_threads_answer_as_they_do_alone)
{
  const std::vector<Options> sets = usable_option_sets();
  ASSERT_FALSE(sets.empty());
  const int threads = 8;
  const int formulas = 6;
  const auto options_of = [&](int t, int i) -> const Options& {
    return sets[static_cast<std::size_t>(t * formulas + i) % sets.size()];
  };
  const auto seed_of = [](int t, int i) { return static_cast<unsigned>(1000 * (t + 1) + i); };

  std::vector<std::string> concurrent(threads);
  std::atomic<int> ready{0};
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t)
    pool.emplace_back([&, t] {
      // start together, so that the threads overlap
      ++ready;
      while (ready.load() < threads)
        std::this_thread::yield();
      for (int i = 0; i < formulas; ++i)
        concurrent[t] += decide(seed_of(t, i), options_of(t, i));
    });
  for (std::thread& th : pool)
    th.join();

  for (int t = 0; t < threads; ++t)
    for (int i = 0; i < formulas; ++i)
    {
      SCOPED_TRACE("thread " + std::to_string(t) + " formula " + std::to_string(i));
      const char alone = decide(seed_of(t, i), options_of(t, i));
      EXPECT_NE(concurrent[t][i], '!') << "a model falsified an assertion";
      EXPECT_NE(concurrent[t][i], 'E') << "an error";
      EXPECT_EQ(concurrent[t][i], alone);
    }
}

} // namespace

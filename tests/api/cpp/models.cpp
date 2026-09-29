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

// models.cpp -- models: detached snapshots, completion against
// try_value, the batch reader, array and function values, the core, the
// SMT-LIB text, models over every sort and the model of a term built after
// the check.

#include "api_common.hpp"

#include <limits>
#include <set>
#include <sstream>

using namespace stp;

namespace
{

class Models : public ::testing::Test
{
protected:
  TermManager tm;
  Solver s{tm};
  Sort bv8 = tm.mk_bv_sort(8), bv32 = tm.mk_bv_sort(32);
  Sort A = tm.mk_array_sort(bv32, bv8);
  Sort f32 = tm.mk_fp32_sort(), RM = tm.mk_rm_sort(), R = tm.mk_real_sort();
  Sort S = tm.declare_sort("S");
  Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  Term a = tm.declare("a", A);
  Term f = tm.declare("f", tm.mk_fun_sort({bv8, bv8}, bv8));
  Term I(std::uint64_t i) { return tm.mk_bv(32, i); }
};

TEST_F(Models, detached_snapshot_survives_stack_changes)
{
  s.add(x == 5);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(x), 5u);
  EXPECT_TRUE(m.manager() == tm);
  s.push();
  s.add(x == 6); // not checked yet: the model is still the last answer's
  EXPECT_EQ(m.uint64_value(x), 5u);
  EXPECT_EQ(s.model().uint64_value(x), 5u);
  s.pop();
  s.add(y == 1);
  EXPECT_EQ(s.model().uint64_value(x), 5u);
  EXPECT_FALSE(s.model().in_core(y));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m2 = s.model();
  EXPECT_EQ(m2.uint64_value(y), 1u);
  EXPECT_TRUE(m2.in_core(y));
  EXPECT_FALSE(m.in_core(y)); // the old snapshot is unchanged
  EXPECT_EQ(m.uint64_value(x), 5u);
  // an unsat check leaves the old handle readable and the solver without one
  s.add(x == 7);
  ASSERT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(m2.uint64_value(x), 5u);
  auto e = API_ERROR_OF(s.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("unsat"), std::string::npos);
  // handles are values
  Model copy = m2;
  copy = m;
  EXPECT_FALSE(copy.in_core(y));
  EXPECT_EQ(copy.uint64_value(x), 5u);
  // a model outlives its solver
  std::optional<Model> survivor;
  {
    TermManager t2;
    Solver s2(t2);
    const Term z = t2.declare("z", t2.mk_bv_sort(8));
    s2.add(z == 9);
    ASSERT_TRUE(s2.check_sat().is_sat());
    survivor.emplace(s2.model());
  }
  EXPECT_EQ(survivor->uint64_value(*survivor->manager().symbol("z")), 9u);
}

TEST_F(Models, completion_versus_try_value)
{
  s.add(x == 5);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  // the core holds what the solver assigned
  ASSERT_EQ(m.symbols().size(), 1u);
  EXPECT_TRUE(m.symbols()[0].same_as(x));
  EXPECT_TRUE(m.in_core(x));
  EXPECT_FALSE(m.in_core(y));
  // value completes with the sort's default, try_value refuses to
  EXPECT_EQ(m.value(y).to_uint64(), 0u);
  EXPECT_FALSE(m.try_value(y).has_value());
  ASSERT_TRUE(m.try_value(x).has_value());
  EXPECT_EQ(m.try_value(x)->to_uint64(), 5u);
  EXPECT_FALSE(m.try_value(x + y).has_value());
  EXPECT_TRUE(m.try_value(x + 1).has_value());
  EXPECT_EQ(m.value(x + y).to_uint64(), 5u);
  EXPECT_EQ(m.value(tm.mk_bv(8, 3)).to_uint64(), 3u); // a value is its own value
  EXPECT_TRUE(m.try_value(tm.mk_true()).has_value());
  // the defaults of every sort
  EXPECT_FALSE(m.bool_value(tm.declare("b", tm.mk_bool_sort())));
  EXPECT_EQ(m.fp_value(tm.declare("fx", f32)).cls, FloatValue::Class::ZERO);
  EXPECT_FALSE(m.fp_value(tm.declare("fx", f32)).sign);
  EXPECT_EQ(m.rm_value(tm.declare("rm", RM)), RoundingMode::RNE);
  EXPECT_EQ(m.real_value(tm.declare("r", R)).str(), "0");
  EXPECT_EQ(m.uninterpreted_index(tm.declare("p", S)), 0u);
  EXPECT_EQ(m.uint64_value(a[I(3)]), 0u);
  EXPECT_EQ(m.array_value(a).size(), 0u);
  EXPECT_EQ(m.array_value(a).default_value().to_uint64(), 0u);
  EXPECT_EQ(m.function_value(f).size(), 0u);
  EXPECT_EQ(m.function_value(f).else_value().to_uint64(), 0u);
  EXPECT_EQ(m.uint64_value(f(x, y)), 0u);
  EXPECT_FALSE(m.try_value(f(x, y)).has_value());
  EXPECT_FALSE(m.try_value(a[I(3)]).has_value());
  EXPECT_TRUE(m.value(a).sort() == A);
  // the batch reader completes as value does
  const std::vector<Term> vs = m.values({x, y, x + 1, bvult(x, y)});
  ASSERT_EQ(vs.size(), 4u);
  EXPECT_EQ(vs[0].to_uint64(), 5u);
  EXPECT_EQ(vs[1].to_uint64(), 0u);
  EXPECT_EQ(vs[2].to_uint64(), 6u);
  EXPECT_FALSE(vs[3].to_bool());
  EXPECT_TRUE(m.values({}).empty());
  // every value the model returns is a VALUE term of the right sort
  for (const Term& v : vs)
    EXPECT_TRUE(v.is_value());
  EXPECT_TRUE(m.value(x).sort() == bv8);
  EXPECT_EQ(m.value(x).kind(), Kind::VALUE);
  // and can be asserted back
  s.add(y == m.value(y));
  s.add(x == m.value(x));
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A Real symbol no arithmetic of the check mentioned is outside the core, as a
// bit-vector symbol the solve never saw is: the exact model's zero for it made
// in_core true, try_value 0 and to_smt2 print it.
TEST_F(Models, an_unused_real_is_outside_the_core)
{
  const Term r = tm.declare("r", R), unused = tm.declare("ur", R);
  s.add(x == 1);
  s.add(real_gt(r, tm.mk_real(1, 2)));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.in_core(r));
  EXPECT_FALSE(m.in_core(unused));
  EXPECT_FALSE(m.try_value(unused).has_value());
  EXPECT_EQ(m.real_value(unused).str(), "0"); // value completes it
  EXPECT_EQ(m.to_smt2().find("ur"), std::string::npos) << m.to_smt2();
  EXPECT_EQ(m.symbols().size(), 2u);
}

// Whether `t` holds no declared symbol: the shape of a value term.
bool symbol_free(const Term& t)
{
  if (t.is_const())
    return false;
  for (const Term& c : t.children())
    if (!symbol_free(c))
      return false;
  return true;
}

// An array's value is a term with no symbol in it, the constant array of its
// default under a store per cell: array_value(t).as_term(). A function has no
// value term. try_value completes nothing: an array needs its base in the core
// (or a constant array) and every symbol it reads there.
TEST_F(Models, the_value_of_an_array_or_a_function_term)
{
  const Term i = tm.declare("i", bv32), j = tm.declare("j", bv32);
  const Term b = tm.declare("b", A), c = tm.declare("c", tm.mk_bool_sort());
  s.add(a[I(1)] == 10);
  s.add(a[i] == 7);
  s.add(i == 200);
  s.add(c);
  s.add(f(x, x) == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  const Term va = m.value(a);
  EXPECT_TRUE(va.same_as(m.array_value(a).as_term()));
  EXPECT_TRUE(va.sort() == A);
  EXPECT_TRUE(symbol_free(va));
  EXPECT_EQ(m.uint64_value(va[I(1)]), 10u);
  EXPECT_EQ(m.uint64_value(va[I(200)]), 7u);
  // a store over it, an ite of arrays: evaluated, not handed back
  const Term st = store(a, i, tm.mk_bv(8, 9));
  const Term vst = m.value(st);
  EXPECT_TRUE(vst.same_as(m.array_value(st).as_term()));
  EXPECT_TRUE(symbol_free(vst));
  EXPECT_EQ(m.uint64_value(vst[I(200)]), 9u);
  EXPECT_EQ(m.uint64_value(vst[I(1)]), 10u);
  const Term it = ite(c, st, b);
  EXPECT_TRUE(m.value(it).same_as(vst));
  // the batch reader alike
  const std::vector<Term> vs = m.values({a, st, x});
  ASSERT_EQ(vs.size(), 3u);
  EXPECT_TRUE(vs[0].same_as(va));
  EXPECT_TRUE(vs[1].same_as(vst));
  // a value term asserts back
  s.add(a == va);
  EXPECT_TRUE(s.check_sat().is_sat());

  // try_value: arrays of the core, and what reads only the core, are values
  ASSERT_TRUE(m.try_value(a).has_value());
  EXPECT_TRUE(m.try_value(a)->same_as(va));
  ASSERT_TRUE(m.try_value(it).has_value());
  EXPECT_TRUE(m.try_value(it)->same_as(vst));
  // but not an array outside the core, nor a store at a symbol outside it
  EXPECT_FALSE(m.in_core(b));
  EXPECT_FALSE(m.try_value(b).has_value());
  EXPECT_TRUE(symbol_free(m.value(b)));
  EXPECT_FALSE(m.try_value(store(a, j, tm.mk_bv(8, 1))).has_value());
  EXPECT_FALSE(m.try_value(ite(c, b, a)).has_value());
  // a constant array is its own base
  const Term k = tm.mk_const_array(A, tm.mk_bv(8, 4));
  ASSERT_TRUE(m.try_value(store(k, i, x)).has_value());

  // a function: SORT_MISMATCH from each reader, pointing at function_value
  for (auto read : {+[](const Model& mm, const Term& t) { (void)mm.value(t); },
                    +[](const Model& mm, const Term& t) { (void)mm.try_value(t); },
                    +[](const Model& mm, const Term& t) { (void)mm.values({t}); }})
  {
    auto e = API_ERROR_OF(read(m, f));
    ASSERT_TRUE(e.has_value());
    EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH);
    EXPECT_NE(std::string(e->what()).find("function_value"), std::string::npos) << e->what();
  }
  EXPECT_EQ(m.function_value(f).size(), 1u);
}

TEST(ArrayEqualityModels, try_value_refuses_missing_bases)
{
  for (bool simplify : {false, true})
    for (const char* fill : {"zero", "ones"})
    {
      SCOPED_TRACE(simplify);
      SCOPED_TRACE(fill);
      TermManager::Config config;
      config.simplify = simplify;
      TermManager tm(config);
      const Sort bv2 = tm.mk_bv_sort(2), A = tm.mk_array_sort(bv2, bv2);
      const Term a = tm.declare("a", A), b = tm.declare("b", A);
      const Term zero = tm.mk_bv(2, 0), one = tm.mk_bv(2, 1);
      const Term k = tm.mk_const_array(A, zero);
      Solver s(tm);
      s.options().set_str("model-array-fill", fill);
      ASSERT_TRUE(s.check_sat().is_sat());
      const Model m = s.model();
      const Term late = tm.declare("late", A);
      EXPECT_FALSE(m.in_core(a));
      EXPECT_FALSE(m.in_core(b));
      EXPECT_FALSE(m.try_value(a).has_value());
      EXPECT_FALSE(m.try_value(b).has_value());
      // Explicit completion still uses the configured fill, without adding
      // the missing arrays to the snapshot for later non-completing reads.
      EXPECT_TRUE(m.bool_value(a == b));
      EXPECT_FALSE(m.bool_value(a != b));
      EXPECT_EQ(m.bool_value(a == k), std::string(fill) == "zero");
      for (const Term& t : {a == b, a != b, a == k, k == b, distinct({a, b, late}),
                            store(a, zero, one) == store(b, zero, one)})
        EXPECT_FALSE(m.try_value(t).has_value()) << t;
      EXPECT_FALSE(m.in_core(a));
      EXPECT_FALSE(m.in_core(b));
    }
}

TEST(ArrayEqualityModels, determined_without_base_values)
{
  for (bool simplify : {false, true})
  {
    SCOPED_TRACE(simplify);
    TermManager::Config config;
    config.simplify = simplify;
    TermManager tm(config);
    const Sort bv1 = tm.mk_bv_sort(1), A = tm.mk_array_sort(bv1, bv1);
    const Term a = tm.declare("a", A), b = tm.declare("b", A);
    const Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
    const Term k0 = tm.mk_const_array(A, zero), k1 = tm.mk_const_array(A, one);
    Solver s(tm);
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    const auto determined = [&](const Term& left, const Term& right, bool equal) {
      const auto eq = m.try_value(left == right), ne = m.try_value(left != right);
      ASSERT_TRUE(eq.has_value());
      ASSERT_TRUE(ne.has_value());
      EXPECT_EQ(eq->to_bool(), equal);
      EXPECT_EQ(ne->to_bool(), !equal);
    };
    determined(a, a, true);
    determined(k0, k1, false);
    const Term half_a = store(a, zero, one), half_b = store(b, zero, one);
    // The same unknown base needs no fill; a known differing cell also
    // decides the result without looking at either base's default.
    determined(half_a, half_a, true);
    determined(half_a, store(b, zero, zero), false);
    // Writes covering both indices on both sides leave no unknown cells.
    const Term full_a = store(half_a, one, zero), full_b = store(half_b, one, zero);
    determined(full_a, full_b, true);
    determined(full_a, k1, false);
    EXPECT_FALSE(m.try_value(half_a == half_b).has_value());
    // Covering the domain only in the union still needs a missing cell on
    // each side; it must not be mistaken for full coverage of both arrays.
    EXPECT_FALSE(m.try_value(half_a == store(b, one, zero)).has_value());
  }
}

TEST(ArrayEqualityModels, uses_recorded_fills_without_completion)
{
  for (bool simplify : {false, true})
    for (const char* fill : {"zero", "ones"})
    {
      SCOPED_TRACE(simplify);
      SCOPED_TRACE(fill);
      TermManager::Config config;
      config.simplify = simplify;
      TermManager tm(config);
      const Sort bv2 = tm.mk_bv_sort(2), A = tm.mk_array_sort(bv2, bv2);
      const Term a = tm.declare("a", A), b = tm.declare("b", A);
      const Term zero = tm.mk_bv(2, 0), one = tm.mk_bv(2, 1);
      Solver s(tm);
      s.options().set_str("model-array-fill", fill);
      s.add(a[zero] == one);
      s.add(b[zero] == one);
      ASSERT_TRUE(s.check_sat().is_sat());
      const Model m = s.model();
      ASSERT_TRUE(m.in_core(a));
      ASSERT_TRUE(m.in_core(b));
      const Term same = store(tm.mk_const_array(A, m.array_value(a).default_value()), zero, one);
      const Term different = store(tm.mk_const_array(A, tm.mk_bv(2, 2)), zero, one);
      for (const auto& [t, expected] :
           {std::pair<Term, bool>{a == b, true}, {a == same, true}, {a == different, false}})
      {
        const auto value = m.try_value(t);
        ASSERT_TRUE(value.has_value()) << t;
        EXPECT_EQ(value->to_bool(), expected);
      }
    }
}

TEST_F(Models, array_values)
{
  const Term i = tm.declare("i", bv32);
  s.add(a[I(1)] == 10);
  s.add(a[I(5)] == 50);
  s.add(a[I(3)] == 30);
  s.add(a[i] == 7);
  s.add(i == 200);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const ArrayValue av = m.array_value(a);
  EXPECT_TRUE(av.sort() == A);
  EXPECT_GE(av.size(), 4u);
  EXPECT_EQ(av.entries().size(), av.size());
  // ascending by unsigned index, every entry a value
  std::uint64_t last = 0;
  bool first = true;
  std::set<std::uint64_t> indices;
  for (const ArrayValue::Entry& e : av.entries())
  {
    EXPECT_TRUE(e.index.is_value());
    EXPECT_TRUE(e.element.is_value());
    EXPECT_TRUE(e.index.sort() == bv32);
    EXPECT_TRUE(e.element.sort() == bv8);
    const std::uint64_t idx = e.index.to_uint64();
    if (!first)
    {
      EXPECT_GT(idx, last);
    }
    first = false;
    last = idx;
    indices.insert(idx);
  }
  for (std::uint64_t idx : {1u, 3u, 5u, 200u})
    EXPECT_EQ(indices.count(idx), 1u) << idx;
  EXPECT_EQ(av.at(I(1)).to_uint64(), 10u);
  EXPECT_EQ(av.at(I(3)).to_uint64(), 30u);
  EXPECT_EQ(av.at(I(5)).to_uint64(), 50u);
  EXPECT_EQ(av.at(I(200)).to_uint64(), 7u);
  EXPECT_EQ(av.at(I(77)).to_uint64(), av.default_value().to_uint64()); // absent: the default
  EXPECT_EQ(av.default_value().to_uint64(), 0u);
  EXPECT_TRUE(av.default_value().is_value());
  EXPECT_TRUE(av.entry(0).index.same_as(av.entries()[0].index));
  API_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, av.entry(av.size()));
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, av.at(i));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, av.at(Term()));
  // the term form: a store chain over a constant array with the same reads
  const Term chain = av.as_term();
  EXPECT_TRUE(chain.sort() == A);
  EXPECT_EQ(chain.kind(), av.size() == 0 ? Kind::CONST_ARRAY : Kind::STORE);
  EXPECT_EQ(select(chain, I(5)).to_uint64(), 50u);
  EXPECT_EQ(select(chain, I(77)).to_uint64(), 0u);
  EXPECT_EQ(m.uint64_value(select(chain, I(200))), 7u);
  // re-asserted through its reads it is consistent with the model
  for (const ArrayValue::Entry& e : av.entries())
    s.add(a[e.index] == select(chain, e.index));
  s.add(a[I(77)] == select(chain, I(77)));
  EXPECT_TRUE(s.check_sat().is_sat());
  // and re-asserted as a whole: the value is an array the engine decides
  // equality against (constant arrays are its own)
  s.add(a == chain);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(a == chain));
  // a model over an array read at a symbolic index built after the check
  const Term j = tm.declare("j", bv32);
  EXPECT_EQ(m.uint64_value(a[j]), 0u); // j completes to 0, a[0] is unobserved
  EXPECT_EQ(m.uint64_value(a[i + 0]), 7u);
  EXPECT_EQ(m.uint64_value(select(store(a, I(1), tm.mk_bv(8, 99)), I(1))), 99u);
  EXPECT_EQ(m.uint64_value(select(store(a, I(1), tm.mk_bv(8, 99)), I(3))), 30u);
  EXPECT_EQ(m.array_value(store(a, I(9), tm.mk_bv(8, 90))).at(I(9)).to_uint64(), 90u);
  EXPECT_EQ(m.array_value(store(a, I(9), tm.mk_bv(8, 90))).at(I(3)).to_uint64(), 30u);
  // dense bytes
  std::uint8_t out[8] = {1, 1, 1, 1, 1, 1, 1, 1};
  m.array_bytes(a, 0, 8, out);
  EXPECT_EQ(out[0], 0u);
  EXPECT_EQ(out[1], 10u);
  EXPECT_EQ(out[2], 0u);
  EXPECT_EQ(out[3], 30u);
  EXPECT_EQ(out[5], 50u);
  EXPECT_EQ(out[7], 0u);
  std::uint8_t two[2] = {9, 9};
  m.array_bytes(a, 199, 2, two);
  EXPECT_EQ(two[0], 0u);
  EXPECT_EQ(two[1], 7u);
  m.array_bytes(a, 0, 0, nullptr); // nothing to write
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, m.array_bytes(a, 0, 1, nullptr));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.array_bytes(x, 0, 1, out));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.array_value(x));
  const Term narrow = tm.declare("narrow", tm.mk_array_sort(bv8, tm.mk_bv_sort(12)));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(narrow, 0, 1, out));
  const Term small = tm.declare("small", tm.mk_array_sort(bv8, bv8));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(small, 250, 10, out));
  m.array_bytes(small, 250, 6, out); // [250, 256) fits
  // checked without first + count - 1, which wraps at 2^64
  const std::uint64_t top = std::numeric_limits<std::uint64_t>::max();
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(small, top, 2, out));
  const Term word = tm.declare("word", tm.mk_array_sort(tm.mk_bv_sort(64), bv8));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(word, top, 2, out));
  m.array_bytes(word, top, 1, out); // [2^64 - 1, 2^64) fits
  {
    // past 64 bits an index beyond 2^64 - 1 carries into bit 64
    const Sort bv65 = tm.mk_bv_sort(65);
    Term cells = tm.mk_const_array(tm.mk_array_sort(bv65, bv8), tm.mk_bv(8, 0));
    cells = store(cells, tm.mk_bv(65, 0), tm.mk_bv(8, 11));
    cells = store(cells, tm.mk_bv(65, top), tm.mk_bv(8, 22));
    cells = store(cells, tm.mk_bv(65, "18446744073709551616", 10), tm.mk_bv(8, 33));
    std::uint8_t across[2] = {0, 0};
    m.array_bytes(cells, top, 2, across);
    EXPECT_EQ(across[0], 22u);
    EXPECT_EQ(across[1], 33u);
  }
  // wide elements come out little-endian per element
  const Term wide = tm.declare("wide", tm.mk_array_sort(bv8, bv32));
  s.add(wide[tm.mk_bv(8, 0)] == 0x11223344);
  ASSERT_TRUE(s.check_sat().is_sat());
  std::uint8_t w[8] = {0};
  s.model().array_bytes(wide, 0, 2, w);
  EXPECT_EQ(w[0], 0x44u);
  EXPECT_EQ(w[1], 0x33u);
  EXPECT_EQ(w[2], 0x22u);
  EXPECT_EQ(w[3], 0x11u);
  EXPECT_EQ(w[4], 0u);
  // arrays holding floats
  const Term af = tm.declare("af", tm.mk_array_sort(bv8, f32));
  s.add(fp_eq(af[tm.mk_bv(8, 2)], tm.mk_fp(f32, RoundingMode::RNE, 2.5)));
  ASSERT_TRUE(s.check_sat().is_sat());
  const ArrayValue afv = s.model().array_value(af);
  EXPECT_EQ(afv.at(tm.mk_bv(8, 2)).to_fp().to_double(), std::optional<double>(2.5));
  EXPECT_EQ(afv.default_value().to_fp().cls, FloatValue::Class::ZERO);
}

TEST_F(Models, function_values)
{
  const Term g = tm.declare("g", tm.mk_fun_sort({bv8}, tm.mk_bool_sort()));
  const Term h = tm.declare("h", tm.mk_fun_sort({bv8}, bv8)); // never applied
  s.add(f(tm.mk_bv(8, 1), tm.mk_bv(8, 2)) == 3);
  s.add(f(tm.mk_bv(8, 2), tm.mk_bv(8, 1)) == 4);
  s.add(f(x, y) == 9);
  s.add(x == 5);
  s.add(y == 6);
  s.add(g(x));
  s.add(!g(tm.mk_bv(8, 0)));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const FunctionValue fv = m.function_value(f);
  EXPECT_TRUE(fv.is_tabular());
  EXPECT_TRUE(fv.sort() == f.sort());
  EXPECT_GE(fv.size(), 3u);
  EXPECT_EQ(fv.entries().size(), fv.size());
  for (const FunctionValue::Entry& e : fv.entries())
  {
    ASSERT_EQ(e.args.size(), 2u);
    EXPECT_TRUE(e.args[0].is_value());
    EXPECT_TRUE(e.args[1].is_value());
    EXPECT_TRUE(e.value.is_value());
    EXPECT_TRUE(fv.apply(e.args).same_as(e.value));
  }
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 1), tm.mk_bv(8, 2)}).to_uint64(), 3u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 2), tm.mk_bv(8, 1)}).to_uint64(), 4u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 5), tm.mk_bv(8, 6)}).to_uint64(), 9u);
  EXPECT_TRUE(fv.else_value().is_value());
  EXPECT_TRUE(fv.else_value().sort() == bv8);
  EXPECT_TRUE(fv.apply({tm.mk_bv(8, 77), tm.mk_bv(8, 78)}).same_as(fv.else_value()));
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, fv.apply({x, y}));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, fv.apply({Term(), Term()}));
  API_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, fv.entry(fv.size()));
  // the ite form agrees with apply wherever the formals are evaluated
  const Term p = tm.declare("p", bv8), q = tm.declare("q", bv8);
  const Term body = fv.as_ite_term({p, q});
  EXPECT_TRUE(body.sort() == bv8);
  EXPECT_EQ(m.uint64_value(body.substitute({{p, tm.mk_bv(8, 1)}, {q, tm.mk_bv(8, 2)}})), 3u);
  EXPECT_EQ(m.uint64_value(body.substitute({{p, tm.mk_bv(8, 5)}, {q, tm.mk_bv(8, 6)}})), 9u);
  EXPECT_EQ(m.uint64_value(fv.as_ite_term({x, y})), 9u);
  EXPECT_EQ(m.uint64_value(fv.as_ite_term({tm.mk_bv(8, 2), tm.mk_bv(8, 1)})), 4u);
  API_EXPECT_ERROR(ErrorCode::ARITY, fv.as_ite_term({p}));
  // applications evaluate through the model, before or after the check
  EXPECT_EQ(m.uint64_value(f(x, y)), 9u);
  EXPECT_EQ(m.uint64_value(f(tm.mk_bv(8, 1), tm.mk_bv(8, 2))), 3u);
  EXPECT_EQ(m.uint64_value(f(y, x)), fv.apply({tm.mk_bv(8, 6), tm.mk_bv(8, 5)}).to_uint64());
  EXPECT_TRUE(m.in_core(f));
  // a Boolean-valued function
  const FunctionValue gv = m.function_value(g);
  EXPECT_TRUE(gv.apply({tm.mk_bv(8, 5)}).to_bool());
  EXPECT_FALSE(gv.apply({tm.mk_bv(8, 0)}).to_bool());
  EXPECT_TRUE(m.bool_value(g(x)));
  EXPECT_TRUE(gv.else_value().sort().is_bool());
  // a function the solver never saw
  const FunctionValue hv = m.function_value(h);
  EXPECT_EQ(hv.size(), 0u);
  EXPECT_EQ(hv.else_value().to_uint64(), 0u);
  EXPECT_EQ(hv.apply({tm.mk_bv(8, 1)}).to_uint64(), 0u);
  EXPECT_FALSE(m.in_core(h));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.function_value(x));
  // the text of the model has the function as an ite
  const std::string text = m.to_smt2();
  EXPECT_NE(text.find("(define-fun f ((x!0 (_ BitVec 8)) (x!1 (_ BitVec 8))) (_ BitVec 8)"), std::string::npos);
  EXPECT_NE(text.find("(ite (and (= x!0"), std::string::npos);
}

TEST_F(Models, defined_function_interpretations_freeze_globals_and_uf_tables)
{
  s.parse_smt2("(define-fun plus_x ((p (_ BitVec 8))) (_ BitVec 8) (bvadd p x)) "
               "(define-fun via_uf ((p (_ BitVec 8))) (_ BitVec 8) (bvadd (f p x) x)) "
               "(define-fun read_a ((p (_ BitVec 32))) (_ BitVec 8) (select a p))");
  const Term plus = *tm.symbol("plus_x"), via = *tm.symbol("via_uf");
  const Term read = *tm.symbol("read_a");
  s.add(x == 5);
  s.add(f(tm.mk_bv(8, 1), x) == 7);
  s.add(a[I(9)] == 42);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model old = s.model();
  const FunctionValue pv = old.function_value(plus), fv = old.function_value(via);
  const FunctionValue av = old.function_value(read);
  EXPECT_FALSE(pv.is_tabular());
  EXPECT_TRUE(pv.sort() == plus.sort());
  EXPECT_EQ(pv.apply({tm.mk_bv(8, 1)}).to_uint64(), 6u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 1)}).to_uint64(), 12u);
  EXPECT_EQ(av.apply({I(9)}).to_uint64(), 42u);
  EXPECT_FALSE(old.in_core(plus)); // a definition expands, it is not assigned
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, pv.size());
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, pv.entry(0));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, pv.entries());
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, pv.else_value());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, old.value(plus));
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, pv.apply({x}));
  API_EXPECT_ERROR(ErrorCode::ARITY, pv.apply({}));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, pv.apply({I(0)}));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, pv.as_ite_term({Term()}));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, pv.as_ite_term({I(0)}));
  TermManager foreign;
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, pv.as_ite_term({foreign.mk_bv(8, 1)}));
  // Supplied arguments are not themselves frozen: using a global as the
  // formal below must distinguish its bound occurrence from its free one.
  const Term pbody = pv.as_ite_term({x}), fbody = fv.as_ite_term({y});
  const Term index = tm.declare("index", bv32);
  const Term abody = av.as_ite_term({index});
  s.reset();
  s.add(x == 100);
  s.add(y == 1);
  s.add(index == 9);
  s.add(f(y, x) == 99);
  s.add(a[index] == 99);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model newer = s.model();
  EXPECT_EQ(newer.uint64_value(pbody), 105u);
  EXPECT_EQ(newer.uint64_value(fbody), 12u);
  EXPECT_EQ(newer.uint64_value(abody), 42u);
  EXPECT_EQ(newer.function_value(plus).apply({tm.mk_bv(8, 1)}).to_uint64(), 101u);
  EXPECT_EQ(pv.apply({tm.mk_bv(8, 1)}).to_uint64(), 6u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 1)}).to_uint64(), 12u);
  EXPECT_EQ(av.apply({I(9)}).to_uint64(), 42u);
  // A definition introduced after the check can still be read in that model.
  s.parse_smt2("(define-fun later ((p (_ BitVec 8))) (_ BitVec 8) (plus_x p))");
  EXPECT_EQ(old.function_value(*tm.symbol("later")).apply({tm.mk_bv(8, 1)}).to_uint64(), 6u);
}

TEST_F(Models, defined_functions_support_array_and_real_arguments_and_results)
{
  s.parse_smt2("(define-fun update ((arr (Array (_ BitVec 32) (_ BitVec 8))) "
                 "(p (_ BitVec 32))) (Array (_ BitVec 32) (_ BitVec 8)) (store arr p #x07)) "
               "(define-fun double_real ((r Real)) Real (+ r r)) "
               "(define-fun identity_u ((u S)) S u) "
               "(define-fun flip ((b Bool)) Bool (not b)) "
               "(define-fun round ((r RoundingMode)) RoundingMode r) "
               "(define-fun abs ((f (_ FloatingPoint 8 24))) (_ FloatingPoint 8 24) (fp.abs f))");
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model model = s.model();
  const Term base = tm.mk_const_array(A, tm.mk_bv(8, 2));
  const FunctionValue update = model.function_value(*tm.symbol("update"));
  const Term array = update.apply({base, I(3)});
  EXPECT_EQ(model.uint64_value(array[I(3)]), 7u);
  EXPECT_EQ(model.uint64_value(array[I(4)]), 2u);
  EXPECT_TRUE(update.as_ite_term({a, I(3)}).same_as(store(a, I(3), tm.mk_bv(8, 7))));
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, update.apply({a, I(3)}));
  const FunctionValue real = model.function_value(*tm.symbol("double_real"));
  EXPECT_EQ(real.apply({tm.mk_real("1/3")}).to_rational().str(), "2/3");
  const Term u = tm.declare("u", S);
  const Term uv = model.value(u);
  EXPECT_TRUE(model.function_value(*tm.symbol("identity_u")).apply({uv}).same_as(uv));
  EXPECT_TRUE(model.function_value(*tm.symbol("flip")).apply({tm.mk_false()}).to_bool());
  EXPECT_EQ(model.function_value(*tm.symbol("round")).apply({tm.mk_rm(RoundingMode::RTZ)}).to_rm(),
            RoundingMode::RTZ);
  EXPECT_EQ(model.function_value(*tm.symbol("abs")).apply({tm.mk_fp(f32, RoundingMode::RNE, -1.5)})
                .to_fp().to_double(), std::optional<double>(1.5));
}

TEST_F(Models, defined_functions_evaluate_partial_fp_in_the_saved_model)
{
  s.parse_smt2("(define-fun convert ((p (_ FloatingPoint 8 24))) (_ BitVec 8) "
                "((_ fp.to_ubv 8) RTZ p))");
  const Term convert = *tm.symbol("convert");
  const Term nan = tm.mk_fp_nan(f32);
  s.add(convert(nan) == 42);
  ASSERT_TRUE(s.check_sat().is_sat());
  const FunctionValue value = s.model().function_value(convert);
  EXPECT_EQ(value.apply({nan}).to_uint64(), 42u);
  const Term p = tm.declare("p", f32);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, value.as_ite_term({p}));
  s.reset();
  s.add(convert(nan) == 17);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(value.apply({nan}).to_uint64(), 42u);
  EXPECT_EQ(s.model().function_value(convert).apply({nan}).to_uint64(), 17u);
}

TEST_F(Models, functions_over_declared_sorts)
{
  // k : S -> S and h : S -> BV4 are tabled over elements of S, not over the
  // bit-vectors that carry them in the solver
  const Term u = tm.declare("u", S), v = tm.declare("v", S);
  const Term k = tm.declare("k", tm.mk_fun_sort({S}, S));
  const Term h = tm.declare("h", tm.mk_fun_sort({S}, tm.mk_bv_sort(4)));
  s.add(u == k(k(u)));
  s.add(u != k(u));
  s.add(h(u) == tm.mk_bv(4, 5));
  s.add(h(v) == tm.mk_bv(4, 9));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(u == k(k(u))));
  EXPECT_TRUE(m.bool_value(u != k(u)));
  EXPECT_EQ(m.uint64_value(h(u)), 5u);
  EXPECT_EQ(m.uint64_value(h(v)), 9u);
  EXPECT_TRUE(m.value(k(u)).is_value());
  EXPECT_TRUE(m.value(k(u)).sort() == S);
  EXPECT_TRUE(m.value(k(k(u))).same_as(m.value(u)));
  const FunctionValue kv = m.function_value(k);
  EXPECT_GE(kv.size(), 2u);
  for (const FunctionValue::Entry& e : kv.entries())
  {
    ASSERT_EQ(e.args.size(), 1u);
    EXPECT_TRUE(e.args[0].sort() == S);
    EXPECT_TRUE(e.value.sort() == S);
    EXPECT_TRUE(kv.apply(e.args).same_as(e.value));
  }
  EXPECT_TRUE(kv.else_value().sort() == S);
  EXPECT_TRUE(kv.apply({m.value(u)}).same_as(m.value(k(u))));
  const FunctionValue hv = m.function_value(h);
  for (const FunctionValue::Entry& e : hv.entries())
    EXPECT_TRUE(e.args[0].sort() == S);
  EXPECT_EQ(hv.apply({m.value(u)}).to_uint64(), 5u);
  EXPECT_EQ(hv.apply({m.value(v)}).to_uint64(), 9u);
  // the text names the elements, never a carrier's bits
  const std::string text = m.to_smt2();
  const std::size_t kdef = text.find("(define-fun k ((x!0 S)) S (ite (= x!0 S!");
  ASSERT_NE(kdef, std::string::npos);
  EXPECT_EQ(text.substr(kdef, text.find('\n', kdef) - kdef).find("#x"), std::string::npos);
  // the values re-assert consistently
  s.add(k(u) == m.value(k(u)));
  s.add(u == m.value(u));
  s.add(v == m.value(v));
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A table of 256 constants written over an array, looked up at a byte read
// once from another array: unconstrained-variable elimination substitutes the
// input array by a write over a fresh array, and taking the model refused
// that entry (INTERNAL, the manager poisoned).
TEST_F(Models, an_array_substituted_by_elimination)
{
  const Term input = tm.declare("input", A);
  Term table = tm.declare("table", A);
  for (std::uint64_t i = 0; i < 256; ++i)
    table = store(table, I(i), tm.mk_bv(8, (i * 7) & 0xff));
  const Term byte = input[I(0)];
  const Term lookup = table[concat(tm.mk_bv(24, 0), byte)];
  s.add(lookup == 0);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(lookup == 0));
  EXPECT_EQ(m.uint64_value(byte), 0u);
  EXPECT_EQ(m.array_value(input).at(I(0)).to_uint64(), 0u);
  EXPECT_TRUE(m.in_core(input));
}

// Default options, arrays and a function: the fourth check engages the
// incremental driver, whose model maps an array to a write over an array
// unconstrained-variable elimination made. The model is read, not refused,
// and every assertion holds in it.
TEST_F(Models, arrays_and_a_function_under_the_incremental_driver)
{
  const Sort b4 = tm.mk_bv_sort(4);
  const Sort arr = tm.mk_array_sort(b4, bv8);
  const Term z = tm.declare("z", bv8);
  const Term i = tm.declare("i", b4), j = tm.declare("j", b4);
  const Term p = tm.declare("p", arr), q = tm.declare("q", arr);
  const Term g = tm.declare("g", tm.mk_fun_sort({bv8}, bv8));
  s.push();
  s.add(!(z == p[i]));
  s.push();
  s.add(i == j);
  const Term m1 = tm.mk_bv(8, 0xd8) ^ x;
  s.add(ite(bvugt(m1, g(y)), g(y), m1) == q[i]);
  for (int k = 0; k < 3; ++k)
    ASSERT_TRUE(s.check_sat().is_sat()) << k;
  const Term lo = concat(tm.mk_bv(7, 0), extract(7, 7, y));
  s.add(store(p, j, p[i])[i] == ite(bvugt(x, lo), lo, x));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  for (const Term& a : s.assertions())
    EXPECT_TRUE(m.bool_value(a)) << a;
  EXPECT_NO_THROW(s.push());
}

// A value object answers only about its own sort: an index or argument of
// another sort, of another manager or of the wrong arity used to answer the
// default.
TEST_F(Models, value_objects_check_their_arguments)
{
  s.add(a[I(1)] == 10);
  s.add(f(tm.mk_bv(8, 1), tm.mk_bv(8, 2)) == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const ArrayValue av = m.array_value(a);
  const FunctionValue fv = m.function_value(f);
  EXPECT_EQ(av.at(I(1)).to_uint64(), 10u);
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, av.at(tm.mk_bv(8, 1)));
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 1), tm.mk_bv(8, 2)}).to_uint64(), 3u);
  API_EXPECT_ERROR(ErrorCode::ARITY, fv.apply({tm.mk_bv(8, 1)}));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, fv.apply({tm.mk_bv(8, 1), tm.mk_bv(16, 2)}));
  TermManager other;
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, av.at(other.mk_bv(32, 1)));
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, fv.apply({other.mk_bv(8, 1), tm.mk_bv(8, 2)}));
}

TEST_F(Models, core_and_text)
{
  s.add(x == 5);
  s.add(a[I(1)] == 10);
  s.add(f(tm.mk_bv(8, 1), tm.mk_bv(8, 2)) == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const std::vector<Term> core = m.symbols();
  ASSERT_EQ(core.size(), 3u);
  EXPECT_TRUE(core[0].same_as(a)); // name order
  EXPECT_TRUE(core[1].same_as(f));
  EXPECT_TRUE(core[2].same_as(x));
  EXPECT_TRUE(m.in_core(a));
  EXPECT_TRUE(m.in_core(f));
  EXPECT_TRUE(m.in_core(x));
  EXPECT_FALSE(m.in_core(y));
  EXPECT_FALSE(m.in_core(x + 1));
  const std::string text = m.to_smt2();
  EXPECT_EQ(text.substr(0, 2), "(\n");
  EXPECT_EQ(text.substr(text.size() - 2), ")\n");
  EXPECT_NE(text.find("(define-fun x () (_ BitVec 8) #x05)"), std::string::npos);
  EXPECT_NE(text.find("(define-fun a () (Array (_ BitVec 32) (_ BitVec 8)) (store ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x00) #x00000001 #x0a))"), std::string::npos);
  EXPECT_NE(text.find("(define-fun f ((x!0 (_ BitVec 8)) (x!1 (_ BitVec 8))) (_ BitVec 8) (ite (and (= x!0 #x01) (= x!1 #x02)) #x03"), std::string::npos);
  EXPECT_EQ(text.find("define-fun y"), std::string::npos);
  std::ostringstream os;
  os << m;
  EXPECT_EQ(os.str(), text);
}

TEST_F(Models, every_sort)
{
  const Term fx = tm.declare("fx", f32), fy = tm.declare("fy", f32);
  const Term rm = tm.declare("rm", RM);
  const Term r = tm.declare("r", R);
  const Term p = tm.declare("p", S), q = tm.declare("q", S), u = tm.declare("u", S);
  const Term b = tm.declare("b", tm.mk_bool_sort());
  const Term tenth = tm.mk_fp(f32, RoundingMode::RNE, 0.1), one = tm.mk_fp(f32, RoundingMode::RNE, 1.0);
  s.add(fp_gt(fx, 1.0));
  s.add(fp_lt(fx, 2.0));
  s.add(fp_is_nan(fy));
  s.add(fp_add(rm, one, tenth) == fp_add(RoundingMode::RTP, one, tenth));
  s.add(rm != tm.mk_rm(RoundingMode::RTP));
  s.add(real_gt(r, tm.mk_real(1, 3)));
  s.add(real_lt(r, tm.mk_real(1, 2)));
  s.add(distinct({p, q, u}));
  s.add(b);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  const FloatValue fv = m.fp_value(fx);
  EXPECT_EQ(fv.cls, FloatValue::Class::NORMAL);
  EXPECT_GT(*fv.to_double(), 1.0);
  EXPECT_LT(*fv.to_double(), 2.0);
  EXPECT_TRUE(m.value(fx).is_value());
  EXPECT_TRUE(m.value(fx).sort() == f32);
  EXPECT_EQ(m.fp_value(fy).cls, FloatValue::Class::NOT_A_NUMBER);
  EXPECT_TRUE(m.value(fy).same_as(tm.mk_fp_nan(f32)));
  const RoundingMode mode = m.rm_value(rm);
  EXPECT_NE(mode, RoundingMode::RTP);
  EXPECT_TRUE(m.value(rm).is_value());
  EXPECT_TRUE(m.value(rm).sort().is_rm());
  EXPECT_TRUE(m.value(rm).same_as(tm.mk_rm(mode)));
  const RationalValue rv = m.real_value(r);
  EXPECT_GT(rv.to_double(), 1.0 / 3.0);
  EXPECT_LT(rv.to_double(), 0.5);
  EXPECT_TRUE(m.value(r).sort().is_real());
  EXPECT_TRUE(m.bool_value(b));
  EXPECT_TRUE(m.value(b).same_as(tm.mk_true()));
  // declared sorts: distinct elements have distinct indices and print as S!k
  const std::set<std::uint64_t> idx{m.uninterpreted_index(p), m.uninterpreted_index(q),
                                    m.uninterpreted_index(u)};
  EXPECT_EQ(idx.size(), 3u);
  EXPECT_EQ(m.value(p).to_uninterpreted_index(), m.uninterpreted_index(p));
  EXPECT_TRUE(m.value(p).is_value());
  EXPECT_TRUE(m.value(p).sort() == S);
  EXPECT_EQ(m.value(p).str().rfind("S!", 0), 0u);
  EXPECT_FALSE(m.bool_value(p == q));
  EXPECT_TRUE(m.bool_value(p == p));
  EXPECT_TRUE(m.bool_value(distinct(p, q)));
  EXPECT_TRUE(m.value(ite(p == q, x, y)).is_value());
  // the text names them the same way
  const std::string text = m.to_smt2();
  EXPECT_NE(text.find("(define-fun p () S S!"), std::string::npos);
  EXPECT_NE(text.find("(define-fun rm () RoundingMode "), std::string::npos);
  EXPECT_NE(text.find("(define-fun fx () (_ FloatingPoint 8 24) (fp "), std::string::npos);
  EXPECT_NE(text.find("(define-fun r () Real "), std::string::npos);
  EXPECT_NE(text.find("(define-fun b () Bool true)"), std::string::npos);
  // the model values re-assert consistently
  s.add(fx == m.value(fx));
  s.add(rm == m.value(rm));
  s.add(r == m.value(r));
  s.add(p == m.value(p));
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST_F(Models, terms_built_after_the_check)
{
  s.add(x == 5);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(bvmul(x, 3)), 15u);
  EXPECT_EQ(m.uint64_value(extract(3, 0, x)), 5u);
  EXPECT_EQ(m.uint64_value(zero_extend(8, x)), 5u);
  EXPECT_EQ(m.int64_value(bvneg(x)), -5);
  EXPECT_TRUE(m.bool_value(bvult(x, 6)));
  EXPECT_TRUE(m.bool_value(x == 5));
  EXPECT_FALSE(m.bool_value(x == 6));
  EXPECT_EQ(m.bv_string(x, 16), "05");
  EXPECT_EQ(m.bv_string(x, 2, false), "101");
  EXPECT_EQ(m.bv_limbs(x), std::vector<std::uint64_t>{5});
  EXPECT_EQ(m.bv_bytes(zero_extend(8, x), false), (std::vector<std::uint8_t>{0, 5}));
  // symbols declared after the check complete
  const Term late = tm.declare("late", bv8);
  EXPECT_EQ(m.uint64_value(late), 0u);
  EXPECT_EQ(m.uint64_value(x + late), 5u);
  EXPECT_FALSE(m.try_value(late).has_value());
  const Term fresh = tm.mk_fresh(f32);
  EXPECT_EQ(m.fp_value(fresh).cls, FloatValue::Class::ZERO);
  // a float expression over completed symbols
  EXPECT_EQ(*m.fp_value(fp_add(RoundingMode::RNE, fresh, 1.5)).to_double(), 1.5);
  EXPECT_EQ(m.real_value(tm.declare("late_r", R) + 2).str(), "2");
  // DOES_NOT_FIT and the sort checks on the typed readers
  const Term wide = tm.declare("wide", tm.mk_bv_sort(70));
  s.add(wide == tm.mk_bv_limbs(70, {0, 1}));
  ASSERT_TRUE(s.check_sat().is_sat());
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, s.model().uint64_value(wide));
  EXPECT_EQ(s.model().bv_limbs(wide)[1], 1u);
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().bool_value(x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().fp_value(x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().real_value(x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().rm_value(x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().uninterpreted_index(x));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, s.model().value(Term()));
  TermManager other;
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.model().value(other.mk_true()));
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.model().in_core(other.mk_true()));
}

TEST_F(Models, no_model_states)
{
  auto e = API_ERROR_OF(s.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("nothing yet"), std::string::npos);
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(x));
  s.add(x == 1);
  s.add(x == 2);
  ASSERT_TRUE(s.check_sat().is_unsat());
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  s.reset_assertions();
  api_test::add_hard_factoring(tm, s);
  ASSERT_TRUE(s.check_sat({}, CheckBudget{std::chrono::milliseconds(0), std::nullopt}).is_unknown());
  e = API_ERROR_OF(s.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("unknown"), std::string::npos);
  s.reset_assertions();
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.value(x).to_uint64(), 3u);
  EXPECT_EQ(s.model().uint64_value(x), 3u);
}

// A function over Reals is tabled from the exact model: an application the
// check saw has the solver's value, an equal argument gives the same value,
// any other completes to 0, and the printed model is well formed and names
// none of the solver's own symbols.
TEST_F(Models, functions_over_reals)
{
  const Term g = tm.declare("g", tm.mk_fun_sort({R}, R));
  const Term k = tm.declare("k", tm.mk_fun_sort({bv8}, R));
  const Term r = tm.declare("r", R);
  s.add(g(r) == tm.mk_real("-5/2"));
  s.add(g(g(r)) == tm.mk_real(9));
  s.add(r == tm.mk_real("3/4"));
  s.add(k(x) == tm.mk_real("7/2"));
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.real_value(g(r)).str(), "-5/2");
  EXPECT_TRUE(m.try_value(g(r)).has_value());
  EXPECT_EQ(m.real_value(g(tm.mk_real("3/4"))).str(), "-5/2");
  EXPECT_EQ(m.real_value(g(tm.mk_real("-5/2"))).str(), "9");
  EXPECT_EQ(m.real_value(g(tm.mk_real(1))).str(), "0");
  EXPECT_FALSE(m.try_value(g(tm.mk_real(1))).has_value());
  EXPECT_EQ(m.real_value(k(tm.mk_bv(8, 3))).str(), "7/2");
  for (const Term& a : s.assertions())
    EXPECT_TRUE(m.value(a).same_as(tm.mk_true())) << a;
  const std::string text = m.to_smt2();
  EXPECT_NE(text.find("(define-fun g ((x!0 Real)) Real (ite"), std::string::npos) << text;
  EXPECT_EQ(text.find('@'), std::string::npos) << text;
}

// A function over Reals that no assertion applies does not stop the model.
TEST_F(Models, an_unapplied_function_over_reals)
{
  tm.declare("unused", tm.mk_fun_sort({R}, R));
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 1u);
}

// A model not yet read survives a Real declaration made after the check.
TEST_F(Models, a_real_declared_after_the_check)
{
  const Term r = tm.declare("r4", R);
  s.add(r == tm.mk_real("4/3"));
  ASSERT_TRUE(s.check_sat().is_sat());
  tm.declare("later", R);
  const Model m = s.model();
  EXPECT_EQ(m.real_value(r).str(), "4/3");
  EXPECT_TRUE(m.in_core(r));
}

// Nor an assertion made after it: the model is the check's, whatever the
// assertion does to the engine's exact Real model or its function values.
TEST_F(Models, an_assertion_made_after_the_check)
{
  const Term r = tm.declare("r5", R);
  const Term f = tm.declare("f5", tm.mk_fun_sort({bv8}, bv8));
  s.add(r == tm.mk_real("5"));
  s.add(f(x) == tm.mk_bv(8, 3));
  ASSERT_TRUE(s.check_sat().is_sat());
  s.add(r == tm.mk_real("7"));
  const Model m = s.model();
  EXPECT_EQ(m.real_value(r).str(), "5");
  EXPECT_EQ(m.uint64_value(f(x)), 3u);
}

} // namespace

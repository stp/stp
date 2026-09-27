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

// api3-models.cpp -- models: detached snapshots, completion against
// try_value, the batch reader, array and function values, the core, the
// SMT-LIB text, models over every sort and the model of a term built after
// the check.

#include "api3_common.hpp"

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
  auto e = API3_ERROR_OF(s.model());
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
  // ascending by unsigned index, every entry observed and a value
  std::uint64_t last = 0;
  bool first = true;
  std::set<std::uint64_t> indices;
  for (const ArrayValue::Entry& e : av.entries())
  {
    EXPECT_TRUE(e.index.is_value());
    EXPECT_TRUE(e.element.is_value());
    EXPECT_TRUE(e.observed);
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
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, av.entry(av.size()));
  API3_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, av.at(i));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, av.at(Term()));
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
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, m.array_bytes(a, 0, 1, nullptr));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.array_bytes(x, 0, 1, out));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.array_value(x));
  const Term narrow = tm.declare("narrow", tm.mk_array_sort(bv8, tm.mk_bv_sort(12)));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(narrow, 0, 1, out));
  const Term small = tm.declare("small", tm.mk_array_sort(bv8, bv8));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, m.array_bytes(small, 250, 10, out));
  m.array_bytes(small, 250, 6, out); // [250, 256) fits
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
  EXPECT_TRUE(fv.sort() == f.sort());
  EXPECT_GE(fv.size(), 3u);
  EXPECT_EQ(fv.entries().size(), fv.size());
  for (const FunctionValue::Entry& e : fv.entries())
  {
    ASSERT_EQ(e.args.size(), 2u);
    EXPECT_TRUE(e.args[0].is_value());
    EXPECT_TRUE(e.args[1].is_value());
    EXPECT_TRUE(e.value.is_value());
    EXPECT_TRUE(e.observed);
    EXPECT_TRUE(fv.apply(e.args).same_as(e.value));
  }
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 1), tm.mk_bv(8, 2)}).to_uint64(), 3u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 2), tm.mk_bv(8, 1)}).to_uint64(), 4u);
  EXPECT_EQ(fv.apply({tm.mk_bv(8, 5), tm.mk_bv(8, 6)}).to_uint64(), 9u);
  EXPECT_TRUE(fv.else_value().is_value());
  EXPECT_TRUE(fv.else_value().sort() == bv8);
  EXPECT_TRUE(fv.apply({tm.mk_bv(8, 77), tm.mk_bv(8, 78)}).same_as(fv.else_value()));
  API3_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, fv.apply({x, y}));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, fv.apply({Term(), Term()}));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, fv.entry(fv.size()));
  // the ite form agrees with apply wherever the formals are evaluated
  const Term p = tm.declare("p", bv8), q = tm.declare("q", bv8);
  const Term body = fv.as_ite_term({p, q});
  EXPECT_TRUE(body.sort() == bv8);
  EXPECT_EQ(m.uint64_value(body.substitute({{p, tm.mk_bv(8, 1)}, {q, tm.mk_bv(8, 2)}})), 3u);
  EXPECT_EQ(m.uint64_value(body.substitute({{p, tm.mk_bv(8, 5)}, {q, tm.mk_bv(8, 6)}})), 9u);
  EXPECT_EQ(m.uint64_value(fv.as_ite_term({x, y})), 9u);
  EXPECT_EQ(m.uint64_value(fv.as_ite_term({tm.mk_bv(8, 2), tm.mk_bv(8, 1)})), 4u);
  API3_EXPECT_ERROR(ErrorCode::ARITY, fv.as_ite_term({p}));
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
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, m.function_value(x));
  // the text of the model has the function as an ite
  const std::string text = m.to_smt2();
  EXPECT_NE(text.find("(define-fun f ((x!0 (_ BitVec 8)) (x!1 (_ BitVec 8))) (_ BitVec 8)"), std::string::npos);
  EXPECT_NE(text.find("(ite (and (= x!0"), std::string::npos);
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
  API3_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, s.model().uint64_value(wide));
  EXPECT_EQ(s.model().bv_limbs(wide)[1], 1u);
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().bool_value(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().fp_value(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().real_value(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().rm_value(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.model().uninterpreted_index(x));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, s.model().value(Term()));
  TermManager other;
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.model().value(other.mk_true()));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.model().in_core(other.mk_true()));
}

TEST_F(Models, no_model_states)
{
  auto e = API3_ERROR_OF(s.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("nothing yet"), std::string::npos);
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(x));
  s.add(x == 1);
  s.add(x == 2);
  ASSERT_TRUE(s.check_sat().is_unsat());
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  s.reset_assertions();
  api3::add_hard_factoring(tm, s);
  ASSERT_TRUE(s.check_sat({}, CheckBudget{std::chrono::milliseconds(0), std::nullopt}).is_unknown());
  e = API3_ERROR_OF(s.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("unknown"), std::string::npos);
  s.reset_assertions();
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.value(x).to_uint64(), 3u);
  EXPECT_EQ(s.model().uint64_value(x), 3u);
}

} // namespace

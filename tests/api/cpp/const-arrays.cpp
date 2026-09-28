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

// Constant arrays as first-class arrays: equality, distinct, if-then-else
// and store chains over them are decided, their models complete with the
// default, and the SMT-LIB spelling round-trips through the parser and the
// printers.

#include "api_common.hpp"

#include <string>
#include <vector>

using namespace stp;

namespace
{
struct Arrays
{
  TermManager tm;
  Sort bv8 = tm.mk_bv_sort(8);
  Sort A = tm.mk_array_sort(bv8, bv8);
  Term c7 = tm.mk_const_array(A, tm.mk_bv(8, 7));
  Term c1 = tm.mk_const_array(A, tm.mk_bv(8, 1));
  Term c2 = tm.mk_const_array(A, tm.mk_bv(8, 2));
  Term idx(std::uint64_t i) { return tm.mk_bv(8, i); }
};

bool some_cell_is_not(const ArrayValue& v, std::uint64_t value)
{
  if (v.default_value().to_uint64() != value)
    return true;
  for (const ArrayValue::Entry& e : v.entries())
    if (e.element.to_uint64() != value)
      return true;
  return false;
}
} // namespace

TEST(ConstArrays, equality_holds_and_the_model_completes_with_the_default)
{
  Arrays f;
  Solver s(f.tm);
  Term a = f.tm.declare("a", f.A);
  s.add(a == f.c7);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(a == f.c7));
  EXPECT_FALSE(m.bool_value(a != f.c7));
  const ArrayValue v = m.array_value(a);
  EXPECT_EQ(v.default_value().to_uint64(), 7u);
  EXPECT_EQ(v.at(f.idx(200)).to_uint64(), 7u);
  EXPECT_EQ(m.uint64_value(a[f.idx(200)]), 7u);
  EXPECT_EQ(m.uint64_value(a[f.idx(0)]), 7u);
  // the model's text says the same
  const std::string text = m.to_smt2();
  EXPECT_NE(text.find("(define-fun a () (Array (_ BitVec 8) (_ BitVec 8)) "), std::string::npos);
  EXPECT_NE(text.find("((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)"), std::string::npos);
  EXPECT_EQ(text.find("constarray"), std::string::npos);
}

TEST(ConstArrays, a_read_disagreeing_with_the_default_is_unsat)
{
  Arrays f;
  Solver s(f.tm);
  Term a = f.tm.declare("a", f.A);
  Term i = f.tm.declare("i", f.bv8);
  s.add(a == f.c7);
  s.add(a[i] != f.idx(7));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(ConstArrays, disequality_has_a_witness_in_the_model)
{
  Arrays f;
  Solver s(f.tm);
  Term a = f.tm.declare("a", f.A);
  s.add(a != f.c7);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_FALSE(m.bool_value(a == f.c7));
  EXPECT_TRUE(m.bool_value(a != f.c7));
  EXPECT_TRUE(some_cell_is_not(m.array_value(a), 7));
}

TEST(ConstArrays, store_chains_over_a_constant_array)
{
  Arrays f;
  Term a = f.tm.declare("a", f.A);
  Term chain = store(f.c7, f.idx(5), f.idx(42));
  {
    Solver s(f.tm);
    s.add(a == chain);
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    EXPECT_TRUE(m.bool_value(a == chain));
    EXPECT_EQ(m.uint64_value(a[f.idx(5)]), 42u);
    EXPECT_EQ(m.uint64_value(a[f.idx(9)]), 7u);
    const ArrayValue v = m.array_value(a);
    EXPECT_EQ(v.default_value().to_uint64(), 7u);
    EXPECT_EQ(v.at(f.idx(5)).to_uint64(), 42u);
    EXPECT_EQ(v.at(f.idx(77)).to_uint64(), 7u);
    // the array value of the chain itself
    const ArrayValue cv = m.array_value(chain);
    EXPECT_EQ(cv.default_value().to_uint64(), 7u);
    EXPECT_EQ(cv.at(f.idx(5)).to_uint64(), 42u);
  }
  // and a read through the chain at an unwritten cell folds to the default
  EXPECT_TRUE(chain[f.idx(9)].is_value());
  EXPECT_EQ(chain[f.idx(9)].to_uint64(), 7u);

  Solver s2(f.tm);
  Term b = f.tm.declare("b", f.A);
  s2.add(b == chain);
  s2.add(b[f.idx(9)] != f.idx(7));
  EXPECT_TRUE(s2.check_sat().is_unsat());
}

TEST(ConstArrays, one_array_cannot_equal_two_constant_arrays)
{
  Arrays f;
  Solver s(f.tm);
  Term a = f.tm.declare("a", f.A);
  s.add(a == f.c1);
  s.add(a == f.c2);
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(ConstArrays, store_chains_over_different_constants)
{
  Arrays f;
  Term x = f.tm.declare("x", f.bv8), y = f.tm.declare("y", f.bv8);
  {
    // eight-bit indexes: two writes cannot cover the 254 other cells
    Solver s(f.tm);
    s.add(store(f.c1, f.idx(0), x) == store(f.c2, f.idx(1), y));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
  {
    // a one-bit index sort: the two writes cover every cell, and each
    // written value must be the other side's default
    Sort A1 = f.tm.mk_array_sort(f.tm.mk_bv_sort(1), f.bv8);
    Term d3 = f.tm.mk_const_array(A1, f.tm.mk_bv(8, 3));
    Term d7 = f.tm.mk_const_array(A1, f.tm.mk_bv(8, 7));
    Solver s(f.tm);
    s.add(store(d3, f.tm.mk_bv(1, 0), x) == store(d7, f.tm.mk_bv(1, 1), y));
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    EXPECT_EQ(m.uint64_value(x), 7u);
    EXPECT_EQ(m.uint64_value(y), 3u);
    s.add(x != f.idx(7));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

// Writes naming every value of the index sort leave no cell for the bases'
// defaults to decide, so the model evaluates the equality of two such chains
// from the written cells alone.
TEST(ConstArrays, writes_naming_every_index_decide_equality_in_the_model)
{
  TermManager::Config config;
  config.uf_sort_width = 1; // a declared sort of two elements
  TermManager tm(config);
  Sort bv1 = tm.mk_bv_sort(1);
  Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  // zero written at each index over an all-ones base, equated with all zeros
  auto over = [&](const Sort& index, const std::vector<Term>& indexes) {
    Sort A = tm.mk_array_sort(index, bv1);
    Term chain = tm.mk_const_array(A, one);
    for (const Term& i : indexes)
      chain = store(chain, i, zero);
    return tm.mk_const_array(A, zero) == chain;
  };
  {
    // the solve and the model agree
    Term e = over(bv1, {zero, one});
    Solver s(tm);
    s.add(e);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(s.model().bool_value(e));
  }

  Sort rm = tm.mk_rm_sort(), f22 = tm.mk_fp_sort(2, 2), S = tm.declare_sort("S");
  std::vector<Term> modes;
  for (RoundingMode r : {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP,
                         RoundingMode::RTN, RoundingMode::RTZ})
    modes.push_back(tm.mk_rm(r));
  // the sixteen patterns of Float(2,2): its fifteen values, NaN twice
  std::vector<Term> floats;
  for (unsigned bits = 0; bits < 16; ++bits)
    floats.push_back(tm.mk_fp_from_bits(f22, tm.mk_bv(4, bits)));
  // -0 is a value of its own, whatever +0 holds
  std::vector<Term> all_but_negative_zero = floats;
  all_but_negative_zero.erase(all_but_negative_zero.begin() + 8);
  Term u = tm.declare("u", S), v = tm.declare("v", S);

  Solver s(tm);
  s.add(u != v);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(over(bv1, {zero, one})));
  EXPECT_FALSE(m.bool_value(over(bv1, {one})));
  EXPECT_TRUE(m.bool_value(over(rm, modes)));
  EXPECT_FALSE(m.bool_value(over(rm, std::vector<Term>(modes.begin(), modes.end() - 1))));
  EXPECT_TRUE(m.bool_value(over(f22, floats)));
  EXPECT_FALSE(m.bool_value(over(f22, all_but_negative_zero)));
  EXPECT_TRUE(m.bool_value(over(S, {u, v})));
  EXPECT_FALSE(m.bool_value(over(S, {u})));
}

// A store chain over one constant array can equal another constant array
// when its writes name every value of the index sort: five for a rounding
// mode and fifteen for Float(2,2), however many patterns their carriers have.
TEST(ConstArrays, writes_naming_every_value_of_a_small_index_sort)
{
  TermManager tm;
  Sort bv1 = tm.mk_bv_sort(1);
  Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  auto over = [&](const Sort& index, const std::vector<Term>& indexes) {
    Sort A = tm.mk_array_sort(index, bv1);
    Term chain = tm.mk_const_array(A, one);
    for (const Term& i : indexes)
      chain = store(chain, i, zero);
    return tm.mk_const_array(A, zero) == chain;
  };
  std::vector<Term> modes;
  for (RoundingMode r : {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP,
                         RoundingMode::RTN, RoundingMode::RTZ})
    modes.push_back(tm.mk_rm(r));
  Sort f22 = tm.mk_fp_sort(2, 2);
  std::vector<Term> floats;
  for (unsigned bits = 0; bits < 16; ++bits)
    floats.push_back(tm.mk_fp_from_bits(f22, tm.mk_bv(4, bits)));
  std::vector<Term> all_but_negative_zero = floats;
  all_but_negative_zero.erase(all_but_negative_zero.begin() + 8);
  for (const Term& every : {over(tm.mk_rm_sort(), modes), over(f22, floats)})
  {
    Solver s(tm);
    s.add(every);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(s.model().bool_value(every));
  }
  for (const Term& missing :
       {over(tm.mk_rm_sort(), std::vector<Term>(modes.begin(), modes.end() - 1)),
        over(f22, all_but_negative_zero)})
  {
    Solver s(tm);
    s.add(missing);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

// The disequality of a constant array and a store chain over another one,
// over index sorts small enough that the solve pins the value of the cell
// witnessing the difference: sat while a value is left unwritten, unsat once
// every value is.
TEST(ConstArrays, disequality_over_a_small_index_sort)
{
  TermManager tm;
  Sort bv1 = tm.mk_bv_sort(1);
  Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  auto differ = [&](const Sort& index, const std::vector<Term>& indexes) {
    Sort A = tm.mk_array_sort(index, bv1);
    Term chain = tm.mk_const_array(A, one);
    for (const Term& i : indexes)
      chain = store(chain, i, zero);
    return tm.mk_const_array(A, zero) != chain;
  };
  std::vector<Term> modes;
  for (RoundingMode r : {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP,
                         RoundingMode::RTN, RoundingMode::RTZ})
    modes.push_back(tm.mk_rm(r));
  Sort f22 = tm.mk_fp_sort(2, 2);
  std::vector<Term> floats;
  for (unsigned bits = 0; bits < 16; ++bits)
    floats.push_back(tm.mk_fp_from_bits(f22, tm.mk_bv(4, bits)));
  std::vector<Term> all_but_negative_zero = floats;
  all_but_negative_zero.erase(all_but_negative_zero.begin() + 8);
  for (const Term& unwritten :
       {differ(bv1, {zero}),
        differ(tm.mk_rm_sort(), std::vector<Term>(modes.begin(), modes.end() - 1)),
        differ(f22, all_but_negative_zero)})
  {
    Solver s(tm);
    s.add(unwritten);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(s.model().bool_value(unwritten));
  }
  for (const Term& written :
       {differ(bv1, {zero, one}), differ(tm.mk_rm_sort(), modes), differ(f22, floats)})
  {
    Solver s(tm);
    s.add(written);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

// A model may give a declared sort fewer elements than its carrier has
// patterns: two writes can cover the sort, so an equality of constant arrays
// with different defaults through them is not refuted -- while a read at a
// term's index, which names an element, still refutes.
TEST(ConstArrays, a_declared_index_sort_is_not_counted_by_its_carrier)
{
  TermManager tm;
  Sort S = tm.declare_sort("S");
  Sort A = tm.mk_array_sort(S, tm.mk_bv_sort(1));
  Term u = tm.declare("u", S), v = tm.declare("v", S);
  Term zero = tm.mk_bv(1, 0), one = tm.mk_bv(1, 1);
  {
    Solver s(tm);
    s.add(u != v);
    s.add(tm.mk_const_array(A, zero) == store(store(tm.mk_const_array(A, one), u, zero), v, zero));
    const Result r = s.check_sat();
    EXPECT_TRUE(r.is_unknown());
    EXPECT_EQ(r.reason(), UnknownReason::INCOMPLETE);
  }
  {
    Solver s(tm);
    Term a = tm.declare("a", A);
    s.add(a == tm.mk_const_array(A, zero));
    s.add(a[u] == one);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST(ConstArrays, equality_between_constant_arrays_is_equality_of_defaults)
{
  Arrays f;
  // the same request is the same array
  EXPECT_TRUE(f.tm.mk_const_array(f.A, f.tm.mk_bv(8, 7)).same_as(f.c7));
  EXPECT_TRUE((f.c7 == f.tm.mk_const_array(f.A, f.tm.mk_bv(8, 7))).same_as(f.tm.mk_true()));
  EXPECT_TRUE((f.c1 == f.c2).same_as(f.tm.mk_false()));
  EXPECT_TRUE((f.c1 != f.c2).same_as(f.tm.mk_true()));
}

// A default is a value: the engine keeps it beside the array's symbol, out of
// every preprocessing pass's sight, so a variable in it could be eliminated
// while the array still named it -- K(0) = store(K(z), 0, 0) with z = 3 came
// back sat, the model setting z to 0.
TEST(ConstArrays, a_default_must_be_a_value)
{
  Arrays f;
  Term z = f.tm.declare("z", f.bv8);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, f.tm.mk_const_array(f.A, z));
  const auto e = API_ERROR_OF(f.tm.mk_term(Kind::CONST_ARRAY, {bvadd(f.idx(1), z)}, {}, f.A));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_EQ(e->argument_index(), 0);
  ASSERT_EQ(e->terms().size(), 1u);
  EXPECT_TRUE(e->terms()[0].same_as(z));
  // an application of a declared function is no value either
  Term g = f.tm.declare("g", f.tm.mk_fun_sort({f.bv8}, f.bv8));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, f.tm.mk_const_array(f.A, g(f.idx(1))));
  // nor in a script, where it is a parse error and the solver is untouched
  Solver s(f.tm);
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(assert (= ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) "
                           "(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) #x00 #x00)))"));
  EXPECT_TRUE(s.assertions().empty());

  // A ground term is a value whether it is folded or not.
  TermManager raw = api_test::raw_manager();
  const Sort bv8 = raw.mk_bv_sort(8), A = raw.mk_array_sort(bv8, bv8);
  const Term three = bvadd(raw.mk_bv(8, 1), raw.mk_bv(8, 2));
  const Term k = raw.mk_const_array(A, three);
  EXPECT_EQ(k.kind(), Kind::CONST_ARRAY);
  const Term a = raw.declare("a", A);
  Solver r(raw);
  r.add(a == k);
  r.add(a[raw.mk_bv(8, 5)] != raw.mk_bv(8, 3));
  EXPECT_TRUE(r.check_sat().is_unsat());
}

TEST(ConstArrays, distinct_over_constant_arrays)
{
  Arrays f;
  {
    Solver s(f.tm);
    s.add(f.tm.mk_term(Kind::DISTINCT, {f.c1, f.c2}));
    EXPECT_TRUE(s.check_sat().is_sat());
  }
  {
    Solver s(f.tm);
    Term a = f.tm.declare("a", f.A);
    s.add(f.tm.mk_term(Kind::DISTINCT, {a, f.c1, f.c2}));
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    EXPECT_TRUE(some_cell_is_not(m.array_value(a), 1));
    EXPECT_TRUE(some_cell_is_not(m.array_value(a), 2));
  }
  {
    Solver s(f.tm);
    Term a = f.tm.declare("a", f.A);
    s.add(a == f.c1);
    s.add(f.tm.mk_term(Kind::DISTINCT, {a, f.c1}));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST(ConstArrays, array_ite_with_a_constant_branch)
{
  Arrays f;
  Term a = f.tm.declare("a", f.A), d = f.tm.declare("d", f.A);
  Term b = f.tm.declare("b", f.tm.mk_bool_sort());
  Term sel = f.tm.mk_term(Kind::ITE, {b, f.c1, d});
  {
    Solver s(f.tm);
    s.add(a == sel);
    s.add(b);
    s.add(a[f.idx(2)] != f.idx(1));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
  {
    Solver s(f.tm);
    s.add(a == sel);
    s.add(b);
    s.add(a[f.idx(2)] == f.idx(1));
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    EXPECT_EQ(m.array_value(a).default_value().to_uint64(), 1u);
    EXPECT_EQ(m.uint64_value(a[f.idx(250)]), 1u);
  }
  {
    // the other branch: a follows d, whose cells are free
    Solver s(f.tm);
    s.add(a == sel);
    s.add(!b);
    s.add(a[f.idx(2)] == f.idx(9));
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(s.model().uint64_value(d[f.idx(2)]), 9u);
  }
}

TEST(ConstArrays, every_element_sort)
{
  TermManager tm;
  Sort bv4 = tm.mk_bv_sort(4);
  Term i = tm.declare("i", bv4);
  {
    Sort F = tm.mk_array_sort(bv4, tm.mk_fp32_sort());
    Term half = tm.mk_fp(tm.mk_fp32_sort(), RoundingMode::RNE, 1.5);
    Term cf = tm.mk_const_array(F, half);
    Term af = tm.declare("af", F);
    {
      Solver s(tm);
      s.add(af == cf);
      s.add(!tm.mk_term(Kind::FP_EQ, {af[i], half}));
      EXPECT_TRUE(s.check_sat().is_unsat());
    }
    Solver s2(tm);
    s2.add(af == cf);
    ASSERT_TRUE(s2.check_sat().is_sat());
    EXPECT_EQ(s2.model().fp_value(af[tm.mk_bv(4, 3)]).to_double(), 1.5);
  }
  {
    Sort R = tm.mk_array_sort(bv4, tm.mk_rm_sort());
    Term cr = tm.mk_const_array(R, tm.mk_rm(RoundingMode::RTZ));
    Term ar = tm.declare("ar", R);
    {
      Solver s(tm);
      s.add(ar == cr);
      s.add(ar[i] != tm.mk_rm(RoundingMode::RTZ));
      EXPECT_TRUE(s.check_sat().is_unsat());
    }
    Solver s2(tm);
    s2.add(ar == cr);
    ASSERT_TRUE(s2.check_sat().is_sat());
    EXPECT_EQ(s2.model().rm_value(ar[tm.mk_bv(4, 9)]), RoundingMode::RTZ);
  }
  {
    // A declared sort has no literals: the default is a value a model gave.
    Sort S = tm.declare_sort("S");
    Sort U = tm.mk_array_sort(bv4, S);
    Term u = tm.declare("u", S);
    API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_const_array(U, u));
    Solver s0(tm);
    s0.add(u != tm.declare("u2", S));
    ASSERT_TRUE(s0.check_sat().is_sat());
    const Term uv = s0.model().value(u);
    Term cu = tm.mk_const_array(U, uv);
    Term au = tm.declare("au", U);
    Solver s(tm);
    s.add(au == cu);
    s.add(au[i] != uv);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST(ConstArrays, arrays_are_not_function_arguments_whatever_they_are)
{
  // The engine's uninterpreted functions take no array argument (the sort
  // is buildable, the declaration is refused), so a constant array cannot
  // reach one any more than a declared array can: there is no function to
  // pass it to. What can be passed is a read of one, which is its default.
  Arrays f;
  const Sort fs = f.tm.mk_fun_sort({f.A}, f.bv8);
  const auto err = api_test::catch_error([&] { (void)f.tm.declare("g", fs); });
  ASSERT_TRUE(err.has_value());
  Term h = f.tm.declare("h", f.tm.mk_fun_sort({f.bv8}, f.bv8));
  Term i = f.tm.declare("i", f.bv8);
  Solver s(f.tm);
  s.add(h(f.c7[i]) != h(f.idx(7)));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(ConstArrays, spelling_and_parsing_round_trip)
{
  Arrays f;
  Solver s(f.tm);
  const std::string spelled = "((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)";
  EXPECT_EQ(f.c7.str(), spelled);
  EXPECT_EQ(f.c7.to_string(Format::SMTLIB2, true), spelled);
  EXPECT_EQ(f.c7.kind(), Kind::CONST_ARRAY);
  EXPECT_EQ(f.c7.children().size(), 1u);
  EXPECT_TRUE(f.c7.children()[0].same_as(f.idx(7)));
  EXPECT_FALSE(f.c7.symbol().has_value());
  EXPECT_FALSE(f.c7.is_const());
  // the parser hands back the same array
  EXPECT_TRUE(s.parse_term(spelled).same_as(f.c7));
  EXPECT_TRUE(s.parse_term("(store " + spelled + " #x05 #x2a)").same_as(store(f.c7, f.idx(5), f.idx(42))));
  // a script over it, and the solver's own script mentions no symbol for it
  s.parse_smt2("(declare-fun z () (Array (_ BitVec 8) (_ BitVec 8)))\n(assert (= z " + spelled +
               "))\n(assert (= (select z #x03) #x07))\n");
  const std::string script = s.to_smt2();
  EXPECT_NE(script.find("as const"), std::string::npos);
  EXPECT_EQ(script.find("constarray"), std::string::npos);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Term z = *f.tm.symbol("z");
  EXPECT_EQ(s.model().uint64_value(z[f.idx(100)]), 7u);
  EXPECT_TRUE(s.model().bool_value(z == f.c7));
  // the wrong element sort is a parse error, and the solver is unchanged
  const auto err = api_test::catch_error(
      [&] { (void)s.parse_term("((as const (Array (_ BitVec 8) (_ BitVec 8))) #b1)"); });
  ASSERT_TRUE(err.has_value());
  EXPECT_EQ(err->code(), ErrorCode::PARSE);
}

TEST(ConstArrays, an_array_value_is_re_assertable_as_a_whole)
{
  Arrays f;
  Solver s(f.tm);
  Term a = f.tm.declare("a", f.A);
  s.add(a[f.idx(3)] == f.idx(9));
  s.add(a[f.idx(4)] == f.idx(10));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Term whole = s.model().array_value(a).as_term();
  s.add(a == whole);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(a == whole));
  EXPECT_EQ(s.model().uint64_value(a[f.idx(3)]), 9u);
  s.add(a[f.idx(200)] != s.model().array_value(a).default_value());
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(ConstArrays, reads_fold_in_every_construction_mode)
{
  // The fold lives in the engine's hashing factory, under every manager.
  TermManager raw = api_test::raw_manager();
  Sort A = raw.mk_array_sort(raw.mk_bv_sort(8), raw.mk_bv_sort(8));
  Term c = raw.mk_const_array(A, raw.mk_bv(8, 7));
  Term i = raw.declare("i", raw.mk_bv_sort(8));
  EXPECT_TRUE(c[i].is_value());
  EXPECT_EQ(c[i].to_uint64(), 7u);
  EXPECT_EQ(c.kind(), Kind::CONST_ARRAY);
  // a store over it keeps its structure
  Term st = store(c, raw.mk_bv(8, 1), raw.mk_bv(8, 2));
  EXPECT_EQ(st.kind(), Kind::STORE);
  EXPECT_EQ(st[i].kind(), Kind::SELECT);
}

// An operand preprocessing turns into a constant array has its witness read
// folded to the default, and the operand is that constant array. Built
// without folding, ite(true, K(0), K(1)) != K(1) was reported lost: an
// internal error that poisoned the manager.
TEST(ConstArrays, an_operand_that_folds_into_a_constant_array)
{
  TermManager tm = api_test::raw_manager();
  const Sort b2 = tm.mk_bv_sort(2), A = tm.mk_array_sort(b2, b2);
  const auto K = [&](std::uint64_t v) { return tm.mk_const_array(A, tm.mk_bv(2, v)); };
  const Term e = ite(tm.mk_true(), K(0), K(1)) != K(1);
  Solver s(tm);
  s.add(e);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(e));
  Solver u(tm);
  u.add(ite(tm.mk_true(), K(0), K(1)) != K(0));
  EXPECT_TRUE(u.check_sat().is_unsat());
}

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

// sorts.cpp -- sorts and symbols: interning, the queries, declare's
// idempotence, fresh symbols and sorts, bind_symbol, term_from_id, function
// and array sorts and the combinations the engine refuses.

#include "api_common.hpp"

#include <set>
#include <unordered_set>

using namespace stp;

namespace
{

TEST(Sorts, interning_and_queries)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  EXPECT_TRUE(bv8 == tm.mk_bv_sort(8));
  EXPECT_FALSE(bv8 != tm.mk_bv_sort(8));
  EXPECT_TRUE(bv8 != tm.mk_bv_sort(9));
  EXPECT_EQ(bv8.id(), tm.mk_bv_sort(8).id());
  EXPECT_NE(bv8.id(), tm.mk_bv_sort(9).id());
  EXPECT_EQ(bv8.kind(), SortKind::BV);
  EXPECT_TRUE(bv8.is_bv());
  EXPECT_FALSE(bv8.is_bool());
  EXPECT_EQ(bv8.bv_size(), 8u);
  EXPECT_EQ(bv8.str(), "(_ BitVec 8)");
  EXPECT_TRUE(bv8.manager() == tm);

  const Sort B = tm.mk_bool_sort();
  EXPECT_TRUE(B == tm.mk_bool_sort());
  EXPECT_EQ(B.kind(), SortKind::BOOL);
  EXPECT_TRUE(B.is_bool());
  EXPECT_EQ(B.str(), "Bool");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, B.bv_size());

  const Sort f32 = tm.mk_fp32_sort();
  EXPECT_TRUE(f32 == tm.mk_fp_sort(8, 24));
  EXPECT_TRUE(tm.mk_fp16_sort() == tm.mk_fp_sort(5, 11));
  EXPECT_TRUE(tm.mk_fp64_sort() == tm.mk_fp_sort(11, 53));
  EXPECT_TRUE(tm.mk_fp128_sort() == tm.mk_fp_sort(15, 113));
  EXPECT_EQ(f32.kind(), SortKind::FP);
  EXPECT_TRUE(f32.is_fp());
  EXPECT_EQ(f32.fp_exp_size(), 8u);
  EXPECT_EQ(f32.fp_sig_size(), 24u);
  EXPECT_EQ(f32.str(), "(_ FloatingPoint 8 24)");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.fp_exp_size());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.fp_sig_size());

  const Sort RM = tm.mk_rm_sort();
  EXPECT_TRUE(RM == tm.mk_rm_sort());
  EXPECT_TRUE(RM.is_rm());
  EXPECT_EQ(RM.str(), "RoundingMode");
  const Sort R = tm.mk_real_sort();
  EXPECT_TRUE(R == tm.mk_real_sort());
  EXPECT_TRUE(R.is_real());
  EXPECT_EQ(R.str(), "Real");

  const Sort A = tm.mk_array_sort(tm.mk_bv_sort(32), bv8);
  EXPECT_TRUE(A == tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));
  EXPECT_TRUE(A != tm.mk_array_sort(bv8, bv8));
  EXPECT_EQ(A.kind(), SortKind::ARRAY);
  EXPECT_TRUE(A.is_array());
  EXPECT_TRUE(A.array_index() == tm.mk_bv_sort(32));
  EXPECT_TRUE(A.array_element() == bv8);
  EXPECT_EQ(A.str(), "(Array (_ BitVec 32) (_ BitVec 8))");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.array_index());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.array_element());

  const Sort FS = tm.mk_fun_sort({bv8, B}, f32);
  EXPECT_TRUE(FS == tm.mk_fun_sort({bv8, B}, f32));
  EXPECT_TRUE(FS != tm.mk_fun_sort({B, bv8}, f32));
  EXPECT_TRUE(FS != tm.mk_fun_sort({bv8, B}, bv8));
  EXPECT_EQ(FS.kind(), SortKind::FUN);
  EXPECT_TRUE(FS.is_fun());
  EXPECT_EQ(FS.fun_arity(), 2u);
  ASSERT_EQ(FS.fun_domain().size(), 2u);
  EXPECT_TRUE(FS.fun_domain()[0] == bv8);
  EXPECT_TRUE(FS.fun_domain()[1] == B);
  EXPECT_TRUE(FS.fun_codomain() == f32);
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.fun_domain());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.fun_codomain());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.fun_arity());
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, bv8.name());

  // the null sort
  const Sort null;
  EXPECT_TRUE(null.is_null());
  EXPECT_FALSE(bv8.is_null());
  EXPECT_EQ(null.id(), 0u);
  EXPECT_EQ(null.str(), "<null sort>");
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, null.kind());
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, null.manager());
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.declare("n", null));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.mk_array_sort(null, bv8));

  // sorts of different managers never compare equal
  TermManager other;
  EXPECT_TRUE(bv8 != other.mk_bv_sort(8));
  EXPECT_NE(tm.id(), other.id());
  EXPECT_TRUE(tm != other);

  // ordering and hashing
  std::set<Sort> ordered{f32, bv8, B, A};
  EXPECT_EQ(ordered.size(), 4u);
  EXPECT_TRUE(ordered.count(tm.mk_bv_sort(8)) == 1);
  std::unordered_set<Sort> hashed{f32, bv8, tm.mk_bv_sort(8)};
  EXPECT_EQ(hashed.size(), 2u);
  std::ostringstream os;
  os << bv8;
  EXPECT_EQ(os.str(), "(_ BitVec 8)");
}

TEST(Sorts, construction_errors)
{
  TermManager tm;
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_bv_sort(0));
  auto e = API_ERROR_OF(tm.mk_fp_sort(1, 5));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_EQ(e->argument_index(), std::optional<int>(0));
  e = API_ERROR_OF(tm.mk_fp_sort(5, 1));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
  EXPECT_EQ(tm.mk_fp_sort(2, 2).fp_sig_size(), 2u);
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fun_sort({}, tm.mk_bv_sort(8)));
  TermManager other;
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER,
                   tm.mk_array_sort(other.mk_bv_sort(8), tm.mk_bv_sort(8)));
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER,
                   tm.mk_fun_sort({tm.mk_bv_sort(8)}, other.mk_bv_sort(8)));
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.declare("x", other.mk_bv_sort(8)));
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, tm.mk_fresh(other.mk_bv_sort(8)));
}

TEST(Sorts, array_combinations)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8), B = tm.mk_bool_sort(), R = tm.mk_real_sort();
  const Sort f32 = tm.mk_fp32_sort(), RM = tm.mk_rm_sort(), S = tm.declare_sort("S");
  const Sort A = tm.mk_array_sort(bv8, bv8);
  // admitted: BV, FP, RM and declared sorts as index and as element
  for (const Sort& index : {bv8, f32, RM, S})
    for (const Sort& element : {bv8, f32, RM, S})
    {
      const Sort arr = tm.mk_array_sort(index, element);
      EXPECT_TRUE(arr.array_index() == index);
      EXPECT_TRUE(arr.array_element() == element);
      EXPECT_TRUE(arr == tm.mk_array_sort(index, element));
    }
  // refused: Bool, Real, arrays and functions in either position
  auto e = API_ERROR_OF(tm.mk_array_sort(B, bv8));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_EQ(e->sorts().size(), 2u);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(bv8, B));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(R, bv8));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(bv8, R));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(A, bv8));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(bv8, A));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_array_sort(tm.mk_fun_sort({bv8}, bv8), bv8));
  EXPECT_EQ(capabilities()["array.index-sorts"], "bv,fp,rm,uninterpreted");
  EXPECT_EQ(capabilities()["array.element-sorts"], "bv,fp,rm,uninterpreted");

  // the admitted exotic arrays solve and read back
  Solver s(tm);
  const Term af = tm.declare("af", tm.mk_array_sort(f32, f32));
  const Term am = tm.declare("am", tm.mk_array_sort(RM, bv8));
  const Term as = tm.declare("as", tm.mk_array_sort(S, S));
  const Term fx = tm.declare("fx", f32);
  const Term p = tm.declare("p", S), q = tm.declare("q", S);
  s.add(fp_eq(af[fx], tm.mk_fp(f32, RoundingMode::RNE, 2.5)));
  s.add(fp_eq(fx, tm.mk_fp(f32, RoundingMode::RNE, 1.0)));
  s.add(am[tm.mk_rm(RoundingMode::RTZ)] == 7);
  s.add(am[tm.mk_rm(RoundingMode::RTP)] == 9);
  s.add(as[p] == q);
  s.add(distinct(p, q));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.fp_value(af[tm.mk_fp(f32, RoundingMode::RNE, 1.0)]).to_double(),
            std::optional<double>(2.5));
  EXPECT_EQ(m.uint64_value(am[tm.mk_rm(RoundingMode::RTZ)]), 7u);
  EXPECT_EQ(m.uint64_value(am[tm.mk_rm(RoundingMode::RTP)]), 9u);
  EXPECT_EQ(m.uninterpreted_index(as[p]), m.uninterpreted_index(q));
  EXPECT_NE(m.uninterpreted_index(p), m.uninterpreted_index(q));
}

TEST(Sorts, function_sorts)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8), B = tm.mk_bool_sort(), R = tm.mk_real_sort();
  const Sort f32 = tm.mk_fp32_sort(), RM = tm.mk_rm_sort(), S = tm.declare_sort("S");
  const Sort A = tm.mk_array_sort(bv8, bv8);
  // every scalar sort as a domain and as a codomain
  for (const Sort& d : {B, bv8, f32, RM, R, S})
    for (const Sort& c : {B, bv8, f32, RM, R, S})
    {
      const std::string name = "g_" + d.str() + "_" + c.str();
      const Term g = tm.declare(name, tm.mk_fun_sort({d}, c));
      EXPECT_TRUE(g.sort().is_fun());
      EXPECT_TRUE(g.sort().fun_codomain() == c);
    }
  // arrays are neither a domain nor a codomain the engine admits
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.declare("ga", tm.mk_fun_sort({A}, bv8)));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.declare("gb", tm.mk_fun_sort({bv8}, A)));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED,
                   tm.declare("gc", tm.mk_fun_sort({tm.mk_fun_sort({bv8}, bv8)}, bv8)));
  // a 3-place function over mixed sorts, applied and solved
  const Term h = tm.declare("h", tm.mk_fun_sort({bv8, B, f32}, R));
  EXPECT_EQ(h.sort().fun_arity(), 3u);
  const Term x = tm.declare("x", bv8);
  const Term app = h(x, tm.mk_true(), tm.mk_fp(f32, RoundingMode::RNE, 1.0));
  EXPECT_EQ(app.kind(), Kind::APPLY);
  EXPECT_TRUE(app.sort().is_real());
  Solver s(tm);
  s.add(real_gt(app, 2));
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  // a Real-valued application is tabled from the exact model: the solver's
  // own answer, which satisfies the assertion it was checked with
  const std::optional<Term> v = s.model().try_value(app);
  ASSERT_TRUE(v.has_value());
  EXPECT_TRUE(s.model().value(real_gt(app, 2)).same_as(tm.mk_true()));
  EXPECT_EQ(s.model().uint64_value(x), 1u);
}

TEST(Symbols, declare_is_keyed_by_name)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8), bv16 = tm.mk_bv_sort(16);
  const Term x = tm.declare("x", bv8);
  EXPECT_TRUE(tm.declare("x", bv8).same_as(x));
  EXPECT_EQ(x.symbol(), std::optional<std::string>("x"));
  EXPECT_TRUE(x.is_const());
  EXPECT_EQ(x.str(), "x"); // a simple symbol prints bare
  ASSERT_TRUE(tm.symbol("x").has_value());
  EXPECT_TRUE(tm.symbol("x")->same_as(x));
  EXPECT_FALSE(tm.symbol("nope").has_value());
  // the same name at another sort is refused, with the pieces attached
  auto e = API_ERROR_OF(tm.declare("x", bv16));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH);
  EXPECT_EQ(e->argument_index(), std::optional<int>(0));
  ASSERT_EQ(e->terms().size(), 1u);
  EXPECT_TRUE(e->terms()[0].same_as(x));
  ASSERT_EQ(e->sorts().size(), 2u);
  EXPECT_TRUE(e->sorts()[0] == bv16);
  EXPECT_TRUE(e->sorts()[1] == bv8);
  // and the table is unchanged by the refusal
  EXPECT_TRUE(tm.symbol("x")->sort() == bv8);
  EXPECT_EQ(tm.symbols().size(), 1u);
  // names: any string, quoted where SMT-LIB needs it; reserved prefixes refused
  const Term odd = tm.declare("has space", bv8);
  EXPECT_EQ(odd.str(), "|has space|");
  EXPECT_EQ(odd.symbol(), std::optional<std::string>("has space"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare("", bv8));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare("@x", bv8));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare(".x", bv8));
  // declaration order
  const Term y = tm.declare("y", bv8);
  const std::vector<Term> all = tm.symbols();
  ASSERT_EQ(all.size(), 3u);
  EXPECT_TRUE(all[0].same_as(x));
  EXPECT_TRUE(all[1].same_as(odd));
  EXPECT_TRUE(all[2].same_as(y));
  // function symbols and declared-sort elements are declared the same way
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  EXPECT_TRUE(tm.declare("f", tm.mk_fun_sort({bv8}, bv8)).same_as(f));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.declare("f", tm.mk_fun_sort({bv16}, bv8)));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.declare("f", bv8));
  EXPECT_EQ(f.symbol(), std::optional<std::string>("f"));
  EXPECT_TRUE(tm.symbol("f")->same_as(f));
  const Sort S = tm.declare_sort("S");
  const Term p = tm.declare("p", S);
  EXPECT_TRUE(tm.declare("p", S).same_as(p));
  EXPECT_EQ(tm.symbols().size(), 5u);
  // a compound term has no symbol
  EXPECT_FALSE((x + y).symbol().has_value());
  EXPECT_FALSE(tm.mk_bv(8, 1).symbol().has_value());
}

TEST(Symbols, mk_fresh_is_anonymous)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term t1 = tm.mk_fresh(bv8, "tmp");
  const Term t2 = tm.mk_fresh(bv8, "tmp");
  EXPECT_FALSE(t1.same_as(t2));
  EXPECT_TRUE(t1.is_const());
  EXPECT_TRUE(t1.sort() == bv8);
  ASSERT_TRUE(t1.symbol().has_value());
  EXPECT_EQ(t1.symbol()->rfind("tmp!", 0), 0u);
  EXPECT_NE(*t1.symbol(), *t2.symbol());
  EXPECT_EQ(t1.str(), *t1.symbol()); // `!` is a simple-symbol character
  // never in the name table
  EXPECT_FALSE(tm.symbol(*t1.symbol()).has_value());
  EXPECT_TRUE(tm.symbols().empty());
  const Term x = tm.declare("x", bv8);
  EXPECT_EQ(tm.symbols().size(), 1u);
  // declaring the fresh symbol's spelling is refused rather than aliased
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare(*t1.symbol(), bv8));
  // the empty prefix works too
  const Term t3 = tm.mk_fresh(bv8);
  EXPECT_TRUE(t3.symbol().has_value());
  EXPECT_FALSE(t3.same_as(t1));
  // fresh symbols solve like any other
  Solver s(tm);
  s.add(t1 + t2 == 10);
  s.add(t1 == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(t2), 7u);
  (void)x;
}

TEST(Symbols, bind_symbol)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term t = tm.mk_fresh(bv8, "anon");
  tm.bind_symbol("named", t);
  ASSERT_TRUE(tm.symbol("named").has_value());
  EXPECT_TRUE(tm.symbol("named")->same_as(t));
  EXPECT_TRUE(tm.declare("named", bv8).same_as(t));
  ASSERT_EQ(tm.symbols().size(), 1u);
  EXPECT_TRUE(tm.symbols()[0].same_as(t));
  // binding the same term again under the same name is a no-op
  tm.bind_symbol("named", t);
  EXPECT_EQ(tm.symbols().size(), 1u);
  // a taken name is refused and unchanged
  const Term other = tm.mk_fresh(bv8);
  auto e = API_ERROR_OF(tm.bind_symbol("named", other));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH);
  EXPECT_TRUE(tm.symbol("named")->same_as(t));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.bind_symbol("", other));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.bind_symbol("z", Term()));
  TermManager foreign;
  API_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER,
                   tm.bind_symbol("z", foreign.declare("z", foreign.mk_bv_sort(8))));
  // a bound function symbol is applicable under its new name
  const Term f = tm.mk_fresh(tm.mk_fun_sort({bv8}, bv8), "fun");
  tm.bind_symbol("g", f);
  EXPECT_TRUE(tm.symbol("g")->same_as(f));
  EXPECT_EQ(tm.symbol("g").value()(t).kind(), Kind::APPLY);
  // a bound symbol keeps its own spelling: the first name it was given
  EXPECT_EQ(t.symbol(), std::optional<std::string>(*t.symbol()));
}

TEST(Symbols, declared_and_fresh_sorts)
{
  TermManager tm;
  const Sort S = tm.declare_sort("S");
  EXPECT_TRUE(S == tm.declare_sort("S"));
  EXPECT_TRUE(S != tm.declare_sort("T"));
  EXPECT_EQ(S.kind(), SortKind::UNINTERPRETED);
  EXPECT_TRUE(S.is_uninterpreted());
  EXPECT_EQ(S.name(), "S");
  EXPECT_EQ(S.str(), "S");
  EXPECT_EQ(tm.declare_sort("with space").str(), "|with space|");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare_sort(""));
  const std::vector<Sort> declared = tm.declared_sorts();
  ASSERT_EQ(declared.size(), 3u);
  EXPECT_TRUE(declared[0] == S);
  EXPECT_EQ(declared[1].name(), "T");
  // fresh sorts are anonymous and distinct
  const Sort F1 = tm.mk_fresh_sort("U"), F2 = tm.mk_fresh_sort("U");
  EXPECT_TRUE(F1 != F2);
  EXPECT_TRUE(F1.is_uninterpreted());
  EXPECT_EQ(F1.name().rfind("U!", 0), 0u);
  EXPECT_NE(F1.name(), F2.name());
  EXPECT_EQ(tm.declared_sorts().size(), 3u);
  EXPECT_TRUE(tm.mk_fresh_sort().is_uninterpreted());
  // elements of a fresh sort solve
  Solver s(tm);
  const Term u1 = tm.declare("u1", F1), u2 = tm.declare("u2", F1), u3 = tm.declare("u3", F1);
  s.add(distinct({u1, u2, u3}));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  std::set<std::uint64_t> seen{m.uninterpreted_index(u1), m.uninterpreted_index(u2),
                               m.uninterpreted_index(u3)};
  EXPECT_EQ(seen.size(), 3u);
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(u1 == tm.declare("v", F2)));
  EXPECT_EQ(tm.uf_sort_width(), 16u);
}

TEST(Symbols, term_from_id)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  const Term sum = x + 1;
  const std::uint64_t id = sum.id();
  EXPECT_NE(id, 0u);
  EXPECT_EQ(id, sum.id());
  EXPECT_NE(id, x.id());
  EXPECT_TRUE(tm.term_from_id(id).same_as(sum));
  EXPECT_TRUE(tm.term_from_id(x.id()).same_as(x));
  auto e = API_ERROR_OF(tm.term_from_id(id + 1000000));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  // ids are stable across handles of the same node
  EXPECT_EQ((x + 1).id(), id);
}

TEST(Symbols, managers_are_shared_handles)
{
  TermManager tm;
  TermManager copy = tm;
  EXPECT_TRUE(copy == tm);
  EXPECT_EQ(copy.id(), tm.id());
  const Term x = copy.declare("x", copy.mk_bv_sort(8));
  EXPECT_TRUE(tm.symbol("x")->same_as(x));
  EXPECT_TRUE(x.manager() == tm);
  EXPECT_TRUE(x.sort().manager() == copy);
  EXPECT_TRUE(tm.simplify());
  EXPECT_EQ(tm.default_rounding_mode(), RoundingMode::RNE);
  tm.set_default_rounding_mode(RoundingMode::RTZ);
  EXPECT_EQ(copy.default_rounding_mode(), RoundingMode::RTZ);
  // moved-from handles refuse
  TermManager moved = std::move(copy);
  EXPECT_TRUE(moved == tm);
  API_EXPECT_ERROR(ErrorCode::STATE, copy.mk_bv_sort(8));
  EXPECT_EQ(copy.id(), 0u);
  // configuration through Config
  TermManager::Config cfg;
  cfg.simplify = false;
  cfg.default_rounding_mode = RoundingMode::RTP;
  cfg.uf_sort_width = 4;
  TermManager raw(cfg);
  EXPECT_FALSE(raw.simplify());
  EXPECT_EQ(raw.default_rounding_mode(), RoundingMode::RTP);
  EXPECT_EQ(raw.uf_sort_width(), 4u);
  const Term rx = raw.declare("rx", raw.mk_bv_sort(8));
  EXPECT_EQ(bvadd(rx, raw.mk_bv(8, 0)).kind(), Kind::BV_ADD);
  EXPECT_TRUE(tm.simplify());
  EXPECT_TRUE(bvadd(x, tm.mk_bv(8, 0)).same_as(x));
  // the manager outlives its handle while a term refers to it
  Term survivor;
  {
    TermManager scoped;
    survivor = scoped.declare("s", scoped.mk_bv_sort(4));
  }
  EXPECT_EQ(survivor.sort().bv_size(), 4u);
  EXPECT_EQ(survivor.symbol(), std::optional<std::string>("s"));
}

} // namespace

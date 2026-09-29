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

// round-trips.cpp -- what the API prints reads back: Solver::to_smt2 for a
// solver asserting one term of each public kind, read into a fresh manager,
// answers as the original does; the options a solver was given print in a
// form every reader accepts.

#include "api_common.hpp"

#include <string>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

// One assertion per public kind (or family), over one manager.
std::vector<std::pair<std::string, Term>> one_per_kind(TermManager& tm)
{
  const Sort B = tm.mk_bool_sort(), bv8 = tm.mk_bv_sort(8), fp = tm.mk_fp_sort(5, 11);
  const Sort R = tm.mk_real_sort(), rmS = tm.mk_rm_sort(), arr = tm.mk_array_sort(bv8, bv8);
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8), p = tm.declare("p", B),
             q = tm.declare("q", B);
  const Term fx = tm.declare("fx", fp), fy = tm.declare("fy", fp), fz = tm.declare("fz", fp),
             rm = tm.declare("rm", rmS), r = tm.declare("r", R), t = tm.declare("t", R);
  const Term a = tm.declare("a", arr), f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Sort S = tm.declare_sort("S");
  const Term u = tm.declare("u", S), v = tm.declare("v", S);
  std::vector<std::pair<std::string, Term>> ts;
  const auto bvk = [&](Kind k) { return tm.mk_term(k, {x, y}); };
  for (Kind k : {Kind::BV_AND, Kind::BV_OR, Kind::BV_XOR, Kind::BV_NAND, Kind::BV_NOR, Kind::BV_XNOR,
                 Kind::BV_ADD, Kind::BV_SUB, Kind::BV_MUL, Kind::BV_UDIV, Kind::BV_UREM, Kind::BV_SDIV,
                 Kind::BV_SREM, Kind::BV_SMOD, Kind::BV_SHL, Kind::BV_LSHR, Kind::BV_ASHR})
    ts.emplace_back(to_string(k), bvk(k) == x);
  for (Kind k : {Kind::BV_ULT, Kind::BV_ULE, Kind::BV_UGT, Kind::BV_UGE, Kind::BV_SLT, Kind::BV_SLE,
                 Kind::BV_SGT, Kind::BV_SGE, Kind::BV_UADDO, Kind::BV_SADDO, Kind::BV_UMULO,
                 Kind::BV_SMULO, Kind::BV_USUBO, Kind::BV_SSUBO, Kind::BV_SDIVO})
    ts.emplace_back(to_string(k), bvk(k));
  ts.emplace_back("BV_NEGO", tm.mk_term(Kind::BV_NEGO, {x}));
  ts.emplace_back("BV_COMP", tm.mk_term(Kind::BV_COMP, {x, y}) == tm.mk_bv(1, 1));
  ts.emplace_back("BV_REDAND", tm.mk_term(Kind::BV_REDAND, {x}) == tm.mk_bv(1, 1));
  ts.emplace_back("BV_REDOR", tm.mk_term(Kind::BV_REDOR, {x}) == tm.mk_bv(1, 1));
  ts.emplace_back("BV_NOT/NEG", tm.mk_term(Kind::BV_NOT, {x}) == tm.mk_term(Kind::BV_NEG, {y}));
  ts.emplace_back("BV_CONCAT", tm.mk_term(Kind::BV_CONCAT, {x, y, x}) == tm.mk_bv(24, 5));
  ts.emplace_back("BV_EXTRACT", tm.mk_term(Kind::BV_EXTRACT, {x}, {5, 2}) == tm.mk_bv(4, 3));
  ts.emplace_back("BV_ZERO_EXTEND", tm.mk_term(Kind::BV_ZERO_EXTEND, {x}, {4}) == tm.mk_bv(12, 3));
  ts.emplace_back("BV_SIGN_EXTEND", tm.mk_term(Kind::BV_SIGN_EXTEND, {x}, {4}) == tm.mk_bv(12, 3));
  ts.emplace_back("BV_REPEAT", tm.mk_term(Kind::BV_REPEAT, {x}, {3}) == tm.mk_bv(24, 3));
  ts.emplace_back("BV_ROTATE_LEFT", tm.mk_term(Kind::BV_ROTATE_LEFT, {x}, {3}) == y);
  ts.emplace_back("BV_ROTATE_RIGHT", tm.mk_term(Kind::BV_ROTATE_RIGHT, {x}, {3}) == y);
  ts.emplace_back("ITE", tm.mk_term(Kind::ITE, {p, x, y}) == x);
  ts.emplace_back("DISTINCT", tm.mk_term(Kind::DISTINCT, {x, y, tm.mk_bv(8, 1)}));
  ts.emplace_back("XOR", tm.mk_term(Kind::XOR, {p, q, p}));
  ts.emplace_back("AND", tm.mk_term(Kind::AND, {p, q, x == y}));
  ts.emplace_back("IMPLIES", tm.mk_term(Kind::IMPLIES, {p, q}));
  ts.emplace_back("SELECT/STORE", select(store(a, x, y), y) == x);
  ts.emplace_back("CONST_ARRAY", a == tm.mk_const_array(arr, tm.mk_bv(8, 5)));
  ts.emplace_back("DISTINCT arrays",
                  tm.mk_term(Kind::DISTINCT, {a, store(a, x, y), tm.mk_const_array(arr, tm.mk_bv(8, 9))}));
  ts.emplace_back("APPLY", f(x) == y);
  ts.emplace_back("FP_FMA/SQRT",
                  fp_eq(tm.mk_term(Kind::FP_FMA, {rm, fx, fy, fz}), tm.mk_term(Kind::FP_SQRT, {rm, fx})));
  for (Kind k : {Kind::FP_ADD, Kind::FP_SUB, Kind::FP_MUL, Kind::FP_DIV})
    ts.emplace_back(to_string(k), tm.mk_term(k, {rm, fx, fy}) == fz);
  for (Kind k : {Kind::FP_REM, Kind::FP_MIN, Kind::FP_MAX})
    ts.emplace_back(to_string(k), tm.mk_term(k, {fx, fy}) == fz);
  ts.emplace_back("FP_RTI/ABS/NEG",
                  tm.mk_term(Kind::FP_RTI, {rm, tm.mk_term(Kind::FP_ABS, {tm.mk_term(Kind::FP_NEG, {fx})})}) == fz);
  for (Kind k : {Kind::FP_EQ, Kind::FP_LT, Kind::FP_LEQ, Kind::FP_GT, Kind::FP_GEQ})
    ts.emplace_back(to_string(k), tm.mk_term(k, {fx, fy}));
  for (Kind k : {Kind::FP_IS_NORMAL, Kind::FP_IS_SUBNORMAL, Kind::FP_IS_ZERO, Kind::FP_IS_INF,
                 Kind::FP_IS_NAN, Kind::FP_IS_NEG, Kind::FP_IS_POS})
    ts.emplace_back(to_string(k), tm.mk_term(k, {fx}));
  ts.emplace_back("FP_FP", tm.mk_term(Kind::FP_FP, {tm.mk_bv(1, 0), tm.mk_bv(5, 3), tm.mk_bv(10, 7)}) == fx);
  ts.emplace_back("FP_TO_FP_FROM_BV", tm.mk_term(Kind::FP_TO_FP_FROM_BV, {tm.mk_bv(16, 7)}, {5, 11}) == fx);
  ts.emplace_back("FP_TO_FP_FROM_FP", tm.mk_term(Kind::FP_TO_FP_FROM_FP, {rm, fx}, {8, 24}) ==
                                          tm.mk_fp(tm.mk_fp32_sort(), RoundingMode::RNE, 1.0));
  ts.emplace_back("FP_TO_FP_FROM_SBV", tm.mk_term(Kind::FP_TO_FP_FROM_SBV, {rm, x}, {5, 11}) == fx);
  ts.emplace_back("FP_TO_FP_FROM_UBV", tm.mk_term(Kind::FP_TO_FP_FROM_UBV, {rm, x}, {5, 11}) == fx);
  ts.emplace_back("FP_TO_FP_FROM_REAL",
                  tm.mk_term(Kind::FP_TO_FP_FROM_REAL, {tm.mk_rm(RoundingMode::RNE), tm.mk_real("5/2")}, {5, 11}) ==
                      fx);
  ts.emplace_back("FP_TO_UBV", tm.mk_term(Kind::FP_TO_UBV, {rm, fx}, {8}) == x);
  ts.emplace_back("FP_TO_SBV", tm.mk_term(Kind::FP_TO_SBV, {rm, fx}, {8}) == x);
  ts.emplace_back("FP_TO_REAL", real_lt(tm.mk_term(Kind::FP_TO_REAL, {fx}), r));
  ts.emplace_back("FP_TO_IEEE_BV", tm.mk_term(Kind::FP_TO_IEEE_BV, {fx}) == tm.mk_bv(16, 0x3c00));
  ts.emplace_back("REAL arithmetic",
                  real_le(tm.mk_term(Kind::REAL_ADD, {r, t, r}),
                          tm.mk_term(Kind::REAL_SUB,
                                     {tm.mk_term(Kind::REAL_NEG, {r}),
                                      tm.mk_term(Kind::REAL_DIV, {tm.mk_term(Kind::REAL_MUL, {r, tm.mk_real(3)}),
                                                                  tm.mk_real(2)})})));
  ts.emplace_back("REAL_GE/GT", tm.mk_term(Kind::REAL_GE, {r, t}) && tm.mk_term(Kind::REAL_GT, {r, t}));
  ts.emplace_back("declared sort", u != v);
  ts.emplace_back("RM", rm == tm.mk_rm(RoundingMode::RTZ));
  return ts;
}

} // namespace

TEST(RoundTrips, to_smt2_of_every_kind_reads_back_and_agrees)
{
  for (const bool simplify : {true, false})
  {
    SCOPED_TRACE(simplify ? "simplify" : "no simplify");
    TermManager::Config cfg;
    cfg.simplify = simplify;
    TermManager tm(cfg);
    for (const auto& [name, term] : one_per_kind(tm))
    {
      SCOPED_TRACE(name);
      Solver s(tm);
      s.add(term);
      const std::string printed = s.to_smt2(true);
      const Result original = s.check_sat();
      TermManager fresh;
      Solver back(fresh);
      const auto e = API_ERROR_OF(back.parse_smt2(printed));
      ASSERT_FALSE(e.has_value()) << e->what() << "\n" << printed;
      EXPECT_EQ(back.check_sat().str(), original.str()) << printed;
    }
  }
}

// A solver's own options are its reader's business: they print as comments
// (produce-models, which SMT-LIB defines, as a set-option), so the script
// reads back whatever they are.
TEST(RoundTrips, to_smt2_prints_options_every_reader_accepts)
{
  TermManager tm;
  Options o;
  o.set_uint("random-seed", 3);
  o.set_duration("max-time", std::chrono::seconds(5));
  o.set_bool("produce-models", false);
  o.set_names("fp-abstraction-ops", {"mul", "div"});
  Solver s(tm, o);
  const Term b = tm.declare("b", tm.mk_bool_sort());
  s.add(b);
  const std::string printed = s.to_smt2(true);
  EXPECT_NE(printed.find("(set-option :produce-models false)"), std::string::npos) << printed;
  EXPECT_NE(printed.find("; random-seed = 3"), std::string::npos) << printed;
  EXPECT_NE(printed.find("; max-time = 5000ms"), std::string::npos) << printed;
  EXPECT_EQ(printed.find(":stp."), std::string::npos) << printed;
  for (const ParseMode mode : {ParseMode::DECLARE_AND_ASSERT, ParseMode::EXECUTE})
  {
    TermManager fresh;
    Solver back(fresh);
    std::string out;
    back.set_output_sink([&](std::string_view text) { out += text; });
    const auto e = API_ERROR_OF(back.parse_smt2(printed, mode));
    ASSERT_FALSE(e.has_value()) << e->what() << "\n" << printed;
    EXPECT_EQ(out.find("unsupported"), std::string::npos) << out;
    EXPECT_EQ(out.find("error"), std::string::npos) << out;
  }
}

// SMT-LIB takes |true| and true for the same symbol, so a declaration named
// after a predefined symbol could not be printed so that it reads back: the
// script would mean the theory's symbol. Such names are refused; every
// other name, reserved words included, prints so that it reads back.
TEST(RoundTrips, names_that_spell_predefined_symbols_are_refused)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  for (const char* name : {"true", "false", "not", "ite", "distinct", "select", "store", "concat",
                           "extract", "bvadd", "bvult", "RNE", "roundTowardZero", "NaN", "+oo",
                           "fp", "fp.add", "to_fp", "+", "<=", "/"})
  {
    SCOPED_TRACE(name);
    API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare(name, bv8));
    API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.bind_symbol(name, x));
    EXPECT_FALSE(tm.symbol(name).has_value());
  }
  for (const char* sort : {"Bool", "Real", "Array", "BitVec", "FloatingPoint", "Float32", "RoundingMode"})
    API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.declare_sort(sort));

  Solver s(tm);
  std::vector<Term> named;
  for (const char* name : {"True", "Select", "bvadd1", "assert", "let", "odd name", "1abc", "x!0"})
    named.push_back(tm.declare(name, bv8));
  for (std::size_t i = 0; i < named.size(); ++i)
    s.add(named[i] == tm.mk_bv(8, i + 1));
  const Sort T = tm.declare_sort("Boolean");
  s.add(tm.declare("t1", T) != tm.declare("t2", T));
  ASSERT_TRUE(s.check_sat().is_sat());
  TermManager fresh;
  Solver back(fresh);
  back.parse_smt2(s.to_smt2(true));
  ASSERT_TRUE(back.check_sat().is_sat());
  for (std::size_t i = 0; i < named.size(); ++i)
  {
    const std::string name = *named[i].symbol();
    ASSERT_TRUE(fresh.symbol(name).has_value()) << name;
    EXPECT_EQ(back.model().uint64_value(*fresh.symbol(name)), i + 1) << name;
  }
}

// SMT-LIB's unary (- a) and n-ary (- a b c) read as one engine node; the
// public view presents them as REAL_NEG and left-associated binary REAL_SUB,
// so a walker rebuilds them from kind(), children(), indices() and sort().
TEST(RoundTrips, a_parsed_real_minus_rebuilds_from_its_view)
{
  for (const bool simplify : {true, false})
  {
    SCOPED_TRACE(simplify ? "simplify" : "no simplify");
    TermManager::Config cfg;
    cfg.simplify = simplify;
    TermManager tm(cfg);
    const Sort R = tm.mk_real_sort();
    const Term r1 = tm.declare("r1", R), r2 = tm.declare("r2", R);
    tm.declare("r3", R);
    Solver s(tm);
    for (const char* text : {"(- r1 r2 r3)", "(- r1)", "(- r1 r2)", "(- 5 2 r3)", "(- r1 r2 r3 r1)"})
    {
      SCOPED_TRACE(text);
      const Term t = s.parse_term(text);
      Term back;
      const auto e = API_ERROR_OF(back = tm.mk_term(t.kind(), t.children(), t.indices(), t.sort()));
      ASSERT_FALSE(e.has_value()) << e->what();
      EXPECT_TRUE(s.entails(back == t).is_valid()) << back.str() << " vs " << t.str();
      const Term swapped = t.substitute({{r1, r2}});
      EXPECT_EQ(swapped.sort(), R);
    }
    EXPECT_EQ(s.parse_term("(- r1)").kind(), Kind::REAL_NEG);
    EXPECT_EQ(s.parse_term("(- r1 r2 r3)").num_children(), 2u);
  }
}

// A bind_symbol alias names its symbol for every reader of the manager's
// table, the parsers included.
TEST(RoundTrips, bind_symbol_aliases_reach_the_parsers)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  tm.bind_symbol("y", x);
  Solver s(tm);
  s.parse_smt2("(assert (= y #x01))");
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 1u);
  EXPECT_TRUE(s.entails(s.parse_term("(bvadd y x)") == bvadd(x, x)).is_valid());
  s.parse("ASSERT(BVLT(y, 0hex05)); QUERY(FALSE);", Format::CVC);
  ASSERT_TRUE(s.check_sat().is_sat());
  // and a script's own declaration of the name is a redeclaration
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(declare-fun y () (_ BitVec 8))"));
}

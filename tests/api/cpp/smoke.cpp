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
// A first end-to-end exercise of the 3.x C++ API: sorts, symbols, values,
// every theory's constructors, options, checks, models and printing.

#include <stp/stp.hpp>

#include <cassert>
#include <cstdio>
#include <iostream>
#include <sstream>

using namespace stp;

static int failures = 0;
#define CHECK(cond)                                                            \
  do                                                                           \
  {                                                                            \
    if (!(cond))                                                               \
    {                                                                          \
      std::printf("FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);              \
      ++failures;                                                              \
    }                                                                          \
  } while (0)

static void bv_basics()
{
  TermManager tm;
  Sort bv32 = tm.mk_bv_sort(32);
  Term x = tm.declare("x", bv32);
  Term y = tm.declare("y", bv32);
  CHECK(x.kind() == Kind::CONSTANT);
  CHECK(x.sort() == bv32);
  CHECK(x.symbol().has_value() && *x.symbol() == "x");
  CHECK(tm.declare("x", bv32).same_as(x));
  Term sum = x + y;
  CHECK(sum.kind() == Kind::BV_ADD);
  CHECK(sum.num_children() == 2);
  Term three = tm.mk_bv(32, 3);
  CHECK(three.is_value() && three.to_uint64() == 3);
  Term c = x * 3 == 7;
  CHECK(c.sort().is_bool());
  Solver s(tm);
  s.add(c);
  s.add(bvult(y, 10));
  Result r = s.check_sat();
  CHECK(r.is_sat());
  Model m = s.model();
  Term xv = m.value(x);
  CHECK(xv.is_value());
  const std::uint64_t xu = xv.to_uint64();
  CHECK(((xu * 3) & 0xffffffffu) == 7);
  CHECK(m.uint64_value(y) < 10);
  CHECK(m.value(x * 3).to_uint64() == 7);
  CHECK(m.in_core(x));
  std::cout << "  model: " << m.to_smt2();
  // unsat
  s.push();
  s.add(x == 0);
  CHECK(s.check_sat().is_unsat());
  s.pop();
  CHECK(s.check_sat().is_sat());
  // entails
  CHECK(s.entails(bvult(y, 11)).is_valid());
  CHECK(s.entails(bvult(y, 3)).is_invalid());
  // readers
  Term big = tm.mk_bv(128, "0x0123456789abcdef0123456789abcdef", 16);
  CHECK(big.to_bv_string(16) == "0123456789abcdef0123456789abcdef");
  CHECK(!big.fits_uint64());
  CHECK(big.to_bv_limbs().size() == 2 && big.to_bv_limbs()[0] == 0x0123456789abcdefull);
  Term neg = tm.mk_bv_signed(8, -2);
  CHECK(neg.to_int64() == -2 && neg.to_uint64() == 254);
  CHECK(neg.to_bv_string(2) == "11111110");
  // structure is only guaranteed by a non-simplifying manager
  TermManager::Config raw_cfg;
  raw_cfg.simplify = false;
  TermManager raw(raw_cfg);
  Term rx = raw.declare("x", raw.mk_bv_sort(32));
  CHECK(extract(3, 0, rx).kind() == Kind::BV_EXTRACT);
  CHECK(extract(3, 0, rx).indices() == std::vector<std::uint32_t>({3, 0}));
  Term ext = zero_extend(8, rx);
  CHECK(ext.sort().bv_size() == 40 && ext.kind() == Kind::BV_ZERO_EXTEND);
  CHECK(ext.indices().size() == 1 && ext.indices()[0] == 8);
  CHECK(zero_extend(8, x).sort().bv_size() == 40);
  CHECK(rotate_left(4, three).is_value() && rotate_left(4, three).to_uint64() == 48);
  CHECK(bvcomp(x, x).sort().bv_size() == 1);
  CHECK(tm.simplify(bvadd(x, tm.mk_bv(32, 0))).same_as(x));
  // errors
  try
  {
    (void)(x + tm.declare("b", tm.mk_bool_sort()));
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::SORT_MISMATCH);
    std::cout << "  expected error: " << e.what() << "\n";
  }
  try
  {
    (void)tm.mk_bv(8, 256);
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::VALUE_OUT_OF_RANGE);
  }
  try
  {
    (void)tm.declare("x", tm.mk_bv_sort(8));
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::SORT_MISMATCH);
  }
  std::cout << "  smt2:\n" << s.to_smt2(true);
}

static void arrays()
{
  TermManager tm;
  Sort bv8 = tm.mk_bv_sort(8), bv32 = tm.mk_bv_sort(32);
  Sort arr = tm.mk_array_sort(bv32, bv8);
  Term a = tm.declare("a", arr);
  Term i = tm.declare("i", bv32);
  Solver s(tm);
  s.add(a[i] == 42);
  s.add(select(store(a, i + 1, tm.mk_bv(8, 7)), i) == 42);
  s.add(i == 5);
  CHECK(s.check_sat().is_sat());
  Model m = s.model();
  CHECK(m.value(a[tm.mk_bv(32, 5)]).to_uint64() == 42);
  ArrayValue av = m.array_value(a);
  CHECK(av.size() >= 1);
  std::cout << "  array model: " << m.to_smt2();
  std::uint8_t bytes[4] = {0, 0, 0, 0};
  m.array_bytes(a, 4, 4, bytes);
  CHECK(bytes[1] == 42);
  // constant arrays
  Term k = tm.mk_const_array(arr, tm.mk_bv(8, 9));
  CHECK(k.kind() == Kind::CONST_ARRAY);
  CHECK(select(k, i).is_value() && select(k, i).to_uint64() == 9);
  Term ks = store(k, tm.mk_bv(32, 1), tm.mk_bv(8, 3));
  CHECK(select(ks, tm.mk_bv(32, 1)).to_uint64() == 3);
  CHECK(select(ks, tm.mk_bv(32, 2)).to_uint64() == 9);
  Term fb = array_from_bytes(tm, {1, 2, 3});
  CHECK(select(fb, tm.mk_bv(32, 2)).to_uint64() == 3);
  // extensional equality
  Term b = tm.declare("b", arr);
  s.reset_assertions();
  s.add(a == store(b, i, tm.mk_bv(8, 1)));
  s.add(b[i] == 2);
  CHECK(s.check_sat().is_sat());
  CHECK(s.model().value(a[i]).to_uint64() == 1);
  s.add(a[i] == 2);
  CHECK(s.check_sat().is_unsat());
}

static void floats()
{
  TermManager tm;
  Sort f32 = tm.mk_fp32_sort();
  Term x = tm.declare("fx", f32);
  Term one = tm.mk_fp(f32, RoundingMode::RNE, 1.0);
  CHECK(one.is_value());
  CHECK(one.to_fp().to_double().has_value() && *one.to_fp().to_double() == 1.0);
  Term tenth = tm.mk_fp(f32, RoundingMode::RNE, "0.1");
  CHECK(tenth.to_fp().to_double().has_value() && static_cast<float>(*tenth.to_fp().to_double()) == 0.1f);
  Term third = tm.mk_fp(f32, RoundingMode::RTZ, "1/3");
  CHECK(third.to_fp().cls == FloatValue::Class::NORMAL);
  Solver s(tm);
  s.add(fp_add(RoundingMode::RNE, x, 1.0) == tm.mk_fp(f32, RoundingMode::RNE, 3.0));
  CHECK(s.check_sat().is_sat());
  Model m = s.model();
  FloatValue v = m.fp_value(x);
  CHECK(v.to_double().has_value());
  // through a volatile float: x87 keeps the sum in extended precision otherwise
  volatile float sum = static_cast<float>(*v.to_double()) + 1.0f;
  CHECK(sum == 3.0f);
  CHECK(*m.value(fp_add(RoundingMode::RNE, x, 1.0)).to_fp().to_double() == 3.0);
  std::cout << "  fp model: " << m.to_smt2();
  CHECK(fp_is_nan(tm.mk_fp_nan(f32)).is_value() && fp_is_nan(tm.mk_fp_nan(f32)).to_bool());
  CHECK(tm.mk_fp_neg_zero(f32).to_fp().sign);
  Term rm = tm.declare("rm", tm.mk_rm_sort());
  s.reset_assertions();
  s.add(fp_add(rm, one, tenth) == fp_add(RoundingMode::RTP, one, tenth));
  s.add(!(rm == tm.mk_rm(RoundingMode::RTP)));
  CHECK(s.check_sat().is_sat());
  Term rmv = s.model().value(rm);
  CHECK(rmv.is_value());
  std::cout << "  rm = " << to_string(rmv.to_rm()) << "\n";
  Term bits = fp_to_ieee_bv(one);
  CHECK(bits.is_value() && bits.to_uint64() == 0x3f800000u);
  Term back = to_fp_from_bits(f32, bits);
  CHECK(back.same_as(one));
  Term i = tm.declare("fi", tm.mk_bv_sort(32));
  Term conv = to_fp(f32, RoundingMode::RNE, i);
  CHECK(conv.kind() == Kind::FP_TO_FP_FROM_SBV && conv.indices() == std::vector<std::uint32_t>({8, 24}));
  Term ub = fp_to_ubv(8, RoundingMode::RTZ, x);
  CHECK(ub.sort().bv_size() == 8 && ub.kind() == Kind::FP_TO_UBV);
  Term fpfp = tm.mk_fp(tm.mk_bv(1, 0), tm.mk_bv(8, 127), tm.mk_bv(23, 0));
  CHECK(fpfp.is_value() && fpfp.same_as(one));
  Term real_to_fp = to_fp(f32, RoundingMode::RNE, tm.mk_real("1/4"));
  CHECK(real_to_fp.is_value() && *real_to_fp.to_fp().to_double() == 0.25);
}

static void uninterpreted()
{
  TermManager tm;
  Sort bv8 = tm.mk_bv_sort(8);
  Sort fs = tm.mk_fun_sort({bv8, bv8}, bv8);
  Term f = tm.declare("f", fs);
  CHECK(f.sort().is_fun() && f.sort().fun_arity() == 2);
  Term a = tm.declare("ua", bv8), b = tm.declare("ub", bv8);
  Term fa = f(a, b);
  CHECK(fa.kind() == Kind::APPLY && fa.sort() == bv8);
  Solver s(tm);
  s.add(fa == 3);
  s.add(f(b, a) == 4);
  s.add(a == b);
  CHECK(s.check_sat().is_unsat());
  s.reset_assertions();
  s.add(fa == 3);
  s.add(f(b, a) == 4);
  CHECK(s.check_sat().is_sat());
  Model m = s.model();
  CHECK(m.value(fa).to_uint64() == 3);
  FunctionValue fv = m.function_value(f);
  std::cout << "  uf model: " << m.to_smt2();
  CHECK(fv.apply({m.value(a), m.value(b)}).to_uint64() == 3);
  // declared sorts
  Sort S = tm.declare_sort("S");
  Term p = tm.declare("p", S), q = tm.declare("q", S);
  s.reset_assertions();
  s.add(distinct(p, q));
  CHECK(s.check_sat().is_sat());
  CHECK(s.model().value(p).to_uninterpreted_index() != s.model().value(q).to_uninterpreted_index());
  std::cout << "  sort model: " << s.model().to_smt2();
}

static void reals()
{
  TermManager tm;
  Sort R = tm.mk_real_sort();
  Term x = tm.declare("rx", R), y = tm.declare("ry", R);
  Solver s(tm);
  s.add(x + y == tm.mk_real(3));
  s.add(real_lt(x, y));
  s.add(x * 2 == y);
  CHECK(s.check_sat().is_sat());
  Model m = s.model();
  RationalValue xv = m.real_value(x);
  std::cout << "  rx = " << xv.str() << " ry = " << m.real_value(y).str() << "\n";
  CHECK(xv.str() == "1");
  CHECK(m.real_value(y).str() == "2");
  s.add(real_gt(x, 5));
  CHECK(s.check_sat().is_unsat());
}

static void options_and_limits()
{
  TermManager tm;
  Options o;
  o.set_bool("produce-models", true);
  o.set("max-time", "2s");
  o.set_uint("max-num-confl", 1000000);
  // a backend this build has (CI builds each backend on its own)
  const std::string backend = sat_backends().front();
  o.set_str("sat-backend", backend);
  CHECK(o.get_duration("max-time").count() == 2000);
  CHECK(o.get_str("sat-backend") == backend);
  o.set_args({"--fp-abstraction", "--bb.div-v3=false"});
  CHECK(o.get_bool("fp-abstraction"));
  CHECK(!o.get_bool("bb.div-v3"));
  try
  {
    o.set("no-such-option", "1");
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::OPTION_UNKNOWN);
  }
  try
  {
    o.set_bool("max-time", true);
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::OPTION_VALUE);
  }
  OptionInfo info = o.info("incremental");
  CHECK(info.type == "mode" && info.tier == Tier::STABLE);
  CHECK(o.names(Tier::STABLE).size() == 22);
  Solver s(tm, o);
  s.options().set_str("logic", "QF_BV"); // before the first check: allowed
  CHECK(s.options().get_str("logic") == "QF_BV");
  try
  {
    s.options().set_str("sat-backend", backend); // construction-only
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::OPTION_TIMING);
  }
  Term x = tm.declare("ox", tm.mk_bv_sort(64));
  s.add(bvmul(x, x) == 1);
  Result r = s.check_sat({}, CheckBudget{std::chrono::milliseconds(0), std::nullopt});
  CHECK(r.is_unknown() && r.reason() == UnknownReason::TIMEOUT);
  std::cout << "  zero budget: " << r << " (" << r.reason_message() << ")\n";
  try
  {
    s.options().set_str("logic", "QF_ABV"); // after a check: refused, unchanged
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::OPTION_TIMING);
    CHECK(s.options().get_str("logic") == "QF_BV");
  }
  s.options().set_duration("max-time", std::chrono::seconds(30)); // anytime
  s.interrupt();
  Result ri = s.check_sat();
  CHECK(ri.is_unknown() && ri.reason() == UnknownReason::INTERRUPTED);
  CHECK(s.check_sat().is_sat());
  Statistics st = s.statistics();
  CHECK(st.str("sat.backend") == backend);
  std::ostringstream cnf;
  s.write_cnf(cnf);
  CHECK(cnf.str().find("p cnf") != std::string::npos);
  std::cout << "  cnf header: " << cnf.str().substr(0, cnf.str().find('\n')) << "\n";
}

static void parsing()
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(set-logic QF_BV)\n(declare-fun px () (_ BitVec 8))\n(assert (= px #x2a))\n(check-sat)\n");
  std::optional<Term> px = tm.symbol("px");
  CHECK(px.has_value());
  CHECK(s.check_sat().is_sat());
  CHECK(s.model().uint64_value(*px) == 42);
  Term t = s.parse_term("(bvadd px #x01)");
  CHECK(t.kind() == Kind::BV_ADD);
  CHECK(s.model().value(t).to_uint64() == 43);
  try
  {
    s.parse_smt2("(assert (= px #x2a)");
    CHECK(false);
  }
  catch (const RecoverableError& e)
  {
    CHECK(e.code() == ErrorCode::PARSE);
    std::cout << "  parse error: " << e.what() << "\n";
  }
  TermManager tm2;
  Solver s2(tm2);
  s2.parse("(declare-fun cx () (_ BitVec 8))\n(assert (= cx #x2a))\n(assert (not (= cx #x2b)))\n",
           Format::SMTLIB2);
  CHECK(s2.check_sat().is_sat());
  CHECK(s2.model().uint64_value(*tm2.symbol("cx")) == 42);
  // floating-point and Real fragments parse without a set-logic in front
  Term fx = tm.declare("pfx", tm.mk_fp32_sort());
  Term fsum = s.parse_term("(fp.add RNE pfx pfx)");
  CHECK(fsum.kind() == Kind::FP_ADD && fsum.sort() == tm.mk_fp32_sort());
  (void)fx;
  CHECK(s.parse_term("(fp #b0 #b01111111 #b00000000000000000000000)").is_value());
}

int main()
{
  std::cout << "STP " << version().string << " api " << capabilities()["api.version"] << "\n";
  std::cout << "[bv]\n";
  bv_basics();
  std::cout << "[arrays]\n";
  arrays();
  std::cout << "[floats]\n";
  floats();
  std::cout << "[uf]\n";
  uninterpreted();
  std::cout << "[reals]\n";
  reals();
  std::cout << "[options]\n";
  options_and_limits();
  std::cout << "[parsing]\n";
  parsing();
  std::cout << (failures ? "FAILURES: " : "all passed: ") << failures << "\n";
  return failures ? 1 : 0;
}

#include "ExactRational.h"
#include "ImathAllocHooks.h"
#include "PortableBits.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>

namespace {

using stp::lra::ExactRational;
using stp::lra::ExactRationalHash;
using stp::lra::NumberBudget;
using stp::lra::NumberFailure;
using stp::lra::NumberFailureKind;
using stp::lra::NumberLimits;
using stp::lra::NumberMetrics;
using stp::lra::NumberOperationScope;

constexpr std::uint64_t unlimited =
    std::numeric_limits<std::uint64_t>::max();

NumberLimits generousLimits()
{
  return NumberLimits{UINT64_C(65536), UINT64_C(65536),
                      UINT64_C(268435456), UINT64_C(16777216)};
}

[[noreturn]] void fail(std::string const& message)
{
  throw std::runtime_error(message);
}

void require(bool condition, std::string const& message)
{
  if (!condition)
  {
    fail(message);
  }
}

template <class Function>
void expectFailure(NumberFailureKind expected,
                   std::string const& label,
                   Function&& function)
{
  try
  {
    function();
  }
  catch (NumberFailure const& failure)
  {
    if (failure.kind() != expected)
    {
      fail(label + ": wrong NumberFailureKind");
    }
    require(failure.operation() != nullptr,
            label + ": missing operation name");
    return;
  }
  fail(label + ": expected NumberFailure");
}

std::string fraction(ExactRational const& value)
{
  return value.canonicalFraction();
}

NumberMetrics::AllocationSite const& allocationSite(
    NumberMetrics const& metrics,
    stp_lra_imath_allocation_site site)
{
  return metrics.allocation_sites[static_cast<std::size_t>(site)];
}

void writeNativeMetrics(std::ostream& output, NumberMetrics const& metrics)
{
  output << ",\"native_materializations\":"
         << metrics.native_materializations << ",\"native_demotions\":"
         << metrics.native_demotions << ",\"native_additions\":"
         << metrics.native_additions << ",\"native_subtractions\":"
         << metrics.native_subtractions << ",\"native_multiplications\":"
         << metrics.native_multiplications << ",\"native_divisions\":"
         << metrics.native_divisions;
  struct NamedSite
  {
    char const* name;
    stp_lra_imath_allocation_site site;
  };
  NamedSite const sites[] = {
      {"unattributed", STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED},
      {"construct", STP_LRA_IMATH_ALLOCATION_CONSTRUCT},
      {"parse", STP_LRA_IMATH_ALLOCATION_PARSE},
      {"materialize", STP_LRA_IMATH_ALLOCATION_MATERIALIZE},
      {"canonicalize", STP_LRA_IMATH_ALLOCATION_CANONICALIZE},
      {"add", STP_LRA_IMATH_ALLOCATION_ADD},
      {"subtract", STP_LRA_IMATH_ALLOCATION_SUBTRACT},
      {"multiply", STP_LRA_IMATH_ALLOCATION_MULTIPLY},
      {"divide", STP_LRA_IMATH_ALLOCATION_DIVIDE},
  };
  for (NamedSite const& named : sites)
  {
    NumberMetrics::AllocationSite const& site =
        allocationSite(metrics, named.site);
    output << ",\"allocation_" << named.name << "_calls\":" << site.calls
           << ",\"allocation_" << named.name << "_bytes\":" << site.bytes;
  }
}

void testConstructionAndOwnership()
{
  NumberBudget budget(generousLimits());
  std::optional<ExactRational> destroy_after_scope;
  {
    NumberOperationScope scope(budget);
    ExactRational zero;
    ExactRational signed_min(std::numeric_limits<std::int64_t>::min());
    ExactRational signed_max(std::numeric_limits<std::int64_t>::max());
    ExactRational unsigned_max(std::numeric_limits<std::uint64_t>::max());
    ExactRational half(2, 4);
    require(fraction(zero) == "0", "default construction");
    std::string const signed_min_text = fraction(signed_min);
    require(signed_min_text == "-9223372036854775808",
            "int64 minimum construction observed " + signed_min_text);
    require(fraction(signed_max) == "9223372036854775807",
            "int64 maximum construction");
    require(fraction(unsigned_max) == "18446744073709551615",
            "uint64 maximum construction");
    require(fraction(half) == "1/2", "rational reduction");
    expectFailure(NumberFailureKind::ZeroDenominator,
                  "zero denominator constructor",
                  [] { ExactRational invalid(1, 0); });

    ExactRational copy(half);
    ExactRational moved(std::move(copy));
    require(fraction(copy) == "0", "moved-from copy is zero");
    require(fraction(moved) == "1/2", "move preserves value");
    ExactRational& self = moved;
    moved = self;
    moved = std::move(self);
    require(fraction(moved) == "1/2", "self assignments");
    copy = moved;
    require(copy == moved, "copy assignment");
    copy.swap(zero);
    require(fraction(copy) == "0" && fraction(zero) == "1/2",
            "swap");

    std::vector<ExactRational> values;
    values.reserve(1);
    for (std::int64_t index = 0; index != 64; ++index)
    {
      values.emplace_back(index);
    }
    for (std::size_t index = 0; index != values.size(); ++index)
    {
      require(fraction(values[index]) == std::to_string(index),
              "vector growth preserves values");
    }
    destroy_after_scope.emplace(ExactRational::parseDecimalOrFraction(
        "123456789012345678901234567890/37"));
    require(budget.metrics().current_values >= 1,
            "live-value metrics within scope");
    require(budget.metrics().peak_values >= budget.metrics().current_values,
            "peak-value metrics");
  }
  require(destroy_after_scope.has_value(), "delayed destruction fixture");
  destroy_after_scope.reset();
  require(budget.metrics().current_values == 0,
          "destruction outside operation scope");
  require(budget.metrics().destroys > 0, "destroy metric");
}

void testParsingAndCanonicalization()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  std::vector<std::pair<std::string, std::string>> const accepted = {
      {"0", "0"},
      {"-0", "0"},
      {"00042", "42"},
      {"-00042", "-42"},
      {"6/8", "3/4"},
      {"-006/0008", "-3/4"},
      {"12.500", "25/2"},
      {"-0.125", "-1/8"},
      {"99999999999999999999999999999999999999/3",
       "33333333333333333333333333333333333333"}};
  for (auto const& [source, canonical] : accepted)
  {
    ExactRational value = ExactRational::parseDecimalOrFraction(source);
    require(fraction(value) == canonical, "parse: " + source);
    require(value.invariantHolds(), "canonical invariant: " + source);
    require(value.denominatorDecimal().front() != '-' &&
                value.denominatorDecimal() != "0",
            "positive denominator: " + source);
    ExactRational roundtrip =
        ExactRational::parseDecimalOrFraction(fraction(value));
    require(roundtrip == value, "canonical round trip: " + source);
    require(fraction(ExactRational::parseDecimalOrFraction(source)) ==
                fraction(roundtrip),
            "stable canonical output: " + source);
  }

  ExactRational defensive =
      ExactRational::fromCanonicalIntegers("00030", "00042");
  require(fraction(defensive) == "5/7",
          "canonical components validated defensively");

  std::vector<std::string> const invalid = {
      "",       " ",      " 1",     "1 ",    "+1",   ".",
      ".1",     "1.",     "1e3",    "0x10",  "NaN",  "inf",
      "1/",     "/2",     "- /2",   "1/-2",  "1/+2", "1/2x",
      "1/2/3",  "1..2",   "--1",    "1 2",   "-",    "-.",
  };
  for (std::string const& source : invalid)
  {
    expectFailure(NumberFailureKind::InvalidText, "invalid parse: " + source,
                  [&] { (void)ExactRational::parseDecimalOrFraction(source); });
  }
  expectFailure(NumberFailureKind::ZeroDenominator,
                "parsed zero denominator",
                [] { (void)ExactRational::parseDecimalOrFraction("1/000"); });
  expectFailure(NumberFailureKind::ZeroDenominator,
                "component zero denominator",
                [] { (void)ExactRational::fromCanonicalIntegers("1", "0"); });
}

void testArithmetic()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  ExactRational a = ExactRational::parseDecimalOrFraction("7/12");
  ExactRational b = ExactRational::parseDecimalOrFraction("-5/18");
  require(fraction(a + b) == "11/36", "addition");
  require(fraction(a - b) == "31/36", "subtraction");
  require(fraction(a * b) == "-35/216", "multiplication");
  require(fraction(a / b) == "-21/10", "division");
  require(fraction(-a) == "-7/12", "unary minus");
  require(fraction(a.inverse()) == "12/7", "inverse");

  ExactRational compound(a);
  compound += b;
  require(fraction(compound) == "11/36", "compound add");
  compound -= b;
  compound *= b;
  compound /= b;
  require(compound == a, "compound operations");

  ExactRational out(std::int64_t{9});
  stp::lra::add(out, a, b);
  require(fraction(out) == "11/36", "out add");
  stp::lra::subtract(out, a, b);
  require(fraction(out) == "31/36", "out subtract");
  stp::lra::multiply(out, a, b);
  require(fraction(out) == "-35/216", "out multiply");
  stp::lra::divide(out, a, b);
  require(fraction(out) == "-21/10", "out divide");

  ExactRational alias = a;
  stp::lra::add(alias, alias, b);
  require(fraction(alias) == "11/36", "out alias input");
  stp::lra::multiply(alias, alias, alias);
  require(fraction(alias) == "121/1296", "full alias multiply");
  ExactRational cancellation = ExactRational::parseDecimalOrFraction(
      "999999999999999999999999999999/37");
  require(fraction(cancellation / cancellation) == "1", "cancellation");
  require(fraction(a + ExactRational(std::int64_t{0})) == "7/12" &&
              fraction(a * ExactRational(std::int64_t{1})) == "7/12",
          "zero and one identities");
  ExactRational reduced = ExactRational::parseDecimalOrFraction("65535/257") *
                          ExactRational::parseDecimalOrFraction("257/255");
  require(fraction(reduced) == "257" && reduced.numeratorBits() == 9 &&
              reduced.denominatorBits() == 1,
          "post-operation reduction and exact bit sizes");
  ExactRational minimum(std::numeric_limits<std::int64_t>::min());
  require(fraction(-minimum) == "9223372036854775808",
          "minimum signed unary negation");

  ExactRational zero;
  expectFailure(NumberFailureKind::DivisionByZero, "division by zero",
                [&] { (void)(a / zero); });
  expectFailure(NumberFailureKind::DivisionByZero, "inverse zero",
                [&] { (void)zero.inverse(); });
}

void testBackendNeutralOptimizations()
{
  {
    NumberBudget budget(generousLimits());
    NumberOperationScope scope(budget);
    NumberMetrics const before = budget.metrics();
    ExactRational reduced_constructor(6, UINT64_C(8));
    ExactRational small_unsigned(UINT64_C(42));
    ExactRational reduced_parse = ExactRational::parseDecimalOrFraction(
        "6000000000000000000/3000000000000000000");
    NumberMetrics const small = budget.metrics();
    require(fraction(reduced_constructor) == "3/4" &&
                fraction(small_unsigned) == "42" &&
                fraction(reduced_parse) == "2",
            "word-sized construction and parse values");
    require(small.allocation_calls == before.allocation_calls &&
                small.native_demotions == before.native_demotions,
            "word-sized constants avoid native allocation and demotion");

    ExactRational demoted_parse = ExactRational::parseDecimalOrFraction(
        "12000000000000000000/6000000000000000000");
    NumberMetrics const demoted = budget.metrics();
    require(fraction(demoted_parse) == "2",
            "wide reducible parse canonical value");
    require(demoted.native_demotions == small.native_demotions + 1 &&
                allocationSite(demoted, STP_LRA_IMATH_ALLOCATION_PARSE).calls >
                    allocationSite(small, STP_LRA_IMATH_ALLOCATION_PARSE).calls,
            "wide parse records native allocation and demotion");
  }

  {
    NumberBudget budget(generousLimits());
    NumberOperationScope scope(budget);
    std::string const power_of_two =
        "115792089237316195423570985008687907853269984665640564039457584007913129639936";
    ExactRational one_over_three = ExactRational::fromCanonicalIntegers(
        "1",
        "347376267711948586270712955026063723559809953996921692118372752023739388919808");
    ExactRational one_over_five = ExactRational::fromCanonicalIntegers(
        "1",
        "578960446186580977117854925043439539266349923328202820197287920039565648199680");
    ExactRational seventeen_over_power =
        ExactRational::fromCanonicalIntegers("17", power_of_two);
    ExactRational power_over_nineteen =
        ExactRational::fromCanonicalIntegers(power_of_two, "19");
    ExactRational nineteen_over_power =
        ExactRational::fromCanonicalIntegers("19", power_of_two);
    NumberMetrics const before = budget.metrics();

    ExactRational sum = one_over_three + one_over_five;
    ExactRational difference = one_over_three - one_over_five;
    ExactRational product = seventeen_over_power * power_over_nineteen;
    ExactRational quotient = seventeen_over_power / nineteen_over_power;
    NumberMetrics const after = budget.metrics();
    require(
        fraction(sum) ==
            "1/217110167319967866419195596891289827224881221248076057573982970014837118074880" &&
            fraction(difference) ==
                "1/868440669279871465676782387565159308899524884992304230295931880059348472299520",
        "denominator-GCD addition and subtraction");
    require(fraction(product) == "17/19" &&
                fraction(quotient) == "17/19",
            "cross-cancelled multiplication and division");
    require(after.native_additions == before.native_additions + 1 &&
                after.native_subtractions == before.native_subtractions + 1 &&
                after.native_multiplications ==
                    before.native_multiplications + 1 &&
                after.native_divisions == before.native_divisions + 1,
            "native arithmetic path counters");
    require(allocationSite(after, STP_LRA_IMATH_ALLOCATION_ADD).calls >
                allocationSite(before, STP_LRA_IMATH_ALLOCATION_ADD).calls &&
                allocationSite(after, STP_LRA_IMATH_ALLOCATION_SUBTRACT).calls >
                    allocationSite(before,
                                   STP_LRA_IMATH_ALLOCATION_SUBTRACT).calls &&
                allocationSite(after, STP_LRA_IMATH_ALLOCATION_MULTIPLY).calls >
                    allocationSite(before,
                                   STP_LRA_IMATH_ALLOCATION_MULTIPLY).calls &&
                allocationSite(after, STP_LRA_IMATH_ALLOCATION_DIVIDE).calls >
                    allocationSite(before,
                                   STP_LRA_IMATH_ALLOCATION_DIVIDE).calls,
            "native arithmetic allocation sites");
  }

  {
    NumberBudget budget(generousLimits());
    NumberOperationScope scope(budget);
    ExactRational native = ExactRational::fromCanonicalIntegers(
        "1",
        "115792089237316195423570985008687907853269984665640564039457584007913129639936");
    // The widest word: 2^62 - 1 where the word lane has a 128-bit type to
    // multiply in, 2^31 - 1 where it runs at half scale without one.
#ifdef STP_LRA_HAVE_WIDE
    ExactRational word = ExactRational::fromCanonicalIntegers(
        "4611686018427387903", "4611686018427387902");
#else
    ExactRational word =
        ExactRational::fromCanonicalIntegers("2147483647", "2147483646");
#endif
    NumberMetrics const before = budget.metrics();
    ExactRational product = native * word;
    NumberMetrics const after = budget.metrics();
    require(product.invariantHolds(), "materialized multiplication invariant");
    require(after.native_materializations ==
                    before.native_materializations + 1 &&
                after.native_multiplications ==
                    before.native_multiplications + 1 &&
                allocationSite(after,
                               STP_LRA_IMATH_ALLOCATION_MATERIALIZE).calls >
                    allocationSite(before,
                                   STP_LRA_IMATH_ALLOCATION_MATERIALIZE).calls,
            "native materialization metric and allocation site");
  }
}

void testComparisonHashAndSmall()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  ExactRational half = ExactRational::parseDecimalOrFraction("2/4");
  ExactRational same = ExactRational::parseDecimalOrFraction("0.5");
  ExactRational lower = ExactRational::parseDecimalOrFraction("499/1000");
  require(half == same && !(half != same), "equality");
  require(lower < half && lower <= half && half > lower && half >= lower,
          "all order relations");
  require(half.compare(same) == 0 && lower.compare(half) == -1 &&
              half.compare(lower) == 1,
          "three-way comparison domain");

  ExactRational huge_left = ExactRational::fromCanonicalIntegers(
      std::string(620, '9'), std::string(311, '9'));
  ExactRational huge_right = ExactRational::fromCanonicalIntegers(
      std::string(619, '9'), std::string(310, '9'));
  require(huge_left.compare(huge_right) < 0,
          "checked huge cross-product comparison");

  require(half.stableHash() == UINT64_C(5008217293888502209),
          "pinned FNV-1a hash for 1/2");
  require(ExactRational(std::int64_t{0}).stableHash() ==
              UINT64_C(5626642007058801603),
          "pinned FNV-1a hash for 0/1");
  require(ExactRational(std::int64_t{-1}).stableHash() ==
              UINT64_C(13870184763889768679),
          "pinned FNV-1a hash for -1/1");
  require(half.stableHash() == same.stableHash(),
          "hash ignores noncanonical source text");
  std::unordered_map<ExactRational, std::string, ExactRationalHash> table;
  table.emplace(half, "half");
  require(table.at(same) == "half", "unordered_map hash behavior");

  auto small = half.trySmall();
  require(small && small->numerator == 1 && small->denominator == 2,
          "small extraction");
  ExactRational reconstructed(small->numerator, small->denominator);
  require(reconstructed == half, "small extraction exact round trip");
  ExactRational minimum(std::numeric_limits<std::int64_t>::min(),
                        std::numeric_limits<std::uint64_t>::max());
  auto minimum_small = minimum.trySmall();
  require(minimum_small &&
              minimum_small->numerator ==
                  std::numeric_limits<std::int64_t>::min() &&
              minimum_small->denominator ==
                  std::numeric_limits<std::uint64_t>::max(),
          "small extraction fixed-width boundaries");
  require(!huge_left.trySmall(), "huge value is not truncated by trySmall");
}

/* Negation of a word-sized value has to stay word-sized.
 *
 * The value assertions hold under either representation, so they cannot see
 * which one is in use; the allocation count is what pins it.  Word values never
 * touch the allocator, so a negate that quietly materialised into IMath would
 * raise allocation_calls and fail here.
 *
 * Everything inside the counted region therefore reads values back through
 * trySmall, which has a word path.  canonicalFraction does not -- it asks for
 * the native form and allocates -- so the printed comparisons come after. */
void testNegationStaysWordSized()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);

  auto const small = [](ExactRational const& value) {
    auto const extracted = value.trySmall();
    require(static_cast<bool>(extracted), "value is word sized");
    return *extracted;
  };

  ExactRational value(std::int64_t{-7}, std::uint64_t{3});
  ExactRational rotating(std::int64_t{5}, std::uint64_t{8});
  ExactRational zero(std::int64_t{0});
  /* Wide enough to exercise the sign flip on a multi-digit numerator, and
   * still inside the word range on the half-scale build a platform without a
   * 128-bit type gets. */
  ExactRational large(-std::int64_t{2147483647}, std::uint64_t{2});

  std::uint64_t const before = budget.metrics().allocation_calls;

  ExactRational const negated = -value;
  require(small(negated).numerator == 7 && small(negated).denominator == 3,
          "unary minus on a word value");
  require(small(-negated).numerator == -7, "unary minus round trip");

  for (int index = 0; index < 64; ++index)
  {
    rotating.negate();
  }
  require(small(rotating).numerator == 5, "even negate count is the identity");
  rotating.negate();
  require(small(rotating).numerator == -5 && small(rotating).denominator == 8,
          "odd negate count flips the sign");

  zero.negate();
  require(small(zero).numerator == 0 && small(zero).denominator == 1 &&
              zero.sign() == 0,
          "negated zero stays canonical zero");

  ExactRational const large_negated = -large;
  require(small(large_negated).numerator == 2147483647 &&
              small(large_negated).denominator == 2,
          "negation of a large word value");
  require(-large_negated == large, "large word negation round trip");

  require(budget.metrics().allocation_calls == before,
          "negating word values does not allocate");
  require(negated.invariantHolds() && rotating.invariantHolds() &&
              zero.invariantHolds() && large_negated.invariantHolds(),
          "negated word values stay canonical");
  require(fraction(negated) == "7/3" && fraction(rotating) == "-5/8" &&
              fraction(zero) == "0" && fraction(large_negated) == "2147483647/2",
          "negated word values print as expected");

  /* A value too wide for the word state still negates through IMath. */
  ExactRational const wide = ExactRational::parseDecimalOrFraction(
      std::string(120, '9') + "/" + std::string(60, '7'));
  ExactRational const wide_negated = -wide;
  require(wide_negated.sign() == -wide.sign() && wide_negated != wide,
          "wide negation still flips the sign");
  require(-wide_negated == wide, "wide negation round trip");
  require(budget.metrics().allocation_calls > before,
          "the wide value did reach the allocator");
}

void testIntegerHelpers()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  ExactRational positive = ExactRational::parseDecimalOrFraction("7/3");
  ExactRational negative = ExactRational::parseDecimalOrFraction("-1/3");
  require(fraction(positive.floor()) == "2" &&
              fraction(positive.ceil()) == "3",
          "positive floor and ceil");
  require(fraction(negative.floor()) == "-1" &&
              fraction(negative.ceil()) == "0",
          "negative floor and ceil");
  require(fraction(positive.ceil() - positive.floor()) == "1",
          "ceil-floor property");

  ExactRational a(std::int64_t{-17});
  ExactRational b(std::int64_t{5});
  ExactRational negative_divisor(std::int64_t{-5});
  require(fraction(stp::lra::floorIntegerDivide(a, b)) == "-4",
          "floor integer division negative dividend");
  require(fraction(stp::lra::floorIntegerDivide(a, negative_divisor)) == "3",
          "floor integer division negative divisor");
  require(fraction(a.integerModulo(b)) == "3", "positive-divisor modulo");
  require(fraction(a.integerModulo(negative_divisor)) == "-2",
          "negative-divisor modulo");
  require(fraction(stp::lra::exactIntegerDivide(
                       ExactRational(std::int64_t{84}),
                       ExactRational(std::int64_t{-7}))) == "-12",
          "exact integer divide");
  expectFailure(NumberFailureKind::NonIntegerOperand,
                "failed exact integer divide",
                [&] { (void)stp::lra::exactIntegerDivide(a, b); });
  require(fraction(stp::lra::integerGcd(
                       ExactRational(std::int64_t{-84}),
                       ExactRational(std::int64_t{30}))) == "6",
          "signed gcd");
  require(fraction(stp::lra::integerLcm(
                       ExactRational(std::int64_t{-21}),
                       ExactRational(std::int64_t{6}))) == "42",
          "signed lcm");
  require(fraction(stp::lra::integerGcd(
                       ExactRational(std::int64_t{0}),
                       ExactRational(std::int64_t{0}))) == "0",
          "gcd zero");
  require(fraction(stp::lra::integerLcm(
                       ExactRational(std::int64_t{0}),
                       ExactRational(std::int64_t{9}))) == "0",
          "lcm zero");
  expectFailure(NumberFailureKind::NonIntegerOperand,
                "noninteger modulo",
                [&] { (void)positive.integerModulo(b); });
  expectFailure(NumberFailureKind::DivisionByZero,
                "integer helper zero divisor",
                [&] {
                  (void)stp::lra::floorIntegerDivide(
                      a, ExactRational(std::int64_t{0}));
                });
}

void testAllocatorContract()
{
  stp_lra_imath_budget_state state;
  stp_lra_imath_budget_init(&state, unlimited);
  state.allocation_calls = unlimited;
  state.allocated_bytes = unlimited - 1;
  require(stp_lra_imath_exchange_active_budget(&state) == nullptr,
          "direct allocator scope starts empty");
  require(stp_lra_imath_exchange_allocation_site(
              STP_LRA_IMATH_ALLOCATION_PARSE) ==
              STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED,
          "direct allocation site starts unattributed");
  void* pointer = stp_lra_imath_malloc(32);
  require(pointer != nullptr, "direct allocation");
  require(reinterpret_cast<std::uintptr_t>(pointer) % alignof(std::max_align_t) ==
              0,
          "max_align_t allocation alignment");
  require(stp_lra_imath_allocation_alignment() >= alignof(std::max_align_t),
          "reported allocation alignment");
  require(state.allocation_calls == unlimited &&
              state.allocated_bytes == unlimited,
          "allocation metrics saturate");
  std::memset(pointer, 0x5a, 32);
  pointer = stp_lra_imath_realloc(pointer, 48);
  require(pointer != nullptr, "direct realloc");
  auto const* bytes = static_cast<unsigned char const*>(pointer);
  require(std::all_of(bytes, bytes + 32,
                      [](unsigned char byte) { return byte == 0x5a; }),
          "realloc preserves contents");
  require(stp_lra_imath_exchange_allocation_site(
              STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED) ==
              STP_LRA_IMATH_ALLOCATION_PARSE,
          "direct allocation site restoration");
  require(state.allocation_calls_by_site[STP_LRA_IMATH_ALLOCATION_PARSE] == 2 &&
              state.allocated_bytes_by_site
                      [STP_LRA_IMATH_ALLOCATION_PARSE] == 80,
          "direct allocation site accounting");
  require(stp_lra_imath_exchange_active_budget(nullptr) == &state,
          "direct allocator scope restoration");
  stp_lra_imath_free(pointer);
  require(state.live_bytes == 0, "free outside active scope accounting");
  stp_lra_imath_free(nullptr);

  stp_lra_imath_budget_init(&state, 64);
  stp_lra_imath_exchange_active_budget(&state);
  pointer = stp_lra_imath_malloc(32);
  require(pointer != nullptr, "limited direct allocation");
  std::memset(pointer, 0x33, 32);
  void* failed = stp_lra_imath_realloc(pointer, 65);
  require(failed == nullptr &&
              stp_lra_imath_last_failure() ==
                  STP_LRA_IMATH_FAILURE_RESOURCE_LIMIT,
          "realloc cap refusal classification");
  bytes = static_cast<unsigned char const*>(pointer);
  require(std::all_of(bytes, bytes + 32,
                      [](unsigned char byte) { return byte == 0x33; }),
          "failed realloc preserves original");
  stp_lra_imath_exchange_active_budget(nullptr);
  stp_lra_imath_free(pointer);
  require(state.live_bytes == 0, "failed realloc remains balanced");
}

void testResourceLimitsAndScopes()
{
  expectFailure(NumberFailureKind::InternalError, "no-scope construction",
                [] { ExactRational value; });

  NumberBudget owner(generousLimits());
  std::optional<ExactRational> seven;
  std::optional<ExactRational> eight;
  {
    NumberOperationScope scope(owner);
    seven.emplace(std::int64_t{7});
    eight.emplace(std::int64_t{8});
  }

  NumberBudget exact_limit(
      NumberLimits{3, 16, UINT64_C(1048576), UINT64_C(1024)});
  {
    NumberOperationScope scope(exact_limit);
    require(seven->compare(*seven) == 0, "exact-at-limit operand");
    expectFailure(NumberFailureKind::ResourceLimit,
                  "one-bit-over operand",
                  [&] { (void)eight->compare(*eight); });
    require(exact_limit.stopped(), "operand refusal marks stopped");
  }
  exact_limit.resetAccounting();
  require(!exact_limit.stopped(), "reset clears stopped state");

  NumberBudget estimate_overflow(generousLimits());
  {
    NumberOperationScope scope(estimate_overflow);
    expectFailure(NumberFailureKind::ResourceLimit,
                  "checked estimate overflow",
                  [] { stp::lra::detail::testEstimateOverflow(); });
    require(estimate_overflow.metrics().preflight_stops == 1,
            "estimate overflow preflight metric");
  }

  auto expectOperationPreflight = [&](char const* label,
                                      std::uint64_t result_bits,
                                      auto&& operation) {
    NumberBudget limited(
        NumberLimits{64, result_bits, UINT64_C(1048576), UINT64_C(1024)});
    NumberOperationScope scope(limited);
    expectFailure(NumberFailureKind::ResourceLimit, label, operation);
    require(limited.metrics().preflight_stops == 1 && limited.stopped(),
            std::string(label) + " stop accounting");
  };
  expectOperationPreflight("addition cross-product preflight", 4,
                           [&] { (void)(*seven + *seven); });
  expectOperationPreflight("multiplication preflight", 5,
                           [&] { (void)(*seven * *seven); });
  expectOperationPreflight("comparison cross-product preflight", 3,
                           [&] { (void)seven->compare(*seven); });
  expectOperationPreflight("division preflight", 3,
                           [&] { (void)(*seven / *seven); });

  NumberBudget post_limit(
      NumberLimits{64, 2, UINT64_C(1048576), UINT64_C(1024)});
  {
    NumberOperationScope scope(post_limit);
    expectFailure(NumberFailureKind::ResourceLimit, "post-result exact cap",
                  [&] { stp::lra::detail::testPostResultLimit(*seven); });
    require(post_limit.stopped(), "post-result cap marks stopped");
  }

  NumberBudget zero_operand(
      NumberLimits{0, 16, UINT64_C(1048576), UINT64_C(1024)});
  {
    NumberOperationScope scope(zero_operand);
    expectFailure(NumberFailureKind::ResourceLimit, "zero operand cap",
                  [&] { (void)seven->compare(*seven); });
  }

  NumberBudget string_exact(
      NumberLimits{64, 64, UINT64_C(1048576), 2});
  {
    NumberOperationScope scope(string_exact);
    ExactRational one = ExactRational::parseDecimalOrFraction("1");
    require(fraction(one) == "1", "exact string cap including terminator");
  }
  NumberBudget string_short(
      NumberLimits{64, 64, UINT64_C(1048576), 1});
  {
    NumberOperationScope scope(string_short);
    expectFailure(NumberFailureKind::ResourceLimit, "input string cap",
                  [] { (void)ExactRational::parseDecimalOrFraction("1"); });
  }
  NumberBudget output_short(
      NumberLimits{64, 64, UINT64_C(1048576), 3});
  {
    NumberOperationScope scope(output_short);
    expectFailure(NumberFailureKind::ResourceLimit, "output string cap",
                  [&] { (void)seven->canonicalFraction(); });
  }

  NumberBudget allocation_limited(
      NumberLimits{8192, 8192, 1, UINT64_C(8192)});
  {
    NumberOperationScope scope(allocation_limited);
    expectFailure(NumberFailureKind::ResourceLimit, "allocation byte cap",
                  [] {
                    (void)ExactRational::parseDecimalOrFraction(
                        std::string(500, '9'));
                  });
    require(allocation_limited.metrics().allocation_stops > 0,
            "allocation stop metric");
  }
  allocation_limited.resetAccounting();
  require(!allocation_limited.stopped(), "allocation stop recovery reset");
  {
    NumberOperationScope scope(allocation_limited);
    ExactRational zero;
    require(zero.isZero(), "recovery after configured allocation refusal");
  }

  NumberBudget first(generousLimits());
  NumberBudget second(generousLimits());
  {
    NumberOperationScope outer(first);
    {
      NumberOperationScope nested(first);
      ExactRational one(std::int64_t{1});
      require(one.isOne(), "nested same-budget scope");
    }
    expectFailure(NumberFailureKind::InternalError,
                  "nested different-budget scope",
                  [&] { NumberOperationScope invalid(second); });
    ExactRational recovered(std::int64_t{2});
    require(fraction(recovered) == "2",
            "scope restored after nested-scope exception");
  }

  NumberBudget active_reset(generousLimits());
  {
    NumberOperationScope scope(active_reset);
    active_reset.resetAccounting();
    require(active_reset.stopped(),
            "reset during an active scope fails closed");
  }
  active_reset.resetAccounting();
  require(!active_reset.stopped(),
          "inactive reset recovers after active-scope refusal");

  NumberBudget reset_budget(generousLimits());
  std::optional<ExactRational> live;
  {
    NumberOperationScope scope(reset_budget);
    live.emplace(ExactRational::parseDecimalOrFraction(
        "123456789012345678901234567890"));
  }
  reset_budget.resetAccounting();
  require(reset_budget.metrics().current_values == 1 &&
              reset_budget.metrics().peak_values == 1 &&
              !reset_budget.stopped(),
          "reset preserves live-value accounting");
  {
    NumberOperationScope scope(reset_budget);
    require(live->canonicalFraction() ==
                "123456789012345678901234567890",
            "live value survives reset");
  }
  live.reset();
  require(reset_budget.metrics().current_values == 0,
          "post-reset destruction accounting");

  NumberBudget strong_limit(
      NumberLimits{64, 4, UINT64_C(1048576), UINT64_C(1024)});
  std::optional<ExactRational> output;
  {
    NumberOperationScope scope(strong_limit);
    output.emplace(std::int64_t{3});
    expectFailure(NumberFailureKind::ResourceLimit,
                  "addition preflight strong commit",
                  [&] { stp::lra::add(*output, *seven, *seven); });
  }
  {
    NumberOperationScope scope(owner);
    require(fraction(*output) == "3", "out value unchanged on refusal");
    require(fraction(*seven) == "7", "operand unchanged on refusal");
  }
  output.reset();
  seven.reset();
  eight.reset();
}

/* The canonical-form self-check is a run-time switch, not a compile-time one,
 * so the solver and this test exercise the same object code. Two things have
 * to hold for that to be worth anything: a budget verifies unless something
 * turns it off -- which is what gives every test and every API caller the
 * check without asking -- and turning it off actually stops the work. The
 * second is measured through the canonicalize allocation site, which is where
 * the re-derivation allocates. */
void testCanonicalVerificationSwitch()
{
  require(NumberBudget::canonicalVerificationDefault(),
          "a budget verifies canonical results unless told otherwise");

  auto exercise = [](NumberBudget& budget) {
    NumberOperationScope scope(budget);
    ExactRational total(std::int64_t{0});
    for (std::int64_t step = 1; step != 60; ++step)
    {
      ExactRational term = ExactRational::parseDecimalOrFraction(
          std::to_string(step) + "/" + std::to_string(step + 1));
      total += term;
      total = -total;
      total *= term;
    }
    return total.canonicalFraction().size();
  };

  std::uint64_t verified = 0;
  std::uint64_t skipped = 0;
  {
    NumberBudget budget(generousLimits());
    (void)exercise(budget);
    verified = allocationSite(budget.metrics(),
                              STP_LRA_IMATH_ALLOCATION_CANONICALIZE).calls;
  }
  NumberBudget::setCanonicalVerificationDefault(false);
  {
    NumberBudget budget(generousLimits());
    (void)exercise(budget);
    skipped = allocationSite(budget.metrics(),
                             STP_LRA_IMATH_ALLOCATION_CANONICALIZE).calls;
  }
  NumberBudget::setCanonicalVerificationDefault(true);

  require(verified > skipped,
          "turning canonical verification off stops the re-derivation");
  require(NumberBudget::canonicalVerificationDefault(),
          "the default is restored for whatever runs next");
}

void runUnitMode()
{
  testCanonicalVerificationSwitch();
  testConstructionAndOwnership();
  testParsingAndCanonicalization();
  testArithmetic();
  testBackendNeutralOptimizations();
  testComparisonHashAndSmall();
  testIntegerHelpers();
  testNegationStaysWordSized();
  testAllocatorContract();
  testResourceLimitsAndScopes();
  std::cout << "{\"mode\":\"unit\",\"passed\":true}" << std::endl;
}

void faultWorkload(ExactRational const& seed,
                   ExactRational const& multiplier,
                   ExactRational& retained_out,
                   unsigned rounds)
{
  for (unsigned round = 0; round != rounds; ++round)
  {
    std::string digits(180 + (round % 5), static_cast<char>('5' + round % 4));
    ExactRational parsed = ExactRational::parseDecimalOrFraction(
        digits + "/123456789012345678901234567890123456789");
    std::string const out_before = retained_out.canonicalFraction();
    try
    {
      stp::lra::add(retained_out, parsed, seed);
    }
    catch (...)
    {
      require(retained_out.canonicalFraction() == out_before &&
                  retained_out.invariantHolds(),
              "faulting out-parameter operation has strong commit");
      throw;
    }
    ExactRational sum = retained_out;
    ExactRational product = sum * multiplier;
    ExactRational recovered = product / multiplier;
    require(recovered == sum, "fault workload cancellation");
    require(product.compare(parsed) != 0, "fault workload comparison");
    require(!product.canonicalFraction().empty(), "fault workload output");
    require(product.stableHash() != 0, "fault workload hash");
    ExactRational integer = product.floor();
    require(integer.isInteger(), "fault workload floor");
  }
}

std::uint64_t measureFaultAttempts(unsigned rounds)
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  ExactRational seed = ExactRational::parseDecimalOrFraction("7/13");
  ExactRational multiplier = ExactRational::parseDecimalOrFraction("19/23");
  ExactRational retained_out(std::int64_t{41});
  (void)seed.canonicalFraction();
  (void)multiplier.canonicalFraction();
  stp_lra_imath_test_fail_nth(unlimited);
  faultWorkload(seed, multiplier, retained_out, rounds);
  std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
  stp_lra_imath_test_disable_failures();
  return attempts;
}

void runFaultMode()
{
  unsigned const rounds = 8;
  std::uint64_t const attempts = measureFaultAttempts(rounds);
  require(attempts >= 96, "fault workload must expose at least 96 points");
  std::uint64_t injected = 0;
  for (std::uint64_t index = 0; index != attempts; ++index)
  {
    NumberBudget budget(generousLimits());
    NumberOperationScope scope(budget);
    ExactRational seed = ExactRational::parseDecimalOrFraction("7/13");
    ExactRational multiplier = ExactRational::parseDecimalOrFraction("19/23");
    ExactRational retained_out(std::int64_t{41});
    std::string const seed_before = seed.canonicalFraction();
    std::string const multiplier_before = multiplier.canonicalFraction();
    stp_lra_imath_test_fail_nth(index);
    try
    {
      faultWorkload(seed, multiplier, retained_out, rounds);
      fail("injected allocation point did not fail at index " +
           std::to_string(index) + " after " +
           std::to_string(stp_lra_imath_test_allocation_attempts()) +
           " attempts (baseline " + std::to_string(attempts) + ")");
    }
    catch (NumberFailure const& failure)
    {
      require(
          failure.kind() == NumberFailureKind::AllocationFailure,
          "fault injection classification at index " +
              std::to_string(index) + ", kind " +
              std::to_string(static_cast<unsigned>(failure.kind())) +
              ", operation " +
              (failure.operation() == nullptr ? "<null>" :
                                                failure.operation()) +
              ", message " + failure.what());
      ++injected;
    }
    stp_lra_imath_test_disable_failures();
    require(seed.canonicalFraction() == seed_before &&
                multiplier.canonicalFraction() == multiplier_before &&
                seed.invariantHolds() && multiplier.invariantHolds() &&
                retained_out.invariantHolds(),
            "fault leaves operands valid and unchanged");
    ExactRational recovery = seed * multiplier;
    require(recovery.invariantHolds(), "recovery after injected failure");
  }

  stp_lra_imath_test_fail_nth(0);
  std::atomic<bool> other_thread_passed{false};
  std::thread unaffected([&] {
    try
    {
      NumberBudget budget(generousLimits());
      NumberOperationScope scope(budget);
      ExactRational value =
          ExactRational::parseDecimalOrFraction("12345678901234567890/7");
      other_thread_passed = value.invariantHolds();
    }
    catch (...)
    {
      other_thread_passed = false;
    }
  });
  unaffected.join();
  stp_lra_imath_test_disable_failures();
  require(other_thread_passed, "fault injection is thread-local");
  std::cout << "{\"mode\":\"fault\",\"passed\":true,"
               "\"allocation_points\":"
            << attempts << ",\"injected_failures\":" << injected
            << ",\"recovery\":true,\"other_thread_unaffected\":true}"
            << std::endl;
}

void runHugeMode()
{
  std::string const numerator(1235, '9');
  std::string const denominator(618, '9');
  NumberBudget budget(generousLimits());
  std::uint64_t peak_live = 0;
  {
    NumberOperationScope scope(budget);
    ExactRational value =
        ExactRational::fromCanonicalIntegers(numerator, denominator);
    require(value.numeratorBits() >= 4098 && value.numeratorBits() <= 4105,
            "huge numerator scale");
    require(value.denominatorBits() >= 2048 &&
                value.denominatorBits() <= 2055,
            "huge denominator scale");
    ExactRational inverse = value.inverse();
    ExactRational product = value * inverse;
    require(product.isOne(), "huge multiplication cancellation");
    require((value / value).isOne(), "huge division cancellation");
    require(value.compare(value) == 0, "huge comparison");
    require(value.invariantHolds(), "huge canonical invariant");
    require(value.canonicalFraction().find('/') != std::string::npos,
            "huge canonical output");
    require(value.stableHash() != 0, "huge stable hash");
    peak_live = budget.metrics().peak_live_bytes;
  }
  require(budget.metrics().current_values == 0,
          "huge live values return to baseline");
  require(peak_live > 0, "huge allocation evidence");

  std::uint64_t construction_peak = 0;
  NumberBudget measurement(generousLimits());
  {
    NumberOperationScope scope(measurement);
    ExactRational value =
        ExactRational::fromCanonicalIntegers(numerator, denominator);
    require(value.invariantHolds(), "huge construction peak fixture");
    construction_peak = measurement.metrics().peak_live_bytes;
  }
  require(construction_peak > 0, "huge construction allocation evidence");

  NumberLimits below_limits = generousLimits();
  below_limits.maximum_allocation_bytes = construction_peak - 1;
  NumberBudget below(below_limits);
  {
    NumberOperationScope scope(below);
    expectFailure(NumberFailureKind::ResourceLimit,
                  "huge allocation just below observed peak",
                  [&] {
                    (void)ExactRational::fromCanonicalIntegers(numerator,
                                                               denominator);
                  });
  }
  NumberLimits above_limits = generousLimits();
  above_limits.maximum_allocation_bytes = construction_peak;
  NumberBudget above(above_limits);
  {
    NumberOperationScope scope(above);
    ExactRational value =
        ExactRational::fromCanonicalIntegers(numerator, denominator);
    require(value.invariantHolds(), "huge allocation exact observed peak");
  }
  std::cout << "{\"mode\":\"huge\",\"passed\":true,"
               "\"numerator_digits\":1235,\"denominator_digits\":618,"
               "\"peak_live_bytes\":"
            << peak_live << ",\"construction_peak_live_bytes\":"
            << construction_peak << "}" << std::endl;
}

void concurrencyWorkload(unsigned thread_index)
{
  NumberBudget budget(generousLimits());
  for (unsigned workload = 0; workload != 100; ++workload)
  {
    NumberOperationScope outer(budget);
    NumberOperationScope nested(budget);
    std::string const numerator =
        std::to_string(UINT64_C(1000003) * (thread_index + 1) + workload);
    ExactRational left = ExactRational::fromCanonicalIntegers(
        numerator, std::to_string(2 * workload + 1));
    ExactRational right = ExactRational::parseDecimalOrFraction("17/29");
    ExactRational result = (left + right) * right.inverse();
    require(result.invariantHolds(), "concurrent arithmetic invariant");
    require(result.compare(result) == 0, "concurrent comparison");
    require(result.stableHash() != 0, "concurrent hash");
    if (workload % 17 == 0)
    {
      expectFailure(NumberFailureKind::DivisionByZero,
                    "concurrent typed failure",
                    [&] {
                      (void)(result / ExactRational(std::int64_t{0}));
                    });
    }
  }
  require(budget.metrics().current_values == 0,
          "concurrent value accounting returns to zero");
}

void runConcurrencyMode()
{
  std::atomic<unsigned> passed{0};
  std::vector<std::thread> threads;
  for (unsigned index = 0; index != 8; ++index)
  {
    threads.emplace_back([&, index] {
      try
      {
        concurrencyWorkload(index);
        ++passed;
      }
      catch (std::exception const& error)
      {
        std::cerr << "thread " << index << ": " << error.what() << '\n';
      }
    });
  }
  for (std::thread& thread : threads)
  {
    thread.join();
  }
  require(passed == 8, "8 x 100 concurrency workloads");
  std::cout << "{\"mode\":\"concurrency\",\"passed\":true,"
               "\"threads\":8,\"workloads_per_thread\":100}"
            << std::endl;
}

void runPerformanceMode()
{
  using Clock = std::chrono::steady_clock;
  constexpr unsigned iterations = 5000;
  NumberBudget budget(generousLimits());
  std::uint64_t checksum = 0;
  std::uint64_t comparison_ns = 0;
  std::uint64_t hash_ns = 0;
  std::uint64_t string_ns = 0;
  std::uint64_t arithmetic_ns = 0;
  std::uint64_t gcd_ns = 0;
  {
    NumberOperationScope scope(budget);
    ExactRational left = ExactRational::fromCanonicalIntegers(
        std::string(180, '9'), "123456789012345678901234567890123456789");
    ExactRational right = ExactRational::parseDecimalOrFraction(
        "987654321098765432109876543210987654321/100000000000000000003");
    auto start = Clock::now();
    for (unsigned index = 0; index != iterations; ++index)
    {
      checksum ^= static_cast<std::uint64_t>(left.compare(right) + 1);
    }
    comparison_ns = static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start)
            .count());

    start = Clock::now();
    for (unsigned index = 0; index != iterations; ++index)
    {
      checksum ^= left.stableHash();
    }
    hash_ns = static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start)
            .count());

    start = Clock::now();
    for (unsigned index = 0; index != iterations; ++index)
    {
      checksum += left.canonicalFraction().size();
    }
    string_ns = static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start)
            .count());

    ExactRational accumulator = left;
    start = Clock::now();
    for (unsigned index = 0; index != iterations; ++index)
    {
      accumulator += right;
      accumulator -= right;
    }
    arithmetic_ns = static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start)
            .count());
    checksum ^= accumulator.stableHash();

    ExactRational gcd_left = ExactRational::parseDecimalOrFraction(
        "1234567890123456789012345678901234567890");
    ExactRational gcd_right = ExactRational::parseDecimalOrFraction(
        "987654321098765432109876543210");
    start = Clock::now();
    for (unsigned index = 0; index != iterations; ++index)
    {
      checksum ^= stp::lra::integerGcd(gcd_left, gcd_right).stableHash();
    }
    gcd_ns = static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start)
            .count());
  }
  auto const metrics = budget.metrics();
  require(metrics.current_values == 0,
          "performance workload returns live values to zero");
  std::cout << "{\"mode\":\"performance\",\"passed\":true,"
               "\"iterations\":"
            << iterations << ",\"comparison_ns\":" << comparison_ns
            << ",\"hash_ns\":" << hash_ns << ",\"string_ns\":"
            << string_ns << ",\"arithmetic_ns\":" << arithmetic_ns
            << ",\"gcd_ns\":" << gcd_ns << ",\"checksum\":"
            << checksum << ",\"allocation_calls\":"
            << metrics.allocation_calls << ",\"allocated_bytes\":"
            << metrics.allocated_bytes << ",\"canonicalizations\":"
            << metrics.canonicalizations << ",\"gcd_operations\":"
            << metrics.gcds << ",\"maximum_numerator_bits\":"
            << metrics.maximum_numerator_bits
            << ",\"maximum_denominator_bits\":"
            << metrics.maximum_denominator_bits;
  writeNativeMetrics(std::cout, metrics);
  std::cout << "}" << std::endl;
}

std::vector<std::string> splitCorpusRow(std::string const& line)
{
  std::vector<std::string> fields;
  std::size_t begin = 0;
  for (;;)
  {
    std::size_t const tab = line.find('\t', begin);
    if (tab == std::string::npos)
    {
      fields.push_back(line.substr(begin));
      return fields;
    }
    fields.push_back(line.substr(begin, tab - begin));
    begin = tab + 1;
  }
}

std::string evaluateCorpusRow(std::string const& operation,
                              std::string const& left_text,
                              std::string const& right_text)
{
  try
  {
    ExactRational left = ExactRational::parseDecimalOrFraction(left_text);
    if (operation == "floor") return left.floor().canonicalFraction();
    if (operation == "ceil") return left.ceil().canonicalFraction();
    if (operation == "canonical") return left.canonicalFraction();
    if (operation == "numerator") return left.numeratorDecimal();
    if (operation == "denominator") return left.denominatorDecimal();
    ExactRational right = ExactRational::parseDecimalOrFraction(right_text);
    if (operation == "add") return (left + right).canonicalFraction();
    if (operation == "sub") return (left - right).canonicalFraction();
    if (operation == "mul") return (left * right).canonicalFraction();
    if (operation == "div") return (left / right).canonicalFraction();
    if (operation == "cmp") return std::to_string(left.compare(right));
    return "ERROR";
  }
  catch (NumberFailure const&)
  {
    return "ERROR";
  }
}

void runCorpusMode(std::string const& input_path,
                   std::string const& output_path)
{
  std::ifstream input(input_path);
  std::ofstream output(output_path, std::ios::trunc);
  require(input.good(), "open differential corpus");
  require(output.good(), "open differential output");
  NumberBudget budget(generousLimits());
  std::string line;
  std::uint64_t records = 0;
  while (std::getline(input, line))
  {
    std::vector<std::string> const fields = splitCorpusRow(line);
    require(fields.size() == 3, "three-column differential corpus row");
    std::string result;
    {
      NumberOperationScope scope(budget);
      result = evaluateCorpusRow(fields[0], fields[1], fields[2]);
    }
    output << records << '\t' << result << '\n';
    ++records;
  }
  require(records == 20006, "pinned differential record count");
  require(output.good(), "write differential output");
  require(budget.metrics().current_values == 0,
          "corpus live-value accounting");
  NumberMetrics const metrics = budget.metrics();
  std::cout << "{\"mode\":\"corpus\",\"passed\":true,"
               "\"operations\":"
            << records << ",\"allocation_calls\":"
            << metrics.allocation_calls << ",\"allocated_bytes\":"
            << metrics.allocated_bytes;
  writeNativeMetrics(std::cout, metrics);
  std::cout << "}" << std::endl;
}

}  // namespace

int main(int argc, char** argv)
{
  try
  {
    if (argc < 2)
    {
      fail("usage: exact_rational_tests MODE [CORPUS OUTPUT]");
    }
    std::string const mode(argv[1]);
    if (mode == "unit")
    {
      runUnitMode();
    }
    else if (mode == "fault")
    {
      runFaultMode();
    }
    else if (mode == "huge")
    {
      runHugeMode();
    }
    else if (mode == "concurrency")
    {
      runConcurrencyMode();
    }
    else if (mode == "performance")
    {
      runPerformanceMode();
    }
    else if (mode == "corpus" && argc == 4)
    {
      runCorpusMode(argv[2], argv[3]);
    }
    else
    {
      fail("unknown or incomplete test mode");
    }
  }
  catch (std::exception const& error)
  {
    std::cerr << "FAIL: " << error.what() << '\n';
    return 1;
  }
  return 0;
}

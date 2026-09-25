#include "ExactRational.h"
#include "PortableBits.h"

#include <algorithm>
#include <charconv>
#include <climits>
#include <limits>
#include <new>
#include <utility>

namespace stp::lra {

namespace detail {

/* Defined below, once the word helpers are in scope.  Turns a word-state
 * rational into a big-state one; a no-op when it already is one. */
void materializeRational(ExactRational const& value, char const* operation);

struct ExactRationalAccess
{
  /* Asking for the native representation is what forces materialisation, so
   * these are not noexcept.  Every noexcept member of ExactRational answers
   * from the word state instead of coming through here. */
  static mp_rat native(ExactRational const& value)
  {
    materializeRational(value, "materialize");
    return &value.big_->value;
  }
  static bool isWord(ExactRational const& value) noexcept
  {
    return value.big_ == nullptr;
  }
  static std::int64_t wordNumerator(ExactRational const& value) noexcept
  {
    return value.numerator_;
  }
  static std::int64_t wordDenominator(ExactRational const& value) noexcept
  {
    return value.denominator_;
  }
  static BigRational* big(ExactRational const& value) noexcept
  {
    return value.big_;
  }
  /* Write a canonical word result in place.  Any big form the target held
   * is released first, with its own budget's accounting. */
  static void setWord(ExactRational& value,
                      std::int64_t numerator,
                      std::int64_t denominator) noexcept
  {
    value.releaseBig();
    value.numerator_ = numerator;
    value.denominator_ = denominator;
  }
  /* Hand a fresh, zero-valued big form to a word-state value. */
  static void adoptBig(ExactRational& value, BigRational* big) noexcept
  {
    value.big_ = big;
  }
  static void dropBig(ExactRational const& value,
                      std::int64_t numerator,
                      std::int64_t denominator) noexcept
  {
    value.big_ = nullptr;
    value.numerator_ = numerator;
    value.denominator_ = denominator;
  }
};

}  // namespace detail

namespace {

using detail::BigRational;
using detail::BudgetAccess;
using detail::ExactRationalAccess;
using detail::NumberMetricEvent;

[[noreturn]] void throwStandardAllocation(char const* operation)
{
  throw NumberFailure(NumberFailureKind::AllocationFailure,
                      operation,
                      "standard-library allocation failed");
}

void checkNativeResult(mp_result result,
                       char const* operation,
                       NumberFailureKind undefined_kind =
                           NumberFailureKind::InternalError)
{
  if (result == MP_OK)
  {
    return;
  }
  if (result == MP_MEMORY)
  {
    throw BudgetAccess::allocationFailure(operation, mp_error_string(result));
  }
  if (result == MP_UNDEF)
  {
    throw NumberFailure(undefined_kind, operation, mp_error_string(result));
  }
  if (result == MP_RANGE)
  {
    throw NumberFailure(NumberFailureKind::RangeError,
                        operation,
                        mp_error_string(result));
  }
  throw NumberFailure(NumberFailureKind::InternalError,
                      operation,
                      mp_error_string(result));
}

template <class Function>
void checkedNative(char const* operation,
                   Function&& function,
                   NumberFailureKind undefined_kind =
                       NumberFailureKind::InternalError)
{
  stp_lra_imath_clear_failure();
  mp_result const result = function();
  if (result == MP_OK &&
      stp_lra_imath_last_failure() != STP_LRA_IMATH_FAILURE_NONE)
  {
    throw BudgetAccess::allocationFailure(
        operation, "native call returned success after allocator failure");
  }
  checkNativeResult(result, operation, undefined_kind);
}

class NativeInteger final
{
 public:
  explicit NativeInteger(char const* operation)
  {
    checkedNative(operation, [this] { return mp_int_init(&value); });
  }
  NativeInteger(NativeInteger const&) = delete;
  NativeInteger& operator=(NativeInteger const&) = delete;
  ~NativeInteger() noexcept { mp_int_clear(&value); }

  imath_int_value value;
};

class AllocationSiteScope final
{
 public:
  explicit AllocationSiteScope(stp_lra_imath_allocation_site site) noexcept
      : previous_(stp_lra_imath_exchange_allocation_site(site))
  {
  }
  AllocationSiteScope(AllocationSiteScope const&) = delete;
  AllocationSiteScope& operator=(AllocationSiteScope const&) = delete;
  ~AllocationSiteScope() noexcept
  {
    (void)stp_lra_imath_exchange_allocation_site(previous_);
  }

 private:
  stp_lra_imath_allocation_site previous_;
};

std::uint64_t checkedAdd(std::uint64_t left,
                         std::uint64_t right,
                         void* state,
                         char const* operation,
                         char const* estimate)
{
  if (std::numeric_limits<std::uint64_t>::max() - left < right)
  {
    BudgetAccess::preflightStop(state, operation,
                                std::string(estimate) + " overflow");
  }
  return left + right;
}

std::uint64_t checkedMultiply(std::uint64_t left,
                              std::uint64_t right,
                              void* state,
                              char const* operation,
                              char const* estimate)
{
  if (left != 0 &&
      right > std::numeric_limits<std::uint64_t>::max() / left)
  {
    BudgetAccess::preflightStop(state, operation,
                                std::string(estimate) + " overflow");
  }
  return left * right;
}

void checkConfiguredMaximum(std::uint64_t value,
                            std::uint64_t maximum,
                            void* state,
                            char const* operation,
                            char const* description)
{
  if (value > maximum)
  {
    BudgetAccess::preflightStop(
        state, operation,
        std::string(description) + " exceeds configured maximum");
  }
}

void checkResultEstimate(std::uint64_t numerator_bits,
                         std::uint64_t denominator_bits,
                         void* state,
                         char const* operation)
{
  // Word-sized estimates cannot cross limits that admit words at all.
  if (BudgetAccess::wordUnlimited(state) && numerator_bits <= 126 &&
      denominator_bits <= 126)
    return;
  NumberLimits const limits = BudgetAccess::limits(state);
  checkConfiguredMaximum(numerator_bits, limits.maximum_result_bits, state,
                         operation, "estimated numerator bits");
  checkConfiguredMaximum(denominator_bits, limits.maximum_result_bits, state,
                         operation, "estimated denominator bits");
}

void checkOperand(ExactRational const& value,
                  void* state,
                  char const* operation)
{
  if (BudgetAccess::wordUnlimited(state) && ExactRationalAccess::isWord(value))
    return;
  NumberLimits const limits = BudgetAccess::limits(state);
  checkConfiguredMaximum(value.numeratorBits(), limits.maximum_operand_bits,
                         state, operation, "numerator operand bits");
  checkConfiguredMaximum(value.denominatorBits(), limits.maximum_operand_bits,
                         state, operation, "denominator operand bits");
}

void checkStringBytes(std::uint64_t bytes,
                      void* state,
                      char const* operation,
                      char const* description)
{
  checkConfiguredMaximum(bytes,
                         BudgetAccess::limits(state).maximum_string_bytes,
                         state,
                         operation,
                         description);
}

bool unsignedDecimal(std::string_view text) noexcept
{
  if (text.empty())
  {
    return false;
  }
  for (char byte : text)
  {
    if (byte < '0' || byte > '9')
    {
      return false;
    }
  }
  return true;
}

bool signedDecimalInteger(std::string_view text) noexcept
{
  if (text.empty() || text.front() == '+')
  {
    return false;
  }
  if (text.front() == '-')
  {
    text.remove_prefix(1);
  }
  return unsignedDecimal(text);
}

bool decimalZero(std::string_view text) noexcept
{
  return std::all_of(text.begin(), text.end(), [](char byte) {
    return byte == '0';
  });
}

std::uint64_t estimatedIntegerBits(std::string_view text,
                                   void* state,
                                   char const* operation)
{
  if (!text.empty() && text.front() == '-')
  {
    text.remove_prefix(1);
  }
  std::size_t first = 0;
  while (first < text.size() && text[first] == '0')
  {
    ++first;
  }
  if (first == text.size())
  {
    return 1;
  }
  std::uint64_t const digits = static_cast<std::uint64_t>(text.size() - first);
  return checkedMultiply(digits, 4, state, operation,
                         "decimal bit estimate");
}

std::string ownedText(std::string_view text, char const* operation)
{
  try
  {
    return std::string(text);
  }
  catch (std::bad_alloc const&)
  {
    throwStandardAllocation(operation);
  }
}

void readInteger(mp_int output,
                 std::string_view text,
                 char const* operation)
{
  std::string const owned = ownedText(text, operation);
  checkedNative(operation, [&] {
    return mp_int_read_string(output, 10, owned.c_str());
  });
}

void preflightComponents(std::string_view numerator,
                         std::string_view denominator,
                         void* state,
                         char const* operation)
{
  std::uint64_t const numerator_bytes = checkedAdd(
      static_cast<std::uint64_t>(numerator.size()), 1, state, operation,
      "numerator component string size");
  std::uint64_t const denominator_bytes = checkedAdd(
      static_cast<std::uint64_t>(denominator.size()), 1, state, operation,
      "denominator component string size");
  checkStringBytes(numerator_bytes, state, operation,
                   "numerator component string bytes");
  checkStringBytes(denominator_bytes, state, operation,
                   "denominator component string bytes");
  std::uint64_t const numerator_bits =
      estimatedIntegerBits(numerator, state, operation);
  std::uint64_t const denominator_bits =
      estimatedIntegerBits(denominator, state, operation);
  NumberLimits const limits = BudgetAccess::limits(state);
  checkConfiguredMaximum(numerator_bits, limits.maximum_operand_bits, state,
                         operation, "numerator input bits");
  checkConfiguredMaximum(denominator_bits, limits.maximum_operand_bits, state,
                         operation, "denominator input bits");
  checkResultEstimate(numerator_bits, denominator_bits, state, operation);
}

bool checkedInvariant(mp_rat value, char const* operation)
{
  if (mp_int_compare_zero(MP_DENOM_P(value)) <= 0)
  {
    return false;
  }
  if (mp_int_compare_zero(MP_NUMER_P(value)) == 0)
  {
    return mp_int_compare_value(MP_DENOM_P(value), 1) == 0 &&
           MP_SIGN(MP_NUMER_P(value)) == MP_ZPOS;
  }
  NativeInteger gcd(operation);
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(value), MP_DENOM_P(value), &gcd.value);
  });
  return mp_int_compare_value(&gcd.value, 1) == 0 &&
         MP_SIGN(MP_DENOM_P(value)) == MP_ZPOS;
}

void postCheckImpl(mp_rat value,
                   void* state,
                   char const* operation,
                   bool known_canonical)
{
  std::uint64_t const numerator_bits = mp_int_count_bits(MP_NUMER_P(value));
  std::uint64_t const denominator_bits = mp_int_count_bits(MP_DENOM_P(value));
  NumberLimits const limits = BudgetAccess::limits(state);
  if (numerator_bits > limits.maximum_result_bits ||
      denominator_bits > limits.maximum_result_bits)
  {
    BudgetAccess::postResultStop(state, operation,
                                 "exact result exceeds configured bit limit");
  }
  bool const verify_invariant =
      !known_canonical || BudgetAccess::verifyCanonical(state);
  if (verify_invariant)
  {
    AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_CANONICALIZE);
    if (!checkedInvariant(value, operation))
    {
      throw NumberFailure(NumberFailureKind::InternalError,
                          operation,
                          "native rational is not canonical");
    }
  }
  BudgetAccess::record(state, NumberMetricEvent::Canonicalize);
  BudgetAccess::observeValue(state, numerator_bits, denominator_bits);
}

void postCheck(mp_rat value, void* state, char const* operation)
{
  postCheckImpl(value, state, operation, false);
}

void postCheckKnownCanonical(mp_rat value,
                             void* state,
                             char const* operation)
{
  postCheckImpl(value, state, operation, true);
}

void setFromComponents(mp_rat target,
                       std::string_view numerator,
                       std::string_view denominator,
                       char const* operation)
{
  NativeInteger native_numerator(operation);
  NativeInteger native_denominator(operation);
  readInteger(&native_numerator.value, numerator, operation);
  readInteger(&native_denominator.value, denominator, operation);
  checkedNative(operation,
                [&] {
                  return mp_rat_set(target, &native_numerator.value,
                                    &native_denominator.value);
                },
                NumberFailureKind::ZeroDenominator);
}

template <class Integer>
std::string_view integerCharacters(Integer value,
                                   char (&buffer)[64],
                                   char const* operation)
{
  auto const converted = std::to_chars(buffer, buffer + sizeof(buffer), value);
  if (converted.ec != std::errc{})
  {
    throw NumberFailure(NumberFailureKind::RangeError,
                        operation,
                        "fixed-width decimal conversion failed");
  }
  return {buffer, static_cast<std::size_t>(converted.ptr - buffer)};
}

std::uint64_t decimalBufferBytes(mp_int value,
                                 void* state,
                                 char const* operation)
{
  std::uint64_t required = mp_int_count_bits(value);
  if (MP_SIGN(value) == MP_NEG)
  {
    required = checkedAdd(required, 1, state, operation,
                          "decimal sign size");
  }
  return checkedAdd(required, 1, state, operation,
                    "decimal terminator size");
}

std::string integerDecimal(mp_int value,
                           void* state,
                           char const* operation)
{
  std::uint64_t const required =
      decimalBufferBytes(value, state, operation);
  checkStringBytes(required, state, operation, "output string bytes");
  if (required > static_cast<std::uint64_t>(INT_MAX))
  {
    throw NumberFailure(NumberFailureKind::RangeError,
                        operation,
                        "native string length exceeds int range");
  }
  std::string output;
  try
  {
    output.assign(static_cast<std::size_t>(required), '\0');
  }
  catch (std::bad_alloc const&)
  {
    throwStandardAllocation(operation);
  }
  checkedNative(operation, [&] {
    return mp_int_to_string(value, 10, output.data(),
                            static_cast<int>(required));
  });
  auto const terminator = std::find(output.begin(), output.end(), '\0');
  if (terminator == output.end())
  {
    throw NumberFailure(NumberFailureKind::InternalError,
                        operation,
                        "native decimal output is not terminated");
  }
  output.resize(static_cast<std::size_t>(terminator - output.begin()));
  return output;
}

/* A word component as decimal text, without going through IMath. */
std::string wordDecimal(std::int64_t value, char const* operation)
{
  char buffer[64];
  std::string_view const text = integerCharacters(value, buffer, operation);
  return ownedText(text, operation);
}

std::uint64_t bitSum(std::uint64_t left,
                     std::uint64_t right,
                     void* state,
                     char const* operation)
{
  return checkedAdd(left, right, state, operation, "bit estimate");
}

void preflightAddSubtract(ExactRational const& lhs,
                          ExactRational const& rhs,
                          void* state,
                          char const* operation)
{
  if (BudgetAccess::wordUnlimited(state) && ExactRationalAccess::isWord(lhs) &&
      ExactRationalAccess::isWord(rhs))
    return;
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  std::uint64_t const first =
      bitSum(lhs.numeratorBits(), rhs.denominatorBits(), state, operation);
  std::uint64_t const second =
      bitSum(rhs.numeratorBits(), lhs.denominatorBits(), state, operation);
  std::uint64_t const numerator = checkedAdd(
      std::max(first, second), 1, state, operation, "addition bit estimate");
  std::uint64_t const denominator =
      bitSum(lhs.denominatorBits(), rhs.denominatorBits(), state, operation);
  checkResultEstimate(numerator, denominator, state, operation);
}

void preflightMultiply(ExactRational const& lhs,
                       ExactRational const& rhs,
                       void* state,
                       char const* operation)
{
  if (BudgetAccess::wordUnlimited(state) && ExactRationalAccess::isWord(lhs) &&
      ExactRationalAccess::isWord(rhs))
    return;
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(
      bitSum(lhs.numeratorBits(), rhs.numeratorBits(), state, operation),
      bitSum(lhs.denominatorBits(), rhs.denominatorBits(), state, operation),
      state, operation);
}

void preflightDivide(ExactRational const& lhs,
                     ExactRational const& rhs,
                     void* state,
                     char const* operation)
{
  // Two words make a result of at most 126 bits: nothing to account for
  // under limits that admit words. The IMath path keeps every check.
  if (BudgetAccess::wordUnlimited(state) && ExactRationalAccess::isWord(lhs) &&
      ExactRationalAccess::isWord(rhs))
    return;
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(
      bitSum(lhs.numeratorBits(), rhs.denominatorBits(), state, operation),
      bitSum(lhs.denominatorBits(), rhs.numeratorBits(), state, operation),
      state, operation);
}

void requireInteger(ExactRational const& value, char const* operation)
{
  if (!value.isInteger())
  {
    throw NumberFailure(NumberFailureKind::NonIntegerOperand,
                        operation,
                        "integer operand required");
  }
}

std::uint64_t magnitudeAsUint64(mp_int value, bool& fits) noexcept
{
  std::uint64_t result = 0;
  fits = true;
  for (mp_size index = MP_USED(value); index > 0; --index)
  {
    mp_digit const digit = MP_DIGITS(value)[index - 1];
    if constexpr (MP_DIGIT_BIT >= 64)
    {
      if (index != 1)
      {
        fits = false;
        return 0;
      }
      result = static_cast<std::uint64_t>(digit);
    }
    else
    {
      if (result >
          (std::numeric_limits<std::uint64_t>::max() >> MP_DIGIT_BIT))
      {
        fits = false;
        return 0;
      }
      result = (result << MP_DIGIT_BIT) | digit;
    }
  }
  return result;
}

/* ---- the word state ------------------------------------------------- */

#ifdef STP_LRA_HAVE_WIDE
/* Wide enough to hold the product of two operand-width values, so the inner
 * arithmetic needs no overflow check.  STP already reaches for a 128-bit type
 * this way in lib/Simplifier/UnsignedIntervalAnalysis.cpp, guarded and marked
 * __extension__ to stay inside -Wpedantic -Werror. */
__extension__ typedef __int128 wide_t;
__extension__ typedef unsigned __int128 uwide_t;
constexpr std::int64_t kWordLimit = (std::int64_t{1} << 62) - 1;
/* The widest magnitude the wide lane may hold: one bit under the signed
 * range, so negation and gcd never meet the unnegatable minimum. */
constexpr int kWideOperandBits = 126;
#else
/* No 128-bit type to compute in (see PortableBits.h), so the word path runs
 * at half scale and anything wider lives in the big state instead. */
typedef std::int64_t wide_t;
typedef std::uint64_t uwide_t;
constexpr std::int64_t kWordLimit = (std::int64_t{1} << 31) - 1;
#endif

/* Bit length, matching mp_int_count_bits exactly -- including that it reports
 * one bit for zero, which the budget's observed-width accounting relies on. */
std::uint64_t wordBitCount(std::int64_t value) noexcept
{
  std::uint64_t const magnitude =
      value < 0 ? (~static_cast<std::uint64_t>(value) + 1U)
                : static_cast<std::uint64_t>(value);
  if (magnitude == 0)
  {
    return 1;
  }
  return static_cast<std::uint64_t>(64 - countLeadingZeros(magnitude));
}

std::uint64_t magnitude64(std::int64_t value) noexcept
{
  return value < 0 ? (~static_cast<std::uint64_t>(value) + 1U)
                   : static_cast<std::uint64_t>(value);
}

/* Binary gcd on machine words; gcd(0, b) = b.  The operands the word lane
 * hands it are components, at most 62 bits, so no step can overflow. */
std::uint64_t gcd64(std::uint64_t a, std::uint64_t b) noexcept
{
  if (a == 0)
    return b;
  if (b == 0)
    return a;
  if (a == 1 || b == 1)
    return 1;
  int const a_twos = countTrailingZeros(a);
  int const b_twos = countTrailingZeros(b);
  a >>= a_twos;
  b >>= b_twos;
  int const twos = a_twos < b_twos ? a_twos : b_twos;
  // Dyadic denominators become one after stripping their powers of two.
  // No subtract/shift loop is needed to prove that the odd parts are coprime.
  if (a == 1 || b == 1)
    return std::uint64_t{1} << twos;
  while (a != b)
  {
    if (a > b)
    {
      a -= b;
      a >>= countTrailingZeros(a);
    }
    else
    {
      b -= a;
      b >>= countTrailingZeros(b);
    }
  }
  return a << twos;
}

#ifdef STP_LRA_HAVE_WIDE
int wideCtz(uwide_t value) noexcept
{
  unsigned long long const low = static_cast<unsigned long long>(value);
  if (low != 0)
  {
    return __builtin_ctzll(low);
  }
  return 64 + __builtin_ctzll(static_cast<unsigned long long>(value >> 64));
}
#endif

wide_t wideGcd(wide_t left, wide_t right) noexcept
{
  /* Binary (Stein) gcd. Modulo-Euclid costs a software 128-bit division
   * (__modti3) per step, and on the MILP families whose values live just
   * past the word boundary that division dominated whole solves; shifts
   * and subtractions do the same job in a fraction of the time. */
  uwide_t a = left < 0 ? static_cast<uwide_t>(-(left + 1)) + 1U
                       : static_cast<uwide_t>(left);
  uwide_t b = right < 0 ? static_cast<uwide_t>(-(right + 1)) + 1U
                        : static_cast<uwide_t>(right);
  if (a == 0)
  {
    return static_cast<wide_t>(b);
  }
  if (b == 0)
  {
    return static_cast<wide_t>(a);
  }
#ifdef STP_LRA_HAVE_WIDE
  /* Operands that both fit a word take the same loop in word arithmetic,
   * decided once here rather than on every shift and subtract inside the
   * loop. */
  if ((a >> 64) == 0 && (b >> 64) == 0)
  {
    return static_cast<wide_t>(gcd64(static_cast<std::uint64_t>(a),
                                     static_cast<std::uint64_t>(b)));
  }
  int const common_twos = [&] {
    int const a_twos = wideCtz(a);
    int const b_twos = wideCtz(b);
    a >>= a_twos;
    b >>= b_twos;
    return a_twos < b_twos ? a_twos : b_twos;
  }();
  if (a == 1 || b == 1)
    return static_cast<wide_t>(uwide_t{1} << common_twos);
  while (a != b)
  {
    if (a > b)
    {
      a -= b;
      a >>= wideCtz(a);
    }
    else
    {
      b -= a;
      b >>= wideCtz(b);
    }
  }
  return static_cast<wide_t>(a << common_twos);
#else
  return static_cast<wide_t>(gcd64(a, b));
#endif
}

/* Reduce to canonical form and report whether the result still fits the word
 * state: coprime, denominator strictly positive, zero written as 0/1. */
bool reduceToWord(wide_t numerator,
                  wide_t denominator,
                  std::int64_t& out_numerator,
                  std::int64_t& out_denominator) noexcept
{
  if (denominator == 0)
  {
    return false;
  }
  if (denominator < 0)
  {
    numerator = -numerator;
    denominator = -denominator;
  }
  if (numerator == 0)
  {
    out_numerator = 0;
    out_denominator = 1;
    return true;
  }
  wide_t const divisor = wideGcd(numerator, denominator);
  if (divisor > 1)
  {
    numerator /= divisor;
    denominator /= divisor;
  }
  wide_t const limit = static_cast<wide_t>(kWordLimit);
  if (numerator > limit || numerator < -limit || denominator > limit)
  {
    return false;
  }
  out_numerator = static_cast<std::int64_t>(numerator);
  out_denominator = static_cast<std::int64_t>(denominator);
  return true;
}

/* Parse directly into the allocation-free representation when both decimal
 * components fit fixed-width inputs.  reduceToWord also admits components
 * which are individually wider than the word-state limit but become small
 * after cancellation. */
bool componentsAsWord(std::string_view numerator,
                      std::string_view denominator,
                      std::int64_t& out_numerator,
                      std::int64_t& out_denominator) noexcept
{
  std::int64_t parsed_numerator = 0;
  std::uint64_t parsed_denominator = 0;
  auto const numerator_result = std::from_chars(
      numerator.data(), numerator.data() + numerator.size(), parsed_numerator);
  auto const denominator_result =
      std::from_chars(denominator.data(),
                      denominator.data() + denominator.size(),
                      parsed_denominator);
  if (numerator_result.ec != std::errc{} ||
      numerator_result.ptr != numerator.data() + numerator.size() ||
      denominator_result.ec != std::errc{} ||
      denominator_result.ptr != denominator.data() + denominator.size())
  {
    return false;
  }
#ifndef STP_LRA_HAVE_WIDE
  if (parsed_numerator == std::numeric_limits<std::int64_t>::min() ||
      parsed_denominator >
      static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()))
  {
    return false;
  }
#endif
  return reduceToWord(static_cast<wide_t>(parsed_numerator),
                      static_cast<wide_t>(parsed_denominator),
                      out_numerator, out_denominator);
}

/* Read a big-state rational back as machine words, without allocating.
 * Returns false when it does not fit, which for a canonical value also means
 * it cannot be equal to any word-state value. */
bool nativeAsWord(imath_rat_value const& value,
                  std::int64_t& out_numerator,
                  std::int64_t& out_denominator) noexcept
{
  mp_rat const native = const_cast<mp_rat>(&value);
  bool numerator_fits = false;
  bool denominator_fits = false;
  std::uint64_t const numerator =
      magnitudeAsUint64(MP_NUMER_P(native), numerator_fits);
  std::uint64_t const denominator =
      magnitudeAsUint64(MP_DENOM_P(native), denominator_fits);
  std::uint64_t const limit = static_cast<std::uint64_t>(kWordLimit);
  if (!numerator_fits || !denominator_fits || denominator == 0 ||
      numerator > limit || denominator > limit)
  {
    return false;
  }
  out_numerator = MP_SIGN(MP_NUMER_P(native)) == MP_NEG
                      ? -static_cast<std::int64_t>(numerator)
                      : static_cast<std::int64_t>(numerator);
  out_denominator = static_cast<std::int64_t>(denominator);
  return true;
}

/* The big form lives in a block from the accounted allocator, so its bytes
 * count against the budget like the digits it holds, and it can be freed
 * after the scope that made it has ended. */
BigRational* allocateBig(void* state, char const* operation)
{
  stp_lra_imath_clear_failure();
  void* const block = stp_lra_imath_malloc(sizeof(BigRational));
  if (block == nullptr)
  {
    throw BudgetAccess::allocationFailure(operation,
                                          "big rational block allocation");
  }
  BigRational* const big = static_cast<BigRational*>(block);
  big->budget_state = state;
  mp_result const result = mp_rat_init(&big->value);
  if (result != MP_OK ||
      stp_lra_imath_last_failure() != STP_LRA_IMATH_FAILURE_NONE)
  {
    stp_lra_imath_free(block);
    if (result != MP_OK)
      checkNativeResult(result, operation);
    throw BudgetAccess::allocationFailure(
        operation, "native init returned success after allocator failure");
  }
  BudgetAccess::valueCreated(state);
  return big;
}

/* Give a word-state value a fresh, zero-valued big form under `state`. */
mp_rat promoteToBig(ExactRational& value, void* state, char const* operation)
{
  BigRational* const big = allocateBig(state, operation);
  ExactRationalAccess::adoptBig(value, big);
  return &big->value;
}

/* Bring a big-state value back to the word state when it fits.
 *
 * Without this the representation is a one-way door: values are born big
 * whenever they come from a parse or a wide constructor, every result
 * computed from one is big too, and the word path never gets a turn.
 * Demoting at the end of construction and after each big operation is what
 * keeps a tableau of small numbers in machine integers. */
void tryDemote(ExactRational& value) noexcept
{
  BigRational* const big = ExactRationalAccess::big(value);
  if (big == nullptr)
  {
    return;
  }
  std::int64_t numerator = 0;
  std::int64_t denominator = 1;
  if (!nativeAsWord(big->value, numerator, denominator))
  {
    return;
  }
  void* const state = big->budget_state;
  mp_rat_clear(&big->value);
  stp_lra_imath_free(big);
  ExactRationalAccess::dropBig(value, numerator, denominator);
  BudgetAccess::valueReleased(state);
  BudgetAccess::record(state, NumberMetricEvent::NativeDemote);
}

/* The word-state counterpart of postCheck: same budget limit, same metric,
 * same observed widths, without asking IMath anything. */
void postCheckWord(std::int64_t numerator,
                   std::int64_t denominator,
                   void* state,
                   char const* operation)
{
  std::uint64_t const numerator_bits = wordBitCount(numerator);
  std::uint64_t const denominator_bits = wordBitCount(denominator);
  if (!BudgetAccess::wordUnlimited(state))
  {
    NumberLimits const limits = BudgetAccess::limits(state);
    if (numerator_bits > limits.maximum_result_bits ||
        denominator_bits > limits.maximum_result_bits)
    {
      BudgetAccess::postResultStop(state, operation,
                                   "exact result exceeds configured bit limit");
    }
  }
  BudgetAccess::record(state, NumberMetricEvent::Canonicalize);
  BudgetAccess::observeValue(state, numerator_bits, denominator_bits);
}

/* Finish constructing a big-state value: limits, metric, demotion. */
void finishBigConstruction(ExactRational& value,
                           void* state,
                           NumberMetricEvent event,
                           char const* operation)
{
  postCheck(&ExactRationalAccess::big(value)->value, state, operation);
  BudgetAccess::record(state, event);
  tryDemote(value);
}

/* Build a big-state result from a native integer. */
ExactRational fromNativeInteger(mp_int value,
                                void* state,
                                char const* operation)
{
  checkResultEstimate(mp_int_count_bits(value), 1, state, operation);
  ExactRational result;
  mp_rat const native = promoteToBig(result, state, operation);
  checkedNative(operation, [&] { return mp_rat_set(native, value, nullptr); });
  postCheck(native, state, operation);
  tryDemote(result);
  return result;
}

ExactRational constructFromComponents(std::string_view numerator,
                                      std::string_view denominator,
                                      void* state,
                                      char const* operation)
{
  if (!signedDecimalInteger(numerator) || !unsignedDecimal(denominator))
  {
    throw NumberFailure(NumberFailureKind::InvalidText,
                        operation,
                        "expected signed numerator and positive denominator");
  }
  if (decimalZero(denominator))
  {
    throw NumberFailure(NumberFailureKind::ZeroDenominator,
                        operation,
                        "zero denominator");
  }
  preflightComponents(numerator, denominator, state, operation);
  ExactRational result;
  std::int64_t word_numerator = 0;
  std::int64_t word_denominator = 1;
  if (componentsAsWord(numerator, denominator, word_numerator,
                       word_denominator))
  {
    ExactRationalAccess::setWord(result, word_numerator, word_denominator);
    postCheckWord(word_numerator, word_denominator, state, operation);
    return result;
  }
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_PARSE);
  mp_rat const native = promoteToBig(result, state, operation);
  setFromComponents(native, numerator, denominator, operation);
  postCheck(native, state, operation);
  tryDemote(result);
  return result;
}

/* ---- the word lane --------------------------------------------------- */

enum class ArithmeticOperation
{
  Add,
  Subtract,
  Multiply,
  Divide
};

bool fitsWord(wide_t numerator, wide_t denominator) noexcept
{
  wide_t const limit = static_cast<wide_t>(kWordLimit);
  return numerator <= limit && numerator >= -limit && denominator <= limit;
}

/* a/b +/- c/d over words, the way the big path does it: form g = gcd(b, d)
 * first, cross-multiply by the reduced cofactors, and after the sum only a
 * divisor of g can remain to cancel (Knuth 4.5.1).  Integers -- both
 * denominators one -- are the common case on a tableau and take one add.
 * False means the reduced result does not fit a word; the caller recomputes
 * it in the wide or big lane. */
bool wordAddSubtract(std::int64_t an, std::int64_t ad,
                     std::int64_t bn, std::int64_t bd,
                     bool subtract,
                     std::int64_t& out_numerator,
                     std::int64_t& out_denominator) noexcept
{
  wide_t const b = subtract ? -static_cast<wide_t>(bn) : static_cast<wide_t>(bn);
  if (ad == 1 && bd == 1)
  {
    wide_t const sum = static_cast<wide_t>(an) + b;
    if (!fitsWord(sum, 1))
      return false;
    out_numerator = static_cast<std::int64_t>(sum);
    out_denominator = 1;
    return true;
  }
  std::uint64_t const common =
      gcd64(static_cast<std::uint64_t>(ad), static_cast<std::uint64_t>(bd));
  std::int64_t const ad_reduced = ad / static_cast<std::int64_t>(common);
  std::int64_t const bd_reduced = bd / static_cast<std::int64_t>(common);
  wide_t numerator = static_cast<wide_t>(an) * bd_reduced + b * ad_reduced;
  wide_t denominator = static_cast<wide_t>(ad) * bd_reduced;
  if (numerator == 0)
  {
    out_numerator = 0;
    out_denominator = 1;
    return true;
  }
  if (common != 1)
  {
    uwide_t const magnitude =
        numerator < 0 ? static_cast<uwide_t>(-numerator)
                      : static_cast<uwide_t>(numerator);
    std::uint64_t const remainder = static_cast<std::uint64_t>(magnitude % common);
    std::uint64_t const shared = gcd64(common, remainder);
    if (shared > 1)
    {
      numerator /= static_cast<wide_t>(shared);
      denominator /= static_cast<wide_t>(shared);
    }
  }
  if (!fitsWord(numerator, denominator))
    return false;
  out_numerator = static_cast<std::int64_t>(numerator);
  out_denominator = static_cast<std::int64_t>(denominator);
  return true;
}

/* a/b * c/d: cancel across the diagonal first, so the products are the
 * canonical result and need no final reduction. */
bool wordMultiply(std::int64_t an, std::int64_t ad,
                  std::int64_t bn, std::int64_t bd,
                  std::int64_t& out_numerator,
                  std::int64_t& out_denominator) noexcept
{
  if (an == 0 || bn == 0)
  {
    out_numerator = 0;
    out_denominator = 1;
    return true;
  }
  std::uint64_t const left_shared =
      gcd64(magnitude64(an), static_cast<std::uint64_t>(bd));
  std::uint64_t const right_shared =
      gcd64(magnitude64(bn), static_cast<std::uint64_t>(ad));
  wide_t const numerator =
      static_cast<wide_t>(an / static_cast<std::int64_t>(left_shared)) *
      (bn / static_cast<std::int64_t>(right_shared));
  wide_t const denominator =
      static_cast<wide_t>(ad / static_cast<std::int64_t>(right_shared)) *
      (bd / static_cast<std::int64_t>(left_shared));
  if (!fitsWord(numerator, denominator))
    return false;
  out_numerator = static_cast<std::int64_t>(numerator);
  out_denominator = static_cast<std::int64_t>(denominator);
  return true;
}

/* a/b / c/d, c nonzero: multiplication by d/c with the divisor's sign
 * moved onto the numerator. */
bool wordDivide(std::int64_t an, std::int64_t ad,
                std::int64_t bn, std::int64_t bd,
                std::int64_t& out_numerator,
                std::int64_t& out_denominator) noexcept
{
  if (an == 0)
  {
    out_numerator = 0;
    out_denominator = 1;
    return true;
  }
  std::uint64_t const numerator_shared = gcd64(magnitude64(an), magnitude64(bn));
  std::uint64_t const denominator_shared =
      gcd64(static_cast<std::uint64_t>(ad), static_cast<std::uint64_t>(bd));
  std::int64_t const divisor_magnitude =
      static_cast<std::int64_t>(magnitude64(bn) / numerator_shared);
  wide_t numerator =
      static_cast<wide_t>(an / static_cast<std::int64_t>(numerator_shared)) *
      (bd / static_cast<std::int64_t>(denominator_shared));
  wide_t const denominator =
      static_cast<wide_t>(ad / static_cast<std::int64_t>(denominator_shared)) *
      divisor_magnitude;
  if (bn < 0)
    numerator = -numerator;
  if (!fitsWord(numerator, denominator))
    return false;
  out_numerator = static_cast<std::int64_t>(numerator);
  out_denominator = static_cast<std::int64_t>(denominator);
  return true;
}

/* ---- the big lane ---------------------------------------------------- */

void setNativeZero(mp_rat target, char const* operation)
{
  mp_int_zero(MP_NUMER_P(target));
  checkedNative(operation,
                [&] { return mp_int_set_value(MP_DENOM_P(target), 1); });
}

void divideExactOrCopy(mp_int value,
                       mp_int divisor,
                       mp_int output,
                       char const* operation)
{
  if (mp_int_compare_value(divisor, 1) == 0)
  {
    checkedNative(operation, [&] { return mp_int_copy(value, output); });
    return;
  }
  checkedNative(operation,
                [&] { return mp_int_div(value, divisor, output, nullptr); });
}

/* For a/b +/- c/d, first form g = gcd(b,d).  The numerator only needs the
 * reduced cross multipliers d/g and b/g, and after the sum only
 * gcd(numerator,g) can remain to cancel.  This avoids constructing b*d and
 * the two full-width cross products when the denominators share factors. */
void nativeAddSubtract(mp_rat lhs,
                       mp_rat rhs,
                       mp_rat target,
                       bool subtract,
                       char const* operation)
{
  NativeInteger common(operation);
  NativeInteger lhs_scale(operation);
  NativeInteger rhs_scale(operation);
  NativeInteger rhs_term(operation);
  NativeInteger reduction(operation);
  NativeInteger denominator_factor(operation);
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_DENOM_P(lhs), MP_DENOM_P(rhs), &common.value);
  });
  if (mp_int_compare_value(&common.value, 1) == 0)
  {
    checkedNative(operation, [&] {
      return mp_int_mul(MP_NUMER_P(lhs), MP_DENOM_P(rhs),
                        MP_NUMER_P(target));
    });
    checkedNative(operation, [&] {
      return mp_int_mul(MP_NUMER_P(rhs), MP_DENOM_P(lhs), &rhs_term.value);
    });
    checkedNative(operation, [&] {
      return subtract
                 ? mp_int_sub(MP_NUMER_P(target), &rhs_term.value,
                              MP_NUMER_P(target))
                 : mp_int_add(MP_NUMER_P(target), &rhs_term.value,
                              MP_NUMER_P(target));
    });
    if (mp_int_compare_zero(MP_NUMER_P(target)) == 0)
    {
      setNativeZero(target, operation);
      return;
    }
    checkedNative(operation, [&] {
      return mp_int_mul(MP_DENOM_P(lhs), MP_DENOM_P(rhs),
                        MP_DENOM_P(target));
    });
    return;
  }
  checkedNative(operation, [&] {
    return mp_int_div(MP_DENOM_P(rhs), &common.value, &lhs_scale.value,
                      nullptr);
  });
  checkedNative(operation, [&] {
    return mp_int_div(MP_DENOM_P(lhs), &common.value, &rhs_scale.value,
                      nullptr);
  });
  checkedNative(operation, [&] {
    return mp_int_mul(MP_NUMER_P(lhs), &lhs_scale.value,
                      MP_NUMER_P(target));
  });
  checkedNative(operation, [&] {
    return mp_int_mul(MP_NUMER_P(rhs), &rhs_scale.value, &rhs_term.value);
  });
  checkedNative(operation, [&] {
    return subtract
               ? mp_int_sub(MP_NUMER_P(target), &rhs_term.value,
                            MP_NUMER_P(target))
               : mp_int_add(MP_NUMER_P(target), &rhs_term.value,
                            MP_NUMER_P(target));
  });
  if (mp_int_compare_zero(MP_NUMER_P(target)) == 0)
  {
    setNativeZero(target, operation);
    return;
  }
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(target), &common.value, &reduction.value);
  });
  if (mp_int_compare_value(&reduction.value, 1) != 0)
  {
    checkedNative(operation, [&] {
      return mp_int_div(MP_NUMER_P(target), &reduction.value,
                        MP_NUMER_P(target), nullptr);
    });
  }
  divideExactOrCopy(MP_DENOM_P(rhs), &reduction.value,
                    &denominator_factor.value, operation);
  checkedNative(operation, [&] {
    return mp_int_mul(&rhs_scale.value, &denominator_factor.value,
                      MP_DENOM_P(target));
  });
}

/* Cancel numerator/denominator pairs before multiplying, so neither product
 * is wider than the canonical result. */
void nativeMultiply(mp_rat lhs,
                    mp_rat rhs,
                    mp_rat target,
                    char const* operation)
{
  if (mp_int_compare_zero(MP_NUMER_P(lhs)) == 0 ||
      mp_int_compare_zero(MP_NUMER_P(rhs)) == 0)
  {
    setNativeZero(target, operation);
    return;
  }
  NativeInteger lhs_gcd(operation);
  NativeInteger rhs_gcd(operation);
  NativeInteger lhs_factor(operation);
  NativeInteger rhs_factor(operation);
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(lhs), MP_DENOM_P(rhs), &lhs_gcd.value);
  });
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(rhs), MP_DENOM_P(lhs), &rhs_gcd.value);
  });
  divideExactOrCopy(MP_NUMER_P(lhs), &lhs_gcd.value, &lhs_factor.value,
                    operation);
  divideExactOrCopy(MP_NUMER_P(rhs), &rhs_gcd.value, &rhs_factor.value,
                    operation);
  checkedNative(operation, [&] {
    return mp_int_mul(&lhs_factor.value, &rhs_factor.value,
                      MP_NUMER_P(target));
  });
  divideExactOrCopy(MP_DENOM_P(lhs), &rhs_gcd.value, &lhs_factor.value,
                    operation);
  divideExactOrCopy(MP_DENOM_P(rhs), &lhs_gcd.value, &rhs_factor.value,
                    operation);
  checkedNative(operation, [&] {
    return mp_int_mul(&lhs_factor.value, &rhs_factor.value,
                      MP_DENOM_P(target));
  });
}

/* Division is multiplication by the reciprocal.  Cancel a/c and d/b before
 * forming (a*d)/(b*c), then normalize the divisor's sign onto the numerator. */
void nativeDivide(mp_rat lhs,
                  mp_rat rhs,
                  mp_rat target,
                  char const* operation)
{
  if (mp_int_compare_zero(MP_NUMER_P(lhs)) == 0)
  {
    setNativeZero(target, operation);
    return;
  }
  bool const divisor_negative = MP_SIGN(MP_NUMER_P(rhs)) == MP_NEG;
  NativeInteger numerator_gcd(operation);
  NativeInteger denominator_gcd(operation);
  NativeInteger lhs_factor(operation);
  NativeInteger rhs_factor(operation);
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(lhs), MP_NUMER_P(rhs),
                      &numerator_gcd.value);
  });
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_DENOM_P(rhs), MP_DENOM_P(lhs),
                      &denominator_gcd.value);
  });
  divideExactOrCopy(MP_NUMER_P(lhs), &numerator_gcd.value,
                    &lhs_factor.value, operation);
  divideExactOrCopy(MP_DENOM_P(rhs), &denominator_gcd.value,
                    &rhs_factor.value, operation);
  checkedNative(operation, [&] {
    return mp_int_mul(&lhs_factor.value, &rhs_factor.value,
                      MP_NUMER_P(target));
  });
  divideExactOrCopy(MP_DENOM_P(lhs), &denominator_gcd.value,
                    &lhs_factor.value, operation);
  divideExactOrCopy(MP_NUMER_P(rhs), &numerator_gcd.value,
                    &rhs_factor.value, operation);
  checkedNative(operation,
                [&] { return mp_int_abs(&rhs_factor.value, &rhs_factor.value); });
  checkedNative(operation, [&] {
    return mp_int_mul(&lhs_factor.value, &rhs_factor.value,
                      MP_DENOM_P(target));
  });
  if (divisor_negative)
  {
    checkedNative(operation, [&] {
      return mp_int_neg(MP_NUMER_P(target), MP_NUMER_P(target));
    });
  }
}

#ifdef STP_LRA_HAVE_WIDE
/* Read a rational's components into the wide type. A word value reads
 * directly; a big one qualifies when both components fit kWideOperandBits,
 * assembled from its digits. False leaves the outputs untouched and sends
 * the caller to the big path. */
bool loadWideComponents(ExactRational const& value,
                        wide_t& numerator,
                        wide_t& denominator) noexcept
{
  if (ExactRationalAccess::isWord(value))
  {
    numerator = ExactRationalAccess::wordNumerator(value);
    denominator = ExactRationalAccess::wordDenominator(value);
    return true;
  }
  mp_rat const rational = &ExactRationalAccess::big(value)->value;
  mp_int const numer = MP_NUMER_P(rational);
  mp_int const denom = MP_DENOM_P(rational);
  if (mp_int_count_bits(numer) > kWideOperandBits ||
      mp_int_count_bits(denom) > kWideOperandBits)
  {
    return false;
  }
  auto const assemble = [](mp_int component) noexcept -> wide_t {
    uwide_t magnitude = 0;
    for (mp_size i = MP_USED(component); i > 0; --i)
    {
      magnitude =
          (magnitude << MP_DIGIT_BIT) | (uwide_t)MP_DIGITS(component)[i - 1];
    }
    wide_t const value = static_cast<wide_t>(magnitude);
    return MP_SIGN(component) == MP_NEG ? -value : value;
  };
  numerator = assemble(numer);
  denominator = assemble(denom);
  return true;
}
#endif

char const* operationName(ArithmeticOperation operation) noexcept
{
  switch (operation)
  {
    case ArithmeticOperation::Add: return "add";
    case ArithmeticOperation::Subtract: return "subtract";
    case ArithmeticOperation::Multiply: return "multiply";
    case ArithmeticOperation::Divide: return "divide";
  }
  return "arithmetic";
}

/* Everything past the word lane: the budget's preflight under limits that
 * do not admit words, the wide lane for values just past a word, and the
 * big path with its temporaries and arbitrary-precision gcd. */
void arithmeticSlow(ExactRational& out,
                    ExactRational const& lhs,
                    ExactRational const& rhs,
                    ArithmeticOperation operation,
                    void* state)
{
  char const* const name = operationName(operation);
  switch (operation)
  {
    case ArithmeticOperation::Add:
    case ArithmeticOperation::Subtract:
      preflightAddSubtract(lhs, rhs, state, name);
      break;
    case ArithmeticOperation::Multiply:
      preflightMultiply(lhs, rhs, state, name);
      break;
    case ArithmeticOperation::Divide:
      if (rhs.isZero())
      {
        throw NumberFailure(NumberFailureKind::DivisionByZero, name,
                            "zero divisor");
      }
      preflightDivide(lhs, rhs, state, name);
      break;
  }
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs))
  {
    /* Words under limits that do not admit them outright: the same lane,
     * followed by the result-bit check the fast path skipped. */
    std::int64_t const an = ExactRationalAccess::wordNumerator(lhs);
    std::int64_t const ad = ExactRationalAccess::wordDenominator(lhs);
    std::int64_t const bn = ExactRationalAccess::wordNumerator(rhs);
    std::int64_t const bd = ExactRationalAccess::wordDenominator(rhs);
    std::int64_t numerator = 0;
    std::int64_t denominator = 1;
    bool fits = false;
    switch (operation)
    {
      case ArithmeticOperation::Add:
        fits = wordAddSubtract(an, ad, bn, bd, false, numerator, denominator);
        break;
      case ArithmeticOperation::Subtract:
        fits = wordAddSubtract(an, ad, bn, bd, true, numerator, denominator);
        break;
      case ArithmeticOperation::Multiply:
        fits = wordMultiply(an, ad, bn, bd, numerator, denominator);
        break;
      case ArithmeticOperation::Divide:
        fits = wordDivide(an, ad, bn, bd, numerator, denominator);
        break;
    }
    if (fits)
    {
      ExactRationalAccess::setWord(out, numerator, denominator);
      postCheckWord(numerator, denominator, state, name);
      return;
    }
  }
#ifdef STP_LRA_HAVE_WIDE
  /* The wide middle lane. Values on the coefficient-heavy families hover
   * just past the 63-bit word boundary, and every operation on them ran
   * the full IMath route -- temporaries, allocation, arbitrary-precision
   * gcd -- for numbers a machine register pair holds. When both operands'
   * components fit 126 bits, compute in the wide type with overflow-checked
   * arithmetic; overflow simply falls through to IMath. */
  {
    wide_t an = 0;
    wide_t ad = 1;
    wide_t bn = 0;
    wide_t bd = 1;
    if (loadWideComponents(lhs, an, ad) && loadWideComponents(rhs, bn, bd))
    {
      wide_t numerator = 0;
      wide_t denominator = 0;
      bool fits = true;
      /* The same algebra the big path uses, so the lane's asymptotics
       * match it. Add and subtract go through the denominators' gcd -- on
       * the MILP families every value shares one decimal scale, and the
       * naive cross-multiply squared that denominator on every operation,
       * then paid a wide gcd to shrink it again. Multiply and divide
       * cancel across the diagonal first, so the products stay small and
       * the result needs no final reduction. */
      switch (operation)
      {
        case ArithmeticOperation::Add:
        case ArithmeticOperation::Subtract:
        {
          wide_t const common = wideGcd(ad, bd);
          wide_t const bd_reduced = bd / common;
          wide_t const ad_reduced = ad / common;
          wide_t cross_left = 0;
          wide_t cross_right = 0;
          fits = !__builtin_mul_overflow(an, bd_reduced, &cross_left) &&
                 !__builtin_mul_overflow(bn, ad_reduced, &cross_right) &&
                 (operation == ArithmeticOperation::Add
                      ? !__builtin_add_overflow(cross_left, cross_right,
                                                &numerator)
                      : !__builtin_sub_overflow(cross_left, cross_right,
                                                &numerator)) &&
                 !__builtin_mul_overflow(ad, bd_reduced, &denominator);
          if (fits && numerator != 0)
          {
            /* Only the common factor can survive into the numerator
             * (Knuth 4.5.1): one small gcd instead of a wide one. */
            wide_t const shared = wideGcd(numerator, common);
            if (shared > 1)
            {
              numerator /= shared;
              denominator /= shared;
            }
          }
          break;
        }
        case ArithmeticOperation::Multiply:
        {
          wide_t const left_shared = wideGcd(an, bd);
          wide_t const right_shared = wideGcd(bn, ad);
          fits = !__builtin_mul_overflow(an / left_shared, bn / right_shared,
                                         &numerator) &&
                 !__builtin_mul_overflow(ad / right_shared, bd / left_shared,
                                         &denominator);
          break;
        }
        case ArithmeticOperation::Divide:
        {
          // A zero divisor was already rejected above.
          if (bn == 0)
          {
            fits = false;
            break;
          }
          wide_t const num_shared = wideGcd(an, bn);
          wide_t const den_shared = wideGcd(ad, bd);
          fits = !__builtin_mul_overflow(an / num_shared, bd / den_shared,
                                         &numerator) &&
                 !__builtin_mul_overflow(ad / den_shared, bn / num_shared,
                                         &denominator);
          break;
        }
      }
      constexpr wide_t wide_minimum =
          static_cast<wide_t>(static_cast<uwide_t>(1) << 127);
      if (fits && denominator != 0 && numerator != wide_minimum &&
          denominator != wide_minimum)
      {
        if (denominator < 0)
        {
          numerator = -numerator;
          denominator = -denominator;
        }
        if (numerator != 0)
        {
          wide_t const divisor = wideGcd(numerator, denominator);
          if (divisor > 1)
          {
            numerator /= divisor;
            denominator /= divisor;
          }
        }
        else
        {
          denominator = 1;
        }
        if (fitsWord(numerator, denominator))
        {
          std::int64_t const word_numerator =
              static_cast<std::int64_t>(numerator);
          std::int64_t const word_denominator =
              static_cast<std::int64_t>(denominator);
          ExactRationalAccess::setWord(out, word_numerator, word_denominator);
          BudgetAccess::record(state, operation == ArithmeticOperation::Add
                                          ? NumberMetricEvent::NativeAdd
                                          : operation ==
                                                    ArithmeticOperation::
                                                        Subtract
                                                ? NumberMetricEvent::
                                                      NativeSubtract
                                                : operation ==
                                                          ArithmeticOperation::
                                                              Multiply
                                                      ? NumberMetricEvent::
                                                            NativeMultiply
                                                      : NumberMetricEvent::
                                                            NativeDivide);
          postCheckWord(word_numerator, word_denominator, state, name);
          return;
        }
        /* The result is wide. Storing it here would strand the value in a
         * load-compute-store round trip on every later operation -- the
         * accumulator patterns of the MILP families measured 7x slower
         * that way. Fall through to the big path instead: the wide
         * compute above is a few checked multiplies and shifts, and the
         * value keeps its big residency, where in-place arithmetic is the
         * cheaper steady state. The lane keeps exactly the operations
         * whose reduced result fits a word again. */
      }
    }
  }
#endif
  stp_lra_imath_allocation_site site_name =
      STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED;
  NumberMetricEvent native_event = NumberMetricEvent::NativeAdd;
  switch (operation)
  {
    case ArithmeticOperation::Add:
      site_name = STP_LRA_IMATH_ALLOCATION_ADD;
      native_event = NumberMetricEvent::NativeAdd;
      break;
    case ArithmeticOperation::Subtract:
      site_name = STP_LRA_IMATH_ALLOCATION_SUBTRACT;
      native_event = NumberMetricEvent::NativeSubtract;
      break;
    case ArithmeticOperation::Multiply:
      site_name = STP_LRA_IMATH_ALLOCATION_MULTIPLY;
      native_event = NumberMetricEvent::NativeMultiply;
      break;
    case ArithmeticOperation::Divide:
      site_name = STP_LRA_IMATH_ALLOCATION_DIVIDE;
      native_event = NumberMetricEvent::NativeDivide;
      break;
  }
  AllocationSiteScope site(site_name);
  ExactRational result;
  mp_rat const target = promoteToBig(result, state, name);
  mp_rat const native_lhs = ExactRationalAccess::native(lhs);
  mp_rat const native_rhs = ExactRationalAccess::native(rhs);
  BudgetAccess::record(state, native_event);
  BudgetAccess::record(state, NumberMetricEvent::BigOperation);
  switch (operation)
  {
    case ArithmeticOperation::Add:
      nativeAddSubtract(native_lhs, native_rhs, target, false, name);
      break;
    case ArithmeticOperation::Subtract:
      nativeAddSubtract(native_lhs, native_rhs, target, true, name);
      break;
    case ArithmeticOperation::Multiply:
      nativeMultiply(native_lhs, native_rhs, target, name);
      break;
    case ArithmeticOperation::Divide:
      nativeDivide(native_lhs, native_rhs, target, name);
      break;
  }
  postCheckKnownCanonical(target, state, name);
  tryDemote(result);
  out.swap(result);
}

template <ArithmeticOperation Operation>
inline void arithmetic(ExactRational& out,
                       ExactRational const& lhs,
                       ExactRational const& rhs)
{
  void* const state = BudgetAccess::requireActive(operationName(Operation));
  BudgetAccess::record(state, Operation == ArithmeticOperation::Add
                                  ? NumberMetricEvent::Add
                                  : Operation == ArithmeticOperation::Subtract
                                        ? NumberMetricEvent::Subtract
                                        : Operation == ArithmeticOperation::Multiply
                                              ? NumberMetricEvent::Multiply
                                              : NumberMetricEvent::Divide);
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs) &&
      BudgetAccess::wordUnlimited(state))
  {
    std::int64_t const an = ExactRationalAccess::wordNumerator(lhs);
    std::int64_t const ad = ExactRationalAccess::wordDenominator(lhs);
    std::int64_t const bn = ExactRationalAccess::wordNumerator(rhs);
    std::int64_t const bd = ExactRationalAccess::wordDenominator(rhs);
    std::int64_t numerator = 0;
    std::int64_t denominator = 1;
    bool fits = false;
    if constexpr (Operation == ArithmeticOperation::Add)
      fits = wordAddSubtract(an, ad, bn, bd, false, numerator, denominator);
    else if constexpr (Operation == ArithmeticOperation::Subtract)
      fits = wordAddSubtract(an, ad, bn, bd, true, numerator, denominator);
    else if constexpr (Operation == ArithmeticOperation::Multiply)
      fits = wordMultiply(an, ad, bn, bd, numerator, denominator);
    else
    {
      if (bn == 0)
      {
        throw NumberFailure(NumberFailureKind::DivisionByZero, "divide",
                            "zero divisor");
      }
      fits = wordDivide(an, ad, bn, bd, numerator, denominator);
    }
    if (fits)
    {
      ExactRationalAccess::setWord(out, numerator, denominator);
      BudgetAccess::record(state, NumberMetricEvent::Canonicalize);
      BudgetAccess::observeValue(state, wordBitCount(numerator),
                                 wordBitCount(denominator));
      return;
    }
  }
  arithmeticSlow(out, lhs, rhs, Operation, state);
}

}  // namespace

/* ---- materialisation ------------------------------------------------- */

namespace detail {

void materializeRational(ExactRational const& value, char const* operation)
{
  if (!ExactRationalAccess::isWord(value))
  {
    return;
  }
  /* Build the big form from the word form, then hand the value over to it.
   * The word fields stop being authoritative at that point.  This input
   * remains big, while fresh arithmetic results are demoted when their
   * canonical components fit.
   *
   * mp_rat_set_value takes mp_small, which is long and therefore 32 bits on
   * Windows, so it cannot carry the whole word range there; those hosts keep
   * the decimal round-trip. Where long is 64 bits the value is set directly:
   * this path is not cold -- a value that hovers around the word boundary is
   * materialized once per crossing, millions of times on the coefficient-
   * heavy families. The word form is canonical, so the reduce inside
   * set_value is one gcd of coprime machine words. */
  void* const state = BudgetAccess::requireActive(operation);
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_MATERIALIZE);
  std::int64_t const numerator = ExactRationalAccess::wordNumerator(value);
  std::int64_t const denominator = ExactRationalAccess::wordDenominator(value);
  BigRational* const big = allocateBig(state, operation);
  try
  {
    if constexpr (sizeof(mp_small) >= sizeof(std::int64_t))
    {
      checkedNative(operation, [&] {
        return mp_rat_set_value(&big->value, static_cast<mp_small>(numerator),
                                static_cast<mp_small>(denominator));
      });
    }
    else
    {
      char numerator_buffer[64];
      char denominator_buffer[64];
      std::string_view const numerator_text =
          integerCharacters(numerator, numerator_buffer, operation);
      std::string_view const denominator_text =
          integerCharacters(denominator, denominator_buffer, operation);
      setFromComponents(&big->value, numerator_text, denominator_text,
                        operation);
    }
  }
  catch (...)
  {
    mp_rat_clear(&big->value);
    BudgetAccess::valueDestroyed(state);
    stp_lra_imath_free(big);
    throw;
  }
  ExactRationalAccess::adoptBig(const_cast<ExactRational&>(value), big);
  BudgetAccess::record(state, NumberMetricEvent::NativeMaterialize);
}

}  // namespace detail

/* ---- the big-state members ------------------------------------------- */

void ExactRational::copyBig(ExactRational const& other)
{
  char const* operation = "ExactRational(copy)";
  void* const state = BudgetAccess::requireActive(operation);
  checkOperand(other, state, operation);
  checkResultEstimate(other.numeratorBits(), other.denominatorBits(), state,
                      operation);
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_CONSTRUCT);
  BigRational* const big = allocateBig(state, operation);
  try
  {
    checkedNative(operation, [&] {
      return mp_rat_copy(&other.big_->value, &big->value);
    });
  }
  catch (...)
  {
    mp_rat_clear(&big->value);
    BudgetAccess::valueDestroyed(state);
    stp_lra_imath_free(big);
    throw;
  }
  big_ = big;
  BudgetAccess::record(state, NumberMetricEvent::Copy);
  BudgetAccess::observeValue(state, numeratorBits(), denominatorBits());
}

void ExactRational::copyWordLimited(void* state)
{
  char const* operation = "ExactRational(copy)";
  checkOperand(*this, state, operation);
  checkResultEstimate(numeratorBits(), denominatorBits(), state, operation);
  BudgetAccess::record(state, NumberMetricEvent::Copy);
}

void ExactRational::destroyBig() noexcept
{
  void* const state = big_->budget_state;
  mp_rat_clear(&big_->value);
  stp_lra_imath_free(big_);
  BudgetAccess::valueDestroyed(state);
}

int ExactRational::bigSign() const noexcept
{
  int const result = mp_int_compare_zero(MP_NUMER_P(&big_->value));
  return result < 0 ? -1 : (result > 0 ? 1 : 0);
}

bool ExactRational::bigIsOne() const noexcept
{
  return mp_int_compare_value(MP_NUMER_P(&big_->value), 1) == 0 &&
         mp_int_compare_value(MP_DENOM_P(&big_->value), 1) == 0;
}

bool ExactRational::bigIsInteger() const noexcept
{
  return mp_rat_is_integer(&big_->value);
}

/* ---- construction ---------------------------------------------------- */

ExactRational::ExactRational(std::int64_t value)
    : numerator_(0), denominator_(1), big_(nullptr)
{
  char const* operation = "ExactRational(int64_t)";
  void* state = BudgetAccess::requireActive(operation);
  if (value <= kWordLimit && value >= -kWordLimit &&
      BudgetAccess::wordUnlimited(state))
  {
    numerator_ = value;
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    BudgetAccess::observeValue(state, wordBitCount(value), 1);
    return;
  }
  char buffer[64];
  std::string_view const numerator =
      integerCharacters(value, buffer, operation);
  preflightComponents(numerator, "1", state, operation);
  if (value <= kWordLimit && value >= -kWordLimit)
  {
    numerator_ = value;
    postCheckWord(numerator_, 1, state, operation);
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    return;
  }
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_CONSTRUCT);
  mp_rat const native = promoteToBig(*this, state, operation);
  setFromComponents(native, numerator, "1", operation);
  finishBigConstruction(*this, state, NumberMetricEvent::Construct, operation);
}

ExactRational::ExactRational(std::uint64_t value)
    : numerator_(0), denominator_(1), big_(nullptr)
{
  char const* operation = "ExactRational(uint64_t)";
  void* state = BudgetAccess::requireActive(operation);
  if (value <= static_cast<std::uint64_t>(kWordLimit) &&
      BudgetAccess::wordUnlimited(state))
  {
    numerator_ = static_cast<std::int64_t>(value);
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    BudgetAccess::observeValue(state, wordBitCount(numerator_), 1);
    return;
  }
  char buffer[64];
  std::string_view const numerator =
      integerCharacters(value, buffer, operation);
  preflightComponents(numerator, "1", state, operation);
  if (value <= static_cast<std::uint64_t>(kWordLimit))
  {
    numerator_ = static_cast<std::int64_t>(value);
    postCheckWord(numerator_, 1, state, operation);
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    return;
  }
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_CONSTRUCT);
  mp_rat const native = promoteToBig(*this, state, operation);
  setFromComponents(native, numerator, "1", operation);
  finishBigConstruction(*this, state, NumberMetricEvent::Construct, operation);
}

ExactRational::ExactRational(std::int64_t numerator,
                             std::uint64_t denominator)
    : numerator_(0), denominator_(1), big_(nullptr)
{
  char const* operation = "ExactRational(int64_t,uint64_t)";
  void* state = BudgetAccess::requireActive(operation);
  if (denominator == 0)
  {
    throw NumberFailure(NumberFailureKind::ZeroDenominator,
                        operation,
                        "zero denominator");
  }
  if (numerator <= kWordLimit && numerator >= -kWordLimit &&
      denominator <= static_cast<std::uint64_t>(kWordLimit) &&
      BudgetAccess::wordUnlimited(state))
  {
    std::int64_t const signed_denominator =
        static_cast<std::int64_t>(denominator);
    if (numerator == 0)
    {
      numerator_ = 0;
      denominator_ = 1;
    }
    else
    {
      std::uint64_t const shared = gcd64(magnitude64(numerator), denominator);
      numerator_ = numerator / static_cast<std::int64_t>(shared);
      denominator_ = signed_denominator / static_cast<std::int64_t>(shared);
    }
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    BudgetAccess::observeValue(state, wordBitCount(numerator_),
                               wordBitCount(denominator_));
    return;
  }
  char numerator_buffer[64];
  char denominator_buffer[64];
  std::string_view const numerator_text =
      integerCharacters(numerator, numerator_buffer, operation);
  std::string_view const denominator_text =
      integerCharacters(denominator, denominator_buffer, operation);
  preflightComponents(numerator_text, denominator_text, state, operation);
  std::int64_t word_numerator = 0;
  std::int64_t word_denominator = 1;
  if (componentsAsWord(numerator_text, denominator_text, word_numerator,
                       word_denominator))
  {
    numerator_ = word_numerator;
    denominator_ = word_denominator;
    postCheckWord(numerator_, denominator_, state, operation);
    BudgetAccess::record(state, NumberMetricEvent::Construct);
    return;
  }
  AllocationSiteScope site(STP_LRA_IMATH_ALLOCATION_CONSTRUCT);
  mp_rat const native = promoteToBig(*this, state, operation);
  setFromComponents(native, numerator_text, denominator_text, operation);
  finishBigConstruction(*this, state, NumberMetricEvent::Construct, operation);
}

ExactRational ExactRational::fromCanonicalIntegers(
    std::string_view numerator,
    std::string_view denominator)
{
  char const* operation = "fromCanonicalIntegers";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Parse);
  return constructFromComponents(numerator, denominator, state, operation);
}

ExactRational ExactRational::parseDecimalOrFraction(std::string_view text)
{
  char const* operation = "parseDecimalOrFraction";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Parse);
  std::uint64_t const input_bytes = checkedAdd(
      static_cast<std::uint64_t>(text.size()), 1, state, operation,
      "input string size");
  checkStringBytes(input_bytes, state, operation, "input string bytes");
  if (text.empty() || text.front() == '+' || text.front() == '.' ||
      text.back() == '.')
  {
    throw NumberFailure(NumberFailureKind::InvalidText, operation,
                        "invalid decimal or fraction grammar");
  }
  std::size_t const slash = text.find('/');
  std::size_t const point = text.find('.');
  if (slash != std::string_view::npos)
  {
    if (point != std::string_view::npos ||
        text.find('/', slash + 1) != std::string_view::npos)
    {
      throw NumberFailure(NumberFailureKind::InvalidText, operation,
                          "invalid fraction grammar");
    }
    std::string_view const numerator = text.substr(0, slash);
    std::string_view const denominator = text.substr(slash + 1);
    if (!signedDecimalInteger(numerator) ||
        !unsignedDecimal(denominator))
    {
      throw NumberFailure(NumberFailureKind::InvalidText, operation,
                          "invalid fraction grammar");
    }
    return constructFromComponents(numerator, denominator, state, operation);
  }
  if (point == std::string_view::npos)
  {
    if (!signedDecimalInteger(text))
    {
      throw NumberFailure(NumberFailureKind::InvalidText, operation,
                          "invalid integer grammar");
    }
    return constructFromComponents(text, "1", state, operation);
  }
  if (text.find('.', point + 1) != std::string_view::npos)
  {
    throw NumberFailure(NumberFailureKind::InvalidText, operation,
                        "multiple decimal points");
  }
  std::string_view integer_part = text.substr(0, point);
  std::string_view const fraction_part = text.substr(point + 1);
  bool const negative = !integer_part.empty() && integer_part.front() == '-';
  if (negative)
  {
    integer_part.remove_prefix(1);
  }
  if (!unsignedDecimal(integer_part) || !unsignedDecimal(fraction_part))
  {
    throw NumberFailure(NumberFailureKind::InvalidText, operation,
                        "invalid finite decimal grammar");
  }
  std::uint64_t numerator_bytes = checkedAdd(
      static_cast<std::uint64_t>(integer_part.size()),
      static_cast<std::uint64_t>(fraction_part.size()), state, operation,
      "finite-decimal numerator size");
  numerator_bytes = checkedAdd(numerator_bytes, negative ? 2 : 1, state,
                               operation, "finite-decimal numerator size");
  std::uint64_t const denominator_bytes = checkedAdd(
      static_cast<std::uint64_t>(fraction_part.size()), 2, state, operation,
      "finite-decimal denominator size");
  checkStringBytes(numerator_bytes, state, operation,
                   "finite-decimal numerator bytes");
  checkStringBytes(denominator_bytes, state, operation,
                   "finite-decimal denominator bytes");
  std::string numerator;
  std::string denominator;
  try
  {
    numerator.reserve(integer_part.size() + fraction_part.size() +
                      (negative ? 1U : 0U));
    if (negative)
    {
      numerator.push_back('-');
    }
    numerator.append(integer_part);
    numerator.append(fraction_part);
    denominator.assign(1, '1');
    denominator.append(fraction_part.size(), '0');
  }
  catch (std::bad_alloc const&)
  {
    throwStandardAllocation(operation);
  }
  return constructFromComponents(numerator, denominator, state, operation);
}

/* ---- text, widths, hashing ------------------------------------------- */

std::string ExactRational::numeratorDecimal() const
{
  char const* operation = "numeratorDecimal";
  void* state = BudgetAccess::requireActive(operation);
  checkOperand(*this, state, operation);
  if (big_ == nullptr)
  {
    return wordDecimal(numerator_, operation);
  }
  return integerDecimal(MP_NUMER_P(&big_->value), state, operation);
}

std::string ExactRational::denominatorDecimal() const
{
  char const* operation = "denominatorDecimal";
  void* state = BudgetAccess::requireActive(operation);
  checkOperand(*this, state, operation);
  if (big_ == nullptr)
  {
    return wordDecimal(denominator_, operation);
  }
  return integerDecimal(MP_DENOM_P(&big_->value), state, operation);
}

std::string ExactRational::canonicalFraction() const
{
  char const* operation = "canonicalFraction";
  void* state = BudgetAccess::requireActive(operation);
  checkOperand(*this, state, operation);
  if (big_ == nullptr)
  {
    std::string text = wordDecimal(numerator_, operation);
    if (denominator_ != 1)
    {
      try
      {
        text.push_back('/');
        text += wordDecimal(denominator_, operation);
      }
      catch (std::bad_alloc const&)
      {
        throwStandardAllocation(operation);
      }
    }
    return text;
  }
  mp_rat native = &big_->value;
  std::uint64_t const numerator_length =
      decimalBufferBytes(MP_NUMER_P(native), state, operation);
  if (isInteger())
  {
    checkStringBytes(numerator_length, state, operation,
                     "canonical output bytes");
    return integerDecimal(MP_NUMER_P(native), state, operation);
  }
  std::uint64_t const denominator_length =
      decimalBufferBytes(MP_DENOM_P(native), state, operation);
  std::uint64_t const combined = checkedAdd(
      numerator_length, denominator_length, state, operation,
      "canonical output size");
  checkStringBytes(combined, state, operation, "canonical output bytes");
  std::string numerator = integerDecimal(MP_NUMER_P(native), state, operation);
  std::string denominator =
      integerDecimal(MP_DENOM_P(native), state, operation);
  try
  {
    numerator.push_back('/');
    numerator += denominator;
  }
  catch (std::bad_alloc const&)
  {
    throwStandardAllocation(operation);
  }
  return numerator;
}

std::uint64_t ExactRational::numeratorBits() const noexcept
{
  if (big_ == nullptr)
  {
    return wordBitCount(numerator_);
  }
  return mp_int_count_bits(MP_NUMER_P(&big_->value));
}

std::uint64_t ExactRational::denominatorBits() const noexcept
{
  if (big_ == nullptr)
  {
    return wordBitCount(denominator_);
  }
  return mp_int_count_bits(MP_DENOM_P(&big_->value));
}

std::uint64_t ExactRational::stableHash() const
{
  std::string const numerator = numeratorDecimal();
  std::string const denominator = denominatorDecimal();
  std::uint64_t hash = UINT64_C(14695981039346656037);
  auto consume = [&hash](std::string const& text) {
    for (char byte : text)
    {
      hash ^= static_cast<unsigned char>(byte);
      hash *= UINT64_C(1099511628211);
    }
  };
  consume(numerator);
  hash ^= static_cast<unsigned char>('/');
  hash *= UINT64_C(1099511628211);
  consume(denominator);
  return hash;
}

std::optional<SmallRational> ExactRational::trySmall() const noexcept
{
  if (big_ == nullptr)
  {
    return SmallRational{numerator_, static_cast<std::uint64_t>(denominator_)};
  }
  mp_rat native = &big_->value;
  bool numerator_fits = false;
  bool denominator_fits = false;
  std::uint64_t const numerator_magnitude =
      magnitudeAsUint64(MP_NUMER_P(native), numerator_fits);
  std::uint64_t const denominator =
      magnitudeAsUint64(MP_DENOM_P(native), denominator_fits);
  if (!numerator_fits || !denominator_fits || denominator == 0 ||
      MP_SIGN(MP_DENOM_P(native)) != MP_ZPOS)
  {
    return std::nullopt;
  }
  std::int64_t numerator = 0;
  if (MP_SIGN(MP_NUMER_P(native)) == MP_NEG)
  {
    std::uint64_t const minimum_magnitude =
        UINT64_C(1) << (std::numeric_limits<std::uint64_t>::digits - 1);
    if (numerator_magnitude > minimum_magnitude)
    {
      return std::nullopt;
    }
    if (numerator_magnitude == minimum_magnitude)
    {
      numerator = std::numeric_limits<std::int64_t>::min();
    }
    else
    {
      numerator = -static_cast<std::int64_t>(numerator_magnitude);
    }
  }
  else
  {
    if (numerator_magnitude >
        static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()))
    {
      return std::nullopt;
    }
    numerator = static_cast<std::int64_t>(numerator_magnitude);
  }
  return SmallRational{numerator, denominator};
}

/* ---- comparison and predicates --------------------------------------- */

int ExactRational::compare(ExactRational const& other) const
{
  char const* operation = "compare";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Compare);
  bool const both_words = big_ == nullptr && other.big_ == nullptr;
  if (!(BudgetAccess::wordUnlimited(state) && both_words))
  {
    checkOperand(*this, state, operation);
    checkOperand(other, state, operation);
    std::uint64_t const left_bits =
        bitSum(numeratorBits(), other.denominatorBits(), state, operation);
    std::uint64_t const right_bits =
        bitSum(other.numeratorBits(), denominatorBits(), state, operation);
    checkResultEstimate(left_bits, right_bits, state, operation);
  }
  if (both_words)
  {
    int word_sign = 0;
    if (denominator_ == other.denominator_)
    {
      word_sign = numerator_ < other.numerator_
                      ? -1
                      : (numerator_ > other.numerator_ ? 1 : 0);
    }
    else
    {
      wide_t const left_cross =
          static_cast<wide_t>(numerator_) * other.denominator_;
      wide_t const right_cross =
          static_cast<wide_t>(other.numerator_) * denominator_;
      word_sign =
          left_cross < right_cross ? -1 : (left_cross > right_cross ? 1 : 0);
    }
    return word_sign;
  }
  NativeInteger left(operation);
  NativeInteger right(operation);
  checkedNative(operation, [&] {
    return mp_int_mul(MP_NUMER_P(ExactRationalAccess::native(*this)),
                      MP_DENOM_P(ExactRationalAccess::native(other)),
                      &left.value);
  });
  checkedNative(operation, [&] {
    return mp_int_mul(MP_NUMER_P(ExactRationalAccess::native(other)),
                      MP_DENOM_P(ExactRationalAccess::native(*this)),
                      &right.value);
  });
  int const result = mp_int_compare(&left.value, &right.value);
  int const exact_sign = result < 0 ? -1 : (result > 0 ? 1 : 0);
  return exact_sign;
}

bool ExactRational::invariantHolds() const noexcept
{
  if (big_ == nullptr)
  {
    if (denominator_ <= 0 || denominator_ > kWordLimit ||
        numerator_ > kWordLimit || numerator_ < -kWordLimit)
    {
      return false;
    }
    if (numerator_ == 0)
    {
      return denominator_ == 1;
    }
    return gcd64(magnitude64(numerator_),
                 static_cast<std::uint64_t>(denominator_)) == 1;
  }
  if (BudgetAccess::active() == nullptr)
  {
    return false;
  }
  try
  {
    return checkedInvariant(&big_->value, "invariantHolds");
  }
  catch (...)
  {
    return false;
  }
}

/* ---- unary operations ------------------------------------------------ */

ExactRational& ExactRational::negate()
{
  char const* operation = "negate";
  void* state = BudgetAccess::requireActive(operation);
  if (big_ == nullptr)
  {
    if (!BudgetAccess::wordUnlimited(state))
    {
      checkOperand(*this, state, operation);
      checkResultEstimate(numeratorBits(), denominatorBits(), state,
                          operation);
    }
    numerator_ = -numerator_;
    postCheckWord(numerator_, denominator_, state, operation);
    return *this;
  }
  checkOperand(*this, state, operation);
  checkResultEstimate(numeratorBits(), denominatorBits(), state, operation);
  ExactRational result;
  mp_rat const target = promoteToBig(result, state, operation);
  checkedNative(operation, [&] { return mp_rat_neg(&big_->value, target); });
  postCheck(target, state, operation);
  swap(result);
  return *this;
}

ExactRational ExactRational::operator-() const
{
  ExactRational result(*this);
  result.negate();
  return result;
}

ExactRational ExactRational::inverse() const
{
  char const* operation = "inverse";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Divide);
  if (isZero())
  {
    throw NumberFailure(NumberFailureKind::DivisionByZero, operation,
                        "inverse of zero");
  }
  if (big_ == nullptr)
  {
    /* The reciprocal of a canonical word is canonical: the same coprime
     * pair the other way up, with the sign moved onto the numerator. */
    if (!BudgetAccess::wordUnlimited(state))
    {
      checkOperand(*this, state, operation);
      checkResultEstimate(denominatorBits(), numeratorBits(), state,
                          operation);
    }
    ExactRational result;
    if (numerator_ < 0)
    {
      result.numerator_ = -denominator_;
      result.denominator_ = -numerator_;
    }
    else
    {
      result.numerator_ = denominator_;
      result.denominator_ = numerator_;
    }
    postCheckWord(result.numerator_, result.denominator_, state, operation);
    return result;
  }
  checkOperand(*this, state, operation);
  checkResultEstimate(denominatorBits(), numeratorBits(), state, operation);
  ExactRational result;
  mp_rat const target = promoteToBig(result, state, operation);
  checkedNative(operation,
                [&] { return mp_rat_recip(&big_->value, target); },
                NumberFailureKind::DivisionByZero);
  postCheck(target, state, operation);
  tryDemote(result);
  return result;
}

namespace {

/* floor(n/d) over words, d > 0: truncation rounds toward zero, so a
 * negative inexact quotient steps down once. */
std::int64_t wordFloor(std::int64_t numerator, std::int64_t denominator) noexcept
{
  std::int64_t const quotient = numerator / denominator;
  return (numerator % denominator != 0 && numerator < 0) ? quotient - 1
                                                          : quotient;
}

std::int64_t wordCeil(std::int64_t numerator, std::int64_t denominator) noexcept
{
  std::int64_t const quotient = numerator / denominator;
  return (numerator % denominator != 0 && numerator > 0) ? quotient + 1
                                                          : quotient;
}

ExactRational wordInteger(std::int64_t value, void* state, char const* operation)
{
  ExactRational result;
  ExactRationalAccess::setWord(result, value, 1);
  postCheckWord(value, 1, state, operation);
  return result;
}

}  // namespace

ExactRational ExactRational::floor() const
{
  char const* operation = "floor";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::FloorDivide);
  if (big_ == nullptr)
  {
    if (!BudgetAccess::wordUnlimited(state))
    {
      checkOperand(*this, state, operation);
      checkResultEstimate(checkedAdd(numeratorBits(), 1, state, operation,
                                     "floor result bit estimate"),
                          1, state, operation);
    }
    return wordInteger(wordFloor(numerator_, denominator_), state, operation);
  }
  checkOperand(*this, state, operation);
  checkResultEstimate(checkedAdd(numeratorBits(), 1, state, operation,
                                 "floor result bit estimate"),
                      1, state, operation);
  NativeInteger quotient(operation);
  NativeInteger remainder(operation);
  checkedNative(operation, [&] {
    return mp_int_div(MP_NUMER_P(&big_->value), MP_DENOM_P(&big_->value),
                      &quotient.value, &remainder.value);
  });
  if (sign() < 0 && mp_int_compare_zero(&remainder.value) != 0)
  {
    checkedNative(operation, [&] {
      return mp_int_sub_value(&quotient.value, 1, &quotient.value);
    });
  }
  return fromNativeInteger(&quotient.value, state, operation);
}

ExactRational ExactRational::ceil() const
{
  char const* operation = "ceil";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::FloorDivide);
  if (big_ == nullptr)
  {
    if (!BudgetAccess::wordUnlimited(state))
    {
      checkOperand(*this, state, operation);
      checkResultEstimate(checkedAdd(numeratorBits(), 1, state, operation,
                                     "ceil result bit estimate"),
                          1, state, operation);
    }
    return wordInteger(wordCeil(numerator_, denominator_), state, operation);
  }
  checkOperand(*this, state, operation);
  checkResultEstimate(checkedAdd(numeratorBits(), 1, state, operation,
                                 "ceil result bit estimate"),
                      1, state, operation);
  NativeInteger quotient(operation);
  NativeInteger remainder(operation);
  checkedNative(operation, [&] {
    return mp_int_div(MP_NUMER_P(&big_->value), MP_DENOM_P(&big_->value),
                      &quotient.value, &remainder.value);
  });
  if (sign() > 0 && mp_int_compare_zero(&remainder.value) != 0)
  {
    checkedNative(operation, [&] {
      return mp_int_add_value(&quotient.value, 1, &quotient.value);
    });
  }
  return fromNativeInteger(&quotient.value, state, operation);
}

ExactRational ExactRational::integerModulo(
    ExactRational const& divisor) const
{
  char const* operation = "integerModulo";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::FloorDivide);
  requireInteger(*this, operation);
  requireInteger(divisor, operation);
  if (divisor.isZero())
  {
    throw NumberFailure(NumberFailureKind::DivisionByZero, operation,
                        "zero divisor");
  }
  if (big_ == nullptr && divisor.big_ == nullptr)
  {
    if (!BudgetAccess::wordUnlimited(state))
    {
      checkOperand(*this, state, operation);
      checkOperand(divisor, state, operation);
      checkResultEstimate(divisor.numeratorBits(), 1, state, operation);
    }
    /* The remainder takes the divisor's sign, as the big path arranges. */
    std::int64_t remainder = numerator_ % divisor.numerator_;
    if (remainder != 0 && (numerator_ < 0) != (divisor.numerator_ < 0))
    {
      remainder += divisor.numerator_;
    }
    return wordInteger(remainder, state, operation);
  }
  checkOperand(*this, state, operation);
  checkOperand(divisor, state, operation);
  checkResultEstimate(divisor.numeratorBits(), 1, state, operation);
  NativeInteger quotient(operation);
  NativeInteger remainder(operation);
  mp_int dividend = MP_NUMER_P(ExactRationalAccess::native(*this));
  mp_int native_divisor =
      MP_NUMER_P(ExactRationalAccess::native(divisor));
  checkedNative(operation, [&] {
    return mp_int_div(dividend, native_divisor, &quotient.value,
                      &remainder.value);
  });
  if (mp_int_compare_zero(&remainder.value) != 0 &&
      (mp_int_compare_zero(dividend) < 0) !=
          (mp_int_compare_zero(native_divisor) < 0))
  {
    checkedNative(operation, [&] {
      return mp_int_add(&remainder.value, native_divisor, &remainder.value);
    });
  }
  return fromNativeInteger(&remainder.value, state, operation);
}

/* ---- binary operations ----------------------------------------------- */

ExactRational& ExactRational::operator+=(ExactRational const& other)
{
  add(*this, *this, other);
  return *this;
}

ExactRational& ExactRational::operator-=(ExactRational const& other)
{
  subtract(*this, *this, other);
  return *this;
}

ExactRational& ExactRational::operator*=(ExactRational const& other)
{
  multiply(*this, *this, other);
  return *this;
}

ExactRational& ExactRational::operator/=(ExactRational const& other)
{
  divide(*this, *this, other);
  return *this;
}

ExactRational operator+(ExactRational lhs, ExactRational const& rhs)
{
  lhs += rhs;
  return lhs;
}

ExactRational operator-(ExactRational lhs, ExactRational const& rhs)
{
  lhs -= rhs;
  return lhs;
}

ExactRational operator*(ExactRational lhs, ExactRational const& rhs)
{
  lhs *= rhs;
  return lhs;
}

ExactRational operator/(ExactRational lhs, ExactRational const& rhs)
{
  lhs /= rhs;
  return lhs;
}

bool operator==(ExactRational const& lhs, ExactRational const& rhs)
{
  bool const left_word = lhs.big_ == nullptr;
  bool const right_word = rhs.big_ == nullptr;
  if (left_word && right_word)
  {
    return lhs.numerator_ == rhs.numerator_ &&
           lhs.denominator_ == rhs.denominator_;
  }
  if (left_word != right_word)
  {
    ExactRational const& worded = left_word ? lhs : rhs;
    ExactRational const& other = left_word ? rhs : lhs;
    std::int64_t numerator = 0;
    std::int64_t denominator = 1;
    if (!nativeAsWord(other.big_->value, numerator, denominator))
    {
      return false;
    }
    return worded.numerator_ == numerator &&
           worded.denominator_ == denominator;
  }
  mp_rat left_native = &lhs.big_->value;
  mp_rat right_native = &rhs.big_->value;
  return mp_int_compare(MP_NUMER_P(left_native),
                        MP_NUMER_P(right_native)) == 0 &&
         mp_int_compare(MP_DENOM_P(left_native),
                        MP_DENOM_P(right_native)) == 0;
}

bool operator!=(ExactRational const& lhs, ExactRational const& rhs)
{
  return !(lhs == rhs);
}

bool operator<(ExactRational const& lhs, ExactRational const& rhs)
{
  return lhs.compare(rhs) < 0;
}

bool operator<=(ExactRational const& lhs, ExactRational const& rhs)
{
  return lhs.compare(rhs) <= 0;
}

bool operator>(ExactRational const& lhs, ExactRational const& rhs)
{
  return lhs.compare(rhs) > 0;
}

bool operator>=(ExactRational const& lhs, ExactRational const& rhs)
{
  return lhs.compare(rhs) >= 0;
}

void add(ExactRational& out,
         ExactRational const& lhs,
         ExactRational const& rhs)
{
  arithmetic<ArithmeticOperation::Add>(out, lhs, rhs);
}

void subtract(ExactRational& out,
              ExactRational const& lhs,
              ExactRational const& rhs)
{
  arithmetic<ArithmeticOperation::Subtract>(out, lhs, rhs);
}

void multiply(ExactRational& out,
              ExactRational const& lhs,
              ExactRational const& rhs)
{
  arithmetic<ArithmeticOperation::Multiply>(out, lhs, rhs);
}

void divide(ExactRational& out,
            ExactRational const& lhs,
            ExactRational const& rhs)
{
  arithmetic<ArithmeticOperation::Divide>(out, lhs, rhs);
}

/* ---- integer operations ---------------------------------------------- */

ExactRational integerGcd(ExactRational const& lhs,
                         ExactRational const& rhs)
{
  char const* operation = "integerGcd";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Gcd);
  requireInteger(lhs, operation);
  requireInteger(rhs, operation);
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(std::max(lhs.numeratorBits(), rhs.numeratorBits()), 1,
                      state, operation);
  if (lhs.isZero() && rhs.isZero())
  {
    return ExactRational{};
  }
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs))
  {
    std::uint64_t const shared =
        gcd64(magnitude64(ExactRationalAccess::wordNumerator(lhs)),
              magnitude64(ExactRationalAccess::wordNumerator(rhs)));
    return wordInteger(static_cast<std::int64_t>(shared), state, operation);
  }
  NativeInteger result(operation);
  checkedNative(operation, [&] {
    return mp_int_gcd(MP_NUMER_P(ExactRationalAccess::native(lhs)),
                      MP_NUMER_P(ExactRationalAccess::native(rhs)),
                      &result.value);
  });
  return fromNativeInteger(&result.value, state, operation);
}

ExactRational integerLcm(ExactRational const& lhs,
                         ExactRational const& rhs)
{
  char const* operation = "integerLcm";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Gcd);
  requireInteger(lhs, operation);
  requireInteger(rhs, operation);
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(
      bitSum(lhs.numeratorBits(), rhs.numeratorBits(), state, operation), 1,
      state, operation);
  if (lhs.isZero() || rhs.isZero())
  {
    return ExactRational{};
  }
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs))
  {
    std::uint64_t const a = magnitude64(ExactRationalAccess::wordNumerator(lhs));
    std::uint64_t const b = magnitude64(ExactRationalAccess::wordNumerator(rhs));
    wide_t const product =
        static_cast<wide_t>(a / gcd64(a, b)) * static_cast<wide_t>(b);
    if (fitsWord(product, 1))
    {
      return wordInteger(static_cast<std::int64_t>(product), state, operation);
    }
  }
  NativeInteger result(operation);
  checkedNative(operation, [&] {
    return mp_int_lcm(MP_NUMER_P(ExactRationalAccess::native(lhs)),
                      MP_NUMER_P(ExactRationalAccess::native(rhs)),
                      &result.value);
  });
  checkedNative(operation,
                [&] { return mp_int_abs(&result.value, &result.value); });
  return fromNativeInteger(&result.value, state, operation);
}

ExactRational exactIntegerDivide(ExactRational const& lhs,
                                 ExactRational const& rhs)
{
  char const* operation = "exactIntegerDivide";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::Divide);
  requireInteger(lhs, operation);
  requireInteger(rhs, operation);
  if (rhs.isZero())
  {
    throw NumberFailure(NumberFailureKind::DivisionByZero, operation,
                        "zero divisor");
  }
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(lhs.numeratorBits(), 1, state, operation);
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs))
  {
    std::int64_t const dividend = ExactRationalAccess::wordNumerator(lhs);
    std::int64_t const divisor = ExactRationalAccess::wordNumerator(rhs);
    if (dividend % divisor != 0)
    {
      throw NumberFailure(NumberFailureKind::NonIntegerOperand,
                          operation,
                          "division has a nonzero remainder");
    }
    return wordInteger(dividend / divisor, state, operation);
  }
  NativeInteger quotient(operation);
  NativeInteger remainder(operation);
  checkedNative(operation, [&] {
    return mp_int_div(MP_NUMER_P(ExactRationalAccess::native(lhs)),
                      MP_NUMER_P(ExactRationalAccess::native(rhs)),
                      &quotient.value, &remainder.value);
  });
  if (mp_int_compare_zero(&remainder.value) != 0)
  {
    throw NumberFailure(NumberFailureKind::NonIntegerOperand,
                        operation,
                        "division has a nonzero remainder");
  }
  return fromNativeInteger(&quotient.value, state, operation);
}

ExactRational floorIntegerDivide(ExactRational const& lhs,
                                 ExactRational const& rhs)
{
  char const* operation = "floorIntegerDivide";
  void* state = BudgetAccess::requireActive(operation);
  BudgetAccess::record(state, NumberMetricEvent::FloorDivide);
  requireInteger(lhs, operation);
  requireInteger(rhs, operation);
  if (rhs.isZero())
  {
    throw NumberFailure(NumberFailureKind::DivisionByZero, operation,
                        "zero divisor");
  }
  checkOperand(lhs, state, operation);
  checkOperand(rhs, state, operation);
  checkResultEstimate(checkedAdd(lhs.numeratorBits(), 1, state, operation,
                                 "floor division bit estimate"),
                      1, state, operation);
  if (ExactRationalAccess::isWord(lhs) && ExactRationalAccess::isWord(rhs))
  {
    std::int64_t const dividend = ExactRationalAccess::wordNumerator(lhs);
    std::int64_t const divisor = ExactRationalAccess::wordNumerator(rhs);
    std::int64_t quotient = dividend / divisor;
    if (dividend % divisor != 0 && (dividend < 0) != (divisor < 0))
    {
      --quotient;
    }
    return wordInteger(quotient, state, operation);
  }
  NativeInteger quotient(operation);
  NativeInteger remainder(operation);
  mp_int dividend = MP_NUMER_P(ExactRationalAccess::native(lhs));
  mp_int divisor = MP_NUMER_P(ExactRationalAccess::native(rhs));
  checkedNative(operation, [&] {
    return mp_int_div(dividend, divisor, &quotient.value, &remainder.value);
  });
  if (mp_int_compare_zero(&remainder.value) != 0 &&
      (mp_int_compare_zero(dividend) < 0) !=
          (mp_int_compare_zero(divisor) < 0))
  {
    checkedNative(operation, [&] {
      return mp_int_sub_value(&quotient.value, 1, &quotient.value);
    });
  }
  return fromNativeInteger(&quotient.value, state, operation);
}

std::size_t ExactRationalHash::operator()(ExactRational const& value) const
{
  std::uint64_t const hash = value.stableHash();
  if constexpr (sizeof(std::size_t) >= sizeof(std::uint64_t))
  {
    return static_cast<std::size_t>(hash);
  }
  else
  {
    return static_cast<std::size_t>(hash ^ (hash >> 32));
  }
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void detail::testEstimateOverflow()
{
  char const* operation = "testEstimateOverflow";
  void* state = BudgetAccess::requireActive(operation);
  (void)checkedAdd(std::numeric_limits<std::uint64_t>::max(), 1, state,
                   operation, "test bit estimate");
}

void detail::testPostResultLimit(ExactRational const& value)
{
  char const* operation = "testPostResultLimit";
  void* state = BudgetAccess::requireActive(operation);
  postCheck(ExactRationalAccess::native(value), state, operation);
}
#endif

}  // namespace stp::lra

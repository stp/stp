#ifndef STP_LRA_EXACT_RATIONAL_H
#define STP_LRA_EXACT_RATIONAL_H

#include "NumberBudget.h"
#include <imrat.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

namespace stp::lra {

struct SmallRational
{
  std::int64_t numerator;
  std::uint64_t denominator;
};

namespace detail {
/* The heap form of a value that has outgrown machine words, or that
 * something asked for natively: a live IMath rational and the budget it is
 * accounted to.  The budget pointer is what keeps the value's metrics exact
 * when it is destroyed after the operation scope that made it has ended;
 * the budget-outlives-values contract keeps the pointer stable. */
struct BigRational
{
  imath_rat_value value;
  void* budget_state;
};

struct ExactRationalAccess;
}  // namespace detail

/* An exact rational in one of two states.
 *
 * In the word state the value is exactly numerator_ / denominator_ --
 * canonical, denominator strictly positive, both within kWordLimit -- and
 * big_ is null.  Such a value is three machine words: it is created, copied,
 * moved, swapped and destroyed inline with no allocation and no accounting,
 * and its arithmetic runs in machine registers.  This is the usual
 * small-value fast path that keeps an exact rational simplex affordable: a
 * machine-word numerator and denominator, escaping to arbitrary precision
 * (here the fetched and patched IMath, not GMP) only when a result
 * overflows.
 *
 * In the big state big_ owns a heap BigRational and the word fields are
 * meaningless.  A value enters it when a result no longer fits a word, or
 * when something asks for the native representation; fresh results and
 * parsed values are demoted again when their canonical components fit.
 *
 * The budget's per-value metrics -- current_values, peak_values, destroys
 * -- count values in the big state, which are the ones that hold memory;
 * word-state values are free and uncounted.  Arithmetic, comparison and
 * construction are counted whatever the state, since those run under a
 * scope whose budget is at hand. */
class ExactRational final
{
 public:
  ExactRational() : numerator_(0), denominator_(1), big_(nullptr)
  {
    /* Zero costs nothing, but construction is an operation and keeps the
     * contract that every operation runs under a scope. */
    detail::BudgetAccess::record(
        detail::BudgetAccess::requireActive("ExactRational()"),
        detail::NumberMetricEvent::Construct);
  }
  ExactRational(std::int64_t);
  ExactRational(std::uint64_t);
  ExactRational(std::int64_t numerator, std::uint64_t denominator);

  static ExactRational parseDecimalOrFraction(std::string_view);
  static ExactRational fromCanonicalIntegers(std::string_view numerator,
                                             std::string_view denominator);

  ExactRational(ExactRational const& other)
      : numerator_(other.numerator_),
        denominator_(other.denominator_),
        big_(nullptr)
  {
    if (other.big_ != nullptr)
      copyBig(other);
    else
      copyWordChecked();
  }
  ExactRational(ExactRational&& other) noexcept
      : numerator_(other.numerator_),
        denominator_(other.denominator_),
        big_(other.big_)
  {
    other.numerator_ = 0;
    other.denominator_ = 1;
    other.big_ = nullptr;
  }
  ExactRational& operator=(ExactRational const& other)
  {
    if (this != &other)
    {
      if (other.big_ == nullptr)
      {
        releaseBig();
        numerator_ = other.numerator_;
        denominator_ = other.denominator_;
      }
      else
      {
        ExactRational copy(other);
        swap(copy);
      }
    }
    return *this;
  }
  ExactRational& operator=(ExactRational&& other) noexcept
  {
    if (this != &other)
    {
      releaseBig();
      numerator_ = other.numerator_;
      denominator_ = other.denominator_;
      big_ = other.big_;
      other.numerator_ = 0;
      other.denominator_ = 1;
      other.big_ = nullptr;
    }
    return *this;
  }
  ~ExactRational() noexcept
  {
    if (big_ != nullptr)
      destroyBig();
  }
  void swap(ExactRational& other) noexcept
  {
    std::swap(numerator_, other.numerator_);
    std::swap(denominator_, other.denominator_);
    std::swap(big_, other.big_);
  }

  std::string canonicalFraction() const;
  std::string numeratorDecimal() const;
  std::string denominatorDecimal() const;
  std::uint64_t numeratorBits() const noexcept;
  std::uint64_t denominatorBits() const noexcept;
  std::uint64_t stableHash() const;
  std::optional<SmallRational> trySmall() const noexcept;

  int compare(ExactRational const&) const;
  int sign() const noexcept
  {
    if (big_ == nullptr)
      return numerator_ < 0 ? -1 : (numerator_ > 0 ? 1 : 0);
    return bigSign();
  }
  bool isZero() const noexcept
  {
    return big_ == nullptr ? numerator_ == 0 : bigSign() == 0;
  }
  bool isOne() const noexcept
  {
    if (big_ == nullptr)
      return numerator_ == 1 && denominator_ == 1;
    return bigIsOne();
  }
  bool isInteger() const noexcept
  {
    if (big_ == nullptr)
      return denominator_ == 1;
    return bigIsInteger();
  }
  bool invariantHolds() const noexcept;

  ExactRational operator-() const;
  ExactRational inverse() const;
  ExactRational floor() const;
  ExactRational ceil() const;
  ExactRational integerModulo(ExactRational const&) const;
  ExactRational& negate();

  ExactRational& operator+=(ExactRational const&);
  ExactRational& operator-=(ExactRational const&);
  ExactRational& operator*=(ExactRational const&);
  ExactRational& operator/=(ExactRational const&);

  friend ExactRational operator+(ExactRational, ExactRational const&);
  friend ExactRational operator-(ExactRational, ExactRational const&);
  friend ExactRational operator*(ExactRational, ExactRational const&);
  friend ExactRational operator/(ExactRational, ExactRational const&);

  friend bool operator==(ExactRational const&, ExactRational const&);
  friend bool operator!=(ExactRational const&, ExactRational const&);
  friend bool operator<(ExactRational const&, ExactRational const&);
  friend bool operator<=(ExactRational const&, ExactRational const&);
  friend bool operator>(ExactRational const&, ExactRational const&);
  friend bool operator>=(ExactRational const&, ExactRational const&);

 private:
  void copyBig(ExactRational const& other);
  /* A word copy under a scope whose limits do not admit every word is an
   * operand check; under one that does, or under none, it is nothing. */
  void copyWordChecked()
  {
    void* const state = detail::BudgetAccess::active();
    if (state != nullptr && !detail::BudgetAccess::wordUnlimited(state))
      copyWordLimited(state);
  }
  void copyWordLimited(void* state);
  void destroyBig() noexcept;
  void releaseBig() noexcept
  {
    if (big_ != nullptr)
    {
      destroyBig();
      big_ = nullptr;
    }
  }
  int bigSign() const noexcept;
  bool bigIsOne() const noexcept;
  bool bigIsInteger() const noexcept;

  /* All three are mutable because materialisation is a representation
   * change, not a change of value: a const rational still has to be able
   * to hand out a native pointer, and a result that shrinks is demoted
   * back to words in place. */
  mutable std::int64_t numerator_;
  mutable std::int64_t denominator_;
  mutable detail::BigRational* big_;

  friend struct detail::ExactRationalAccess;
};

static_assert(sizeof(ExactRational) <= 3 * sizeof(std::int64_t),
              "an exact rational is at most three 64-bit words");

void add(ExactRational& out,
         ExactRational const& lhs,
         ExactRational const& rhs);
void subtract(ExactRational& out,
              ExactRational const& lhs,
              ExactRational const& rhs);
void multiply(ExactRational& out,
              ExactRational const& lhs,
              ExactRational const& rhs);
void divide(ExactRational& out,
            ExactRational const& lhs,
            ExactRational const& rhs);

ExactRational integerGcd(ExactRational const&, ExactRational const&);
ExactRational integerLcm(ExactRational const&, ExactRational const&);
ExactRational exactIntegerDivide(ExactRational const&, ExactRational const&);
ExactRational floorIntegerDivide(ExactRational const&, ExactRational const&);

struct ExactRationalHash
{
  std::size_t operator()(ExactRational const& value) const;
};

#if defined(STP_LRA_TEST_FAULT_INJECTION)
namespace detail {
void testEstimateOverflow();
void testPostResultLimit(ExactRational const& value);
}
#endif

}  // namespace stp::lra

#endif

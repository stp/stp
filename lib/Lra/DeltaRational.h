#ifndef STP_LRA_DELTA_RATIONAL_H
#define STP_LRA_DELTA_RATIONAL_H

#include "ExactRational.h"

#include <string>
#include <utility>

namespace stp::lra
{

/* A value of the form r + d * delta for an infinitesimal positive delta
 * (the delta-rationals of Dutertre & de Moura, CAV 2006): the number
 * field the exact tableau is evaluated in, so that a strict
 * bound x < c is the closed bound x <= c - delta and every assignment
 * the engine keeps is a genuine point of the relaxed polyhedron.
 * Comparison is lexicographic, the rational part first; a delta part
 * of zero is the common case and the arithmetic skips it. */
class DeltaRational final
{
 public:
  DeltaRational();
  explicit DeltaRational(ExactRational const& value);
  DeltaRational(ExactRational const& value, ExactRational const& infinitesimal);
  DeltaRational(ExactRational&& value, ExactRational&& infinitesimal) noexcept;

  DeltaRational(DeltaRational const&) = default;
  DeltaRational(DeltaRational&&) noexcept = default;
  DeltaRational& operator=(DeltaRational const&) = default;
  DeltaRational& operator=(DeltaRational&&) noexcept = default;
  ~DeltaRational() noexcept = default;

  ExactRational const& rational() const noexcept { return rational_; }
  ExactRational const& infinitesimal() const noexcept { return infinitesimal_; }

  /* The sign of the value: that of the rational part unless it is zero. */
  int sign() const;
  int compare(DeltaRational const&) const;
  bool isZero() const noexcept
  {
    return rational_.isZero() && infinitesimal_.isZero();
  }

  void swap(DeltaRational& other) noexcept
  {
    rational_.swap(other.rational_);
    infinitesimal_.swap(other.infinitesimal_);
  }
  void negate();

  DeltaRational& operator+=(DeltaRational const&);
  DeltaRational& operator-=(DeltaRational const&);
  DeltaRational& operator*=(ExactRational const&);
  DeltaRational& operator/=(ExactRational const&);
  /* *this += factor * other, without a temporary DeltaRational. */
  void addScaled(ExactRational const& factor, DeltaRational const& other);


  friend bool operator==(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return lhs.rational_ == rhs.rational_ &&
           lhs.infinitesimal_ == rhs.infinitesimal_;
  }
  friend bool operator!=(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return !(lhs == rhs);
  }
  friend bool operator<(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return lhs.compare(rhs) < 0;
  }
  friend bool operator<=(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return lhs.compare(rhs) <= 0;
  }
  friend bool operator>(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return lhs.compare(rhs) > 0;
  }
  friend bool operator>=(DeltaRational const& lhs, DeltaRational const& rhs)
  {
    return lhs.compare(rhs) >= 0;
  }

 private:
  ExactRational rational_;
  ExactRational infinitesimal_;
};

DeltaRational operator+(DeltaRational lhs, DeltaRational const& rhs);
DeltaRational operator-(DeltaRational lhs, DeltaRational const& rhs);
DeltaRational operator-(DeltaRational value);
DeltaRational operator*(ExactRational const& scalar, DeltaRational value);
DeltaRational operator*(DeltaRational value, ExactRational const& scalar);
DeltaRational operator/(DeltaRational value, ExactRational const& scalar);

}  // namespace stp::lra

#endif

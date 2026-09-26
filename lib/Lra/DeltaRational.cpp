#include "DeltaRational.h"

namespace stp::lra
{

DeltaRational::DeltaRational() : rational_(std::int64_t{0}), infinitesimal_(std::int64_t{0}) {}

DeltaRational::DeltaRational(ExactRational const& value)
    : rational_(value), infinitesimal_(std::int64_t{0})
{}

DeltaRational::DeltaRational(ExactRational const& value, ExactRational const& infinitesimal)
    : rational_(value), infinitesimal_(infinitesimal)
{}

DeltaRational::DeltaRational(ExactRational&& value, ExactRational&& infinitesimal) noexcept
    : rational_(std::move(value)), infinitesimal_(std::move(infinitesimal))
{}

int DeltaRational::sign() const
{
  int const rational_sign = rational_.sign();
  return rational_sign != 0 ? rational_sign : infinitesimal_.sign();
}

int DeltaRational::compare(DeltaRational const& other) const
{
  int const rational_order = rational_.compare(other.rational_);
  return rational_order != 0 ? rational_order
                             : infinitesimal_.compare(other.infinitesimal_);
}

void DeltaRational::negate()
{
  ExactRational rational = -rational_;
  rational_.swap(rational);
  if (!infinitesimal_.isZero())
  {
    ExactRational infinitesimal = -infinitesimal_;
    infinitesimal_.swap(infinitesimal);
  }
}


/* The in-place free functions leave their target untouched when they
 * throw, so the strong guarantee the swaps used to provide holds without a
 * temporary per component. */
DeltaRational& DeltaRational::operator+=(DeltaRational const& other)
{
  add(rational_, rational_, other.rational_);
  if (!other.infinitesimal_.isZero())
    add(infinitesimal_, infinitesimal_, other.infinitesimal_);
  return *this;
}

DeltaRational& DeltaRational::operator-=(DeltaRational const& other)
{
  subtract(rational_, rational_, other.rational_);
  if (!other.infinitesimal_.isZero())
    subtract(infinitesimal_, infinitesimal_, other.infinitesimal_);
  return *this;
}

DeltaRational& DeltaRational::operator*=(ExactRational const& scalar)
{
  multiply(rational_, rational_, scalar);
  if (!infinitesimal_.isZero())
    multiply(infinitesimal_, infinitesimal_, scalar);
  return *this;
}

DeltaRational& DeltaRational::operator/=(ExactRational const& scalar)
{
  divide(rational_, rational_, scalar);
  if (!infinitesimal_.isZero())
    divide(infinitesimal_, infinitesimal_, scalar);
  return *this;
}

void DeltaRational::addScaled(ExactRational const& factor, DeltaRational const& other)
{
  ExactRational product;
  multiply(product, other.rational_, factor);
  add(rational_, rational_, product);
  if (!other.infinitesimal_.isZero())
  {
    multiply(product, other.infinitesimal_, factor);
    add(infinitesimal_, infinitesimal_, product);
  }
}


DeltaRational operator+(DeltaRational lhs, DeltaRational const& rhs)
{
  lhs += rhs;
  return lhs;
}

DeltaRational operator-(DeltaRational lhs, DeltaRational const& rhs)
{
  lhs -= rhs;
  return lhs;
}

DeltaRational operator-(DeltaRational value)
{
  value.negate();
  return value;
}

DeltaRational operator*(ExactRational const& scalar, DeltaRational value)
{
  value *= scalar;
  return value;
}

DeltaRational operator*(DeltaRational value, ExactRational const& scalar)
{
  value *= scalar;
  return value;
}

DeltaRational operator/(DeltaRational value, ExactRational const& scalar)
{
  value /= scalar;
  return value;
}

}  // namespace stp::lra

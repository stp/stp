/********************************************************************
 * Immutable source-language sorts.
 *
 * STP's historical `types` describe the bit-vector/array carrier used by
 * the solving pipeline.  FloatingPoint and RoundingMode are lowered onto
 * those carriers, but they are not interchangeable with them at the public
 * boundary.  SourceSort records that distinction without changing the
 * representation expected by the legacy bit-vector passes.
 ********************************************************************/
#ifndef STP_SOURCESORT_H
#define STP_SOURCESORT_H

#include <cassert>
#include <cstddef>
#include <memory>
#include <string>
#include <unordered_set>

namespace stp
{

class SourceSort final
{
public:
  enum class Kind
  {
    Unknown,
    Bool,
    BitVector,
    FloatingPoint,
    RoundingMode,
    Array
  };

private:
  Kind kind_;
  unsigned first_;
  unsigned second_;
  std::shared_ptr<const SourceSort> index_;
  std::shared_ptr<const SourceSort> element_;

  SourceSort(Kind kind, unsigned first = 0, unsigned second = 0)
      : kind_(kind), first_(first), second_(second)
  {
  }

  SourceSort(const SourceSort& index, const SourceSort& element)
      : kind_(Kind::Array), first_(0), second_(0),
        index_(std::make_shared<const SourceSort>(index)),
        element_(std::make_shared<const SourceSort>(element))
  {
  }

public:
  SourceSort() : SourceSort(Kind::Unknown) {}

  static SourceSort unknown() { return SourceSort(); }
  static SourceSort boolean() { return SourceSort(Kind::Bool); }

  static SourceSort bitVector(unsigned width)
  {
    assert(width > 0);
    return SourceSort(Kind::BitVector, width);
  }

  static SourceSort floatingPoint(unsigned exponent, unsigned significand)
  {
    assert(exponent > 0 && significand > 0);
    return SourceSort(Kind::FloatingPoint, exponent, significand);
  }

  static SourceSort roundingMode()
  {
    return SourceSort(Kind::RoundingMode);
  }

  static SourceSort array(const SourceSort& index, const SourceSort& element)
  {
    assert(index.isScalar() && element.isScalar());
    return SourceSort(index, element);
  }

  Kind kind() const { return kind_; }
  bool isKnown() const { return kind_ != Kind::Unknown; }
  bool isScalar() const
  {
    return kind_ == Kind::BitVector || kind_ == Kind::FloatingPoint ||
           kind_ == Kind::RoundingMode;
  }

  bool containsFloatingPoint() const
  {
    if (kind_ == Kind::FloatingPoint)
      return true;
    return kind_ == Kind::Array &&
           (index().containsFloatingPoint() ||
            element().containsFloatingPoint());
  }

  // RoundingMode belongs to the SMT floating-point theory even when no
  // FloatingPoint value occurs. Printers and other source-level decisions
  // need that broader question; lowering itself usually needs the narrower
  // containsFloatingPoint() predicate above.
  bool usesFloatingPointTheory() const
  {
    if (kind_ == Kind::FloatingPoint || kind_ == Kind::RoundingMode)
      return true;
    return kind_ == Kind::Array &&
           (index().usesFloatingPointTheory() ||
            element().usesFloatingPointTheory());
  }

  unsigned bitVectorWidth() const
  {
    assert(kind_ == Kind::BitVector);
    return first_;
  }

  unsigned exponentWidth() const
  {
    assert(kind_ == Kind::FloatingPoint);
    return first_;
  }

  unsigned significandWidth() const
  {
    assert(kind_ == Kind::FloatingPoint);
    return second_;
  }

  unsigned packedWidth() const
  {
    switch (kind_)
    {
      case Kind::Bool:
        return 0;
      case Kind::BitVector:
        return first_;
      case Kind::FloatingPoint:
        return first_ + second_;
      case Kind::RoundingMode:
        return 5;
      default:
        assert(false && "packedWidth is defined only for scalar sorts");
        return 0;
    }
  }

  const SourceSort& index() const
  {
    assert(kind_ == Kind::Array);
    return *index_;
  }

  const SourceSort& element() const
  {
    assert(kind_ == Kind::Array);
    return *element_;
  }

  friend bool operator==(const SourceSort& left, const SourceSort& right)
  {
    if (left.kind_ != right.kind_ || left.first_ != right.first_ ||
        left.second_ != right.second_)
      return false;
    if (left.kind_ != Kind::Array)
      return true;
    return left.index() == right.index() &&
           left.element() == right.element();
  }

  friend bool operator!=(const SourceSort& left, const SourceSort& right)
  {
    return !(left == right);
  }

  size_t hash() const
  {
    size_t h = static_cast<size_t>(kind_);
    h = h * 1315423911u + first_;
    h = h * 1315423911u + second_;
    if (kind_ == Kind::Array)
    {
      h = h * 1315423911u + index().hash();
      h = h * 1315423911u + element().hash();
    }
    return h;
  }

  // For the manager's intern pool, which is what lets a derived sort be
  // memoised on a node as a pointer.
  struct Hasher
  {
    size_t operator()(const SourceSort& sort) const { return sort.hash(); }
  };
};

// Return the canonical SMT-LIB2 spelling used in diagnostics and model text.
// Unknown is rendered explicitly rather than making diagnostic construction
// itself partial.
std::string sourceSortToSMTLib(const SourceSort& sort);

} // namespace stp

#endif

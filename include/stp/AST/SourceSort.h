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
    Array,
    // A sort introduced by (declare-sort S 0). Appended, never inserted: two
    // lemma-key comparators order by this ordinal and hash() mixes it, so
    // moving an existing enumerator renumbers nodes and reorders keys.
    Uninterpreted
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

  // A sort declared by (declare-sort S 0): an identity of its own, and a
  // bit-vector carrier wide enough to tell some number of its elements apart.
  //
  // The identity is what the sort was missing. Registered as a bare
  // bitVector(width) it was the carrier, so any two declared sorts were one
  // sort and each was the same sort as a genuine bit-vector of that width --
  // and every frontend guard, all of which compare a SourceSort and all of
  // which correctly refuse a float of the same packed width, was defeated by
  // that one fact rather than by any fault of its own.
  //
  // The id occupies first_ and the carrier width second_, so operator== and
  // hash() need no change and cannot be got wrong: they already compare and
  // mix exactly those two fields. Ids come from a process-global counter and
  // name a sort for the life of the process -- see uninterpretedSortName.
  static SourceSort uninterpreted(unsigned id, unsigned width)
  {
    assert(id > 0);
    assert(width > 0);
    return SourceSort(Kind::Uninterpreted, id, width);
  }

  static SourceSort array(const SourceSort& index, const SourceSort& element)
  {
    assert(index.isScalar() && element.isScalar());
    // A declared sort is represented by its finite bit-vector carrier below
    // the source boundary, so it is just as usable as the other scalar sorts
    // as an array index or element. Its identity remains in SourceSort: two
    // declared sorts with the same carrier width are still different sorts.
    return SourceSort(index, element);
  }

  Kind kind() const { return kind_; }
  bool isKnown() const { return kind_ != Kind::Unknown; }
  bool isScalar() const
  {
    return kind_ == Kind::BitVector || kind_ == Kind::FloatingPoint ||
           kind_ == Kind::RoundingMode || kind_ == Kind::Uninterpreted;
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

  unsigned uninterpretedId() const
  {
    assert(kind_ == Kind::Uninterpreted);
    return first_;
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
      case Kind::Uninterpreted:
        return second_;
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

// Register a sort declared by (declare-sort S 0) and return its identity.
//
// Ids come from a process-global counter and are never recycled, which two
// things force. A SourceSort is a value and carries no provenance, so a
// per-manager counter would make manager A's first sort compare equal to
// manager B's -- and the C API creates a manager per validity checker, with
// more than one alive at once. And sort aliases are frame-scoped, so
// (push 1)(declare-sort S 0)(pop 1)(declare-sort S 0) legally declares two
// different sorts spelled the same; keying identity on the name would hand
// back a symbol belonging to a discarded frame.
//
// One string per declared sort per process, kept for the life of the process.
SourceSort registerUninterpretedSort(const std::string& name, unsigned width);

// The name a declared sort was registered under, or an empty string if the id
// is not one this process issued. A free function because its callers are
// free functions and static validators that cannot reach a manager. By value:
// the table is append-only but its storage still moves when it grows, so a
// reference handed out under the lock would not stay valid after it.
std::string uninterpretedSortName(unsigned id);

// Return the canonical SMT-LIB2 spelling used in diagnostics and model text.
// Unknown is rendered explicitly rather than making diagnostic construction
// itself partial.
std::string sourceSortToSMTLib(const SourceSort& sort);

} // namespace stp

#endif

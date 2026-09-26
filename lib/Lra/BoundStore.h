#ifndef STP_LRA_BOUND_STORE_H
#define STP_LRA_BOUND_STORE_H

#include "DeltaRational.h"
#include "VariableStore.h"
#include "Storage/BoundArena.h"
#include "Storage/StorageMetrics.h"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace stp::lra
{

/* Which side of a variable a bound constrains. */
enum class BoundSide : std::uint8_t
{
  Lower,
  Upper
};

/* One bound the core may assert: a side, a variable, a DeltaRational value, and
 * the atom and origin the core uses to turn the engine's explanations
 * back into literals.  Bounds are immutable once allocated; the engine
 * refers to them by BoundRef and keeps its own view of which are
 * active. */
class EngineBound final
{
 public:
  EngineBound(BoundRef reference,
              BoundSide side,
              VariableId variable,
              DeltaRational value,
              OriginId origin,
              AtomId atom);

  BoundRef reference() const noexcept { return reference_; }
  BoundSide side() const noexcept { return side_; }
  VariableId variable() const noexcept { return variable_; }
  DeltaRational const& value() const noexcept { return value_; }
  OriginId origin() const noexcept { return origin_; }
  AtomId atom() const noexcept { return atom_; }

 private:
  BoundRef reference_;
  BoundSide side_;
  VariableId variable_;
  DeltaRational value_;
  OriginId origin_;
  AtomId atom_;
};

/* The bounds of one generation, in an arena that hands out dense
 * ordinals.  An atom's two bounds are allocated as a pair, and
 * allocatePair checks that the arena gave them consecutive ordinals --
 * a self-check on the allocation, not a lookup route: nothing derives
 * one ordinal from the other, and the pair is carried in AtomBounds. */
class BoundStore final
{
 public:
  struct AtomBounds
  {
    VariableId variable;
    BoundRef lower;
    BoundRef upper;
  };

  struct BoundSpec
  {
    BoundSide side;
    DeltaRational value;
    OriginId origin;
    AtomId atom;
  };

  BoundStore(CoreGeneration generation, VariableStore& variable_store);

  EngineBound& operator[](BoundRef reference) { return arena_.at(reference); }
  EngineBound const& operator[](BoundRef reference) const
  {
    return arena_.at(reference);
  }

  BoundRef allocate(VariableId variable, BoundSpec spec);
  /* The two bounds of one atom, one of each side, at consecutive
   * ordinals. */
  AtomBounds allocatePair(VariableId variable, BoundSpec first, BoundSpec second);

  /* Throws unless the variable belongs to this generation. */
  void validateVariable(VariableId variable) const;

  bool contains(BoundRef reference) const noexcept
  {
    return arena_.contains(reference);
  }
  std::size_t size() const noexcept { return arena_.size(); }
  CoreGeneration generation() const noexcept { return arena_.generation(); }
  BoundArena<EngineBound> const& arena() const noexcept { return arena_; }
  VariableStore const& variableStore() const noexcept { return variable_store_; }
  StorageMetrics arenaMetrics() const noexcept { return arena_.metrics(); }

 private:
  VariableStore& variable_store_;
  BoundArena<EngineBound> arena_;
};

}  // namespace stp::lra

#endif

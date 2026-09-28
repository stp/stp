#include "BoundStore.h"

#include "Storage/CheckedConversions.h"
#include "Storage/StorageFailure.h"

#include <utility>

namespace stp::lra
{

EngineBound::EngineBound(BoundRef reference,
                         BoundSide side,
                         VariableId variable,
                         DeltaRational value,
                         OriginId origin,
                         AtomId atom)
    : reference_(reference),
      side_(side),
      variable_(variable),
      value_(std::move(value)),
      origin_(origin),
      atom_(atom)
{}

BoundStore::BoundStore(CoreGeneration generation,
                       VariableStore& variable_store)
    : variable_store_(variable_store), arena_(generation)
{
  if (variable_store.generation() != generation)
  {
    throw StorageFailure(StorageFailureKind::InvalidGeneration,
                         "BoundStore", "store generation mismatch");
  }
}

void BoundStore::validateVariable(VariableId variable) const
{
  if (!variable_store_.contains(variable))
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                         "BoundStore::validateVariable",
                         "unknown variable");
  }
}

BoundRef BoundStore::allocate(VariableId variable, BoundSpec spec)
{
  validateVariable(variable);
  BoundRef const expected(
                          arena_.generation(),
                          checkedSizeToUint32(arena_.size(), "BoundStore::allocate"));
  BoundRef const actual =
      arena_.emplace(expected, spec.side, variable, std::move(spec.value),
                     spec.origin, spec.atom);
  if (actual != expected)
  {
    throw StorageFailure(StorageFailureKind::InvariantViolation,
                         "BoundStore::allocate",
                         "arena returned an unexpected bound reference");
  }
  return actual;
}

BoundStore::AtomBounds BoundStore::allocatePair(VariableId variable,
                                               BoundSpec first,
                                               BoundSpec second)
{
  if (first.side == second.side)
  {
    throw StorageFailure(StorageFailureKind::InvariantViolation,
                         "BoundStore::allocatePair",
                         "pair does not contain complementary kinds");
  }
  std::uint32_t const first_ordinal =
      checkedSizeToUint32(arena_.size(), "BoundStore::allocatePair");
  if (first_ordinal >= BoundRef::maximum_usable_ordinal)
  {
    throw StorageFailure(StorageFailureKind::ResourceLimit,
                         "BoundStore::allocatePair",
                         "complementary bound ordinals exhausted");
  }
  BoundSide const first_side = first.side;
  BoundRef const first_ref = allocate(variable, std::move(first));
  BoundRef const second_ref = allocate(variable, std::move(second));
  if (first_ref.ordinal() != first_ordinal ||
      second_ref.ordinal() != first_ordinal + 1U)
  {
    throw StorageFailure(StorageFailureKind::InvariantViolation,
                         "BoundStore::allocatePair",
                         "the pair did not receive consecutive ordinals");
  }
  BoundRef const upper = first_side == BoundSide::Upper ? first_ref : second_ref;
  BoundRef const lower = first_side == BoundSide::Upper ? second_ref : first_ref;
  return AtomBounds{variable, lower, upper};
}

}  // namespace stp::lra

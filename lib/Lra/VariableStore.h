#ifndef STP_LRA_VARIABLE_STORE_H
#define STP_LRA_VARIABLE_STORE_H

#include "Storage/LraIds.h"

#include <cstddef>

namespace stp::lra
{

/* The variables of one generation of the exact tableau.  Structural
 * variables and the auxiliary variable of every row come from the same
 * counter, so an ordinal is a dense index into the engine's per-variable
 * arrays and membership is a range check against the count. */
class VariableStore final
{
 public:
  explicit VariableStore(CoreGeneration generation);

  VariableId allocate();
  bool contains(VariableId) const noexcept;
  std::size_t size() const noexcept
  {
    return static_cast<std::size_t>(ids_.allocatedCount());
  }
  CoreGeneration generation() const noexcept { return generation_; }

 private:
  CoreGeneration generation_;
  MonotonicIdAllocator<VariableId> ids_;
};

}  // namespace stp::lra

#endif

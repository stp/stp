#include "VariableStore.h"

namespace stp::lra
{

VariableStore::VariableStore(CoreGeneration generation)
    : generation_(generation), ids_(generation)
{}

VariableId VariableStore::allocate()
{
  return ids_.allocate();
}

bool VariableStore::contains(VariableId variable) const noexcept
{
  return variable.generation() == generation_ &&
         variable.ordinal() < ids_.allocatedCount();
}

}  // namespace stp::lra

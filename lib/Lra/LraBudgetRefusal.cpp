#include "LraBudgetRefusal.h"

#include "LraAtomRegistry.h"
#include "LraFrontend.h"
#include "LraSolveContext.h"
#include "NumberBudget.h"

namespace stp::lra
{
namespace
{
template <class Failure>
bool isResourceLimit(const std::exception& thrown) noexcept
{
  const Failure* const typed = dynamic_cast<const Failure*>(&thrown);
  return typed != nullptr &&
         typed->kind() == decltype(typed->kind())::ResourceLimit;
}
}  // namespace

bool gaveUpOnABudget(const std::exception& thrown) noexcept
{
  return isResourceLimit<NumberFailure>(thrown) ||
         isResourceLimit<FrontendFailure>(thrown) ||
         isResourceLimit<RegistryFailure>(thrown) ||
         isResourceLimit<SolveContextFailure>(thrown);
}

}  // namespace stp::lra

#ifndef STP_LRA_EXACT_LRA_ACTIVE_BOUNDS_H
#define STP_LRA_EXACT_LRA_ACTIVE_BOUNDS_H

#include "ExactLraVerificationData.h"
#include "NumberBudget.h"

#include <cstdint>
#include <vector>

namespace stp::lra {

// Rebuilt from the snapshot at each independent audit. Ordinals are used only
// after checking the complete identity against the bound table. The pending
// conflict bound is support too, but must not already occur in the active set.
class ExactLraActiveBounds final
{
 public:
  bool build(ExactLraVerificationDataView const& data)
  {
    active_.clear();
    generation_ = data.current_tag.generation;
    if (data.active_bounds.size() > data.bounds.size())
      return false;
    if (data.active_bounds.empty() && !data.pending_conflict_bound)
      return true;

    void* const budget = detail::BudgetAccess::requireActive(
        "verification active-bound index");
    if (data.bounds.size() > active_.max_size() ||
        data.bounds.size() >
            detail::BudgetAccess::limits(budget).maximum_allocation_bytes)
      detail::BudgetAccess::preflightStop(
          budget, "verification active-bound index", "allocation limit");
    active_.assign(data.bounds.size(), 0);

    auto insert = [&](BoundRef reference) {
      if (reference.generation() != generation_ ||
          reference.ordinal() >= data.bounds.size() ||
          data.bounds[reference.ordinal()].reference != reference ||
          active_[reference.ordinal()] != 0)
        return false;
      active_[reference.ordinal()] = 1;
      return true;
    };
    for (BoundRef reference : data.active_bounds)
      if (!insert(reference))
        return false;
    return !data.pending_conflict_bound || insert(*data.pending_conflict_bound);
  }

  bool contains(BoundRef reference) const noexcept
  {
    return reference.generation() == generation_ &&
           reference.ordinal() < active_.size() &&
           active_[reference.ordinal()] != 0;
  }

 private:
  CoreGeneration generation_{};
  std::vector<std::uint8_t> active_;
};

}  // namespace stp::lra

#endif

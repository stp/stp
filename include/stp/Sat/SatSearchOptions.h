#ifndef STP_SAT_SEARCH_OPTIONS_H
#define STP_SAT_SEARCH_OPTIONS_H

#include <array>

namespace stp
{
// Search heuristics only. Unset fields retain each backend's own policy.
struct SatSearchOptions
{
  int phase = -1;
  int forcephase = -1;
  int rephase = -1;
  int target = -1;

  struct Entry
  {
    const char* name;
    int value;
  };

  std::array<Entry, 4> entries() const
  {
    return {{{"phase", phase}, {"forcephase", forcephase},
             {"rephase", rephase}, {"target", target}}};
  }

  bool hasOverrides() const noexcept
  {
    return phase >= 0 || forcephase >= 0 || rephase >= 0 || target >= 0;
  }
};
} // namespace stp

#endif

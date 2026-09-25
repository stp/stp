#ifndef STP_SAT_CADICAL_OPTIONS_H
#define STP_SAT_CADICAL_OPTIONS_H

#include <optional>

namespace stp
{

// Unspecified entries retain the backend's defaults/environment and STP's
// automatic policies. Explicit entries override those choices on every fresh
// backend, including incremental rebuilds.
struct CadicalOptions
{
  std::optional<int> elim;
  std::optional<int> elimmineff;
  std::optional<int> elimmaxeff;

  bool hasOverrides() const noexcept
  {
    return elim.has_value() || elimmineff.has_value() || elimmaxeff.has_value();
  }
};

} // namespace stp

#endif

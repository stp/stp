/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "Internal.h"

#include <cassert>
#include <iostream>
#include <string_view>

namespace stp
{
namespace api
{
namespace detail
{
namespace
{
using Flags = UserDefinedFlags;

struct Setting
{
  const char* option;
  const char* value;
};

struct Profile
{
  const char* name;
  std::vector<Setting> settings;
};

const Profile& select_profile(Flags::SATSolvers backend, std::string_view logic,
                              bool incremental)
{
  // Full-corpus confirmation at a 24-second complete-session cutoff:
  // Kissat/QF_BV batch: 1.759 -> 1.577s mean PAR2 (46,191 files).
  // CaDiCaL/QF_ABV incremental: 4.695 -> 2.806s (1,272 files).
  // Kissat/QF_ABV incremental: 4.469 -> 3.780s (1,272 files).
  // Incremental directories included single-check files; their multi-check
  // subset independently supported both QF_ABV profiles.
  static const Profile baseline{"backend-defaults", {}};
  static const Profile kissat_bv_batch{
      "kissat-qf-bv-batch",
      {{"sat-phase", "0"}, {"cnf-generation-effort", "new-medium"}}};
  static const Profile cadical_abv_incremental{
      "cadical-qf-abv-incremental",
      {{"search-bias", "sat"},
       {"sat-target", "0"},
       {"cnf-generation-effort", "new-medium"},
       {"cadical-factor", "off"}}};
  static const Profile kissat_abv_incremental{"kissat-qf-abv-incremental",
                                              {{"search-bias", "sat"},
                                               {"kissat-stable", "2"},
                                               {"cadical-factor", "off"}}};

  if (backend == Flags::KISSAT_SOLVER && logic == "QF_BV" && !incremental)
    return kissat_bv_batch;
  if (logic == "QF_ABV" && incremental)
  {
    if (backend == Flags::CADICAL_SOLVER)
      return cadical_abv_incremental;
    if (backend == Flags::KISSAT_SOLVER)
      return kissat_abv_incremental;
  }
  // QF_BV incremental gains were marginal or negative. The CaDiCaL batch
  // QF_ABV finalist requires gia-low, whose ABC recursion overflow must be
  // fixed before that encoding is selected automatically for new workloads.
  return baseline;
}

std::size_t index_of(const char* name)
{
  return option_index(find_option(name));
}

const OptionSpec& spec_at(std::size_t index)
{
  std::size_t count = 0;
  const OptionSpec* specs = option_specs(count);
  assert(index < count);
  return specs[index];
}

bool search_setting(std::string_view name)
{
  return name == "sat-phase" || name == "sat-forcephase" ||
         name == "sat-rephase" || name == "sat-target" ||
         name == "kissat-stable";
}

const char* backend_name(Flags::SATSolvers backend)
{
  switch (backend)
  {
    case Flags::CADICAL_SOLVER:
      return "cadical";
    case Flags::KISSAT_SOLVER:
      return "kissat";
    case Flags::CRYPTOMINISAT5_SOLVER:
      return "cryptominisat";
    case Flags::SIMPLIFYING_MINISAT_SOLVER:
      return "simplifying-minisat";
    default:
      return "minisat";
  }
}
} // namespace

void apply_sat_tuning_defaults(const OptionsImpl& options,
                               const SatTuningDefaults& tuning,
                               DerivedOptions& derived)
{
  if (!tuning.prepared ||
      std::get<std::string>(options.resolved(index_of("sat-tuning"))) != "auto")
    return;
  const bool explicit_bias = options.is_set[index_of("search-bias")];
  for (const auto& [index, value] : tuning.entries)
  {
    // Presence protects even an explicit "auto", "none", -1, or a value
    // equal to the baseline. Derived nondefault values from composite
    // options also outrank a profile default.
    if (!derived.at_default[index])
      continue;
    // An explicitly named search configuration owns its phase/mode policy.
    // Individual explicit phase/mode controls still override it normally.
    if (explicit_bias && search_setting(spec_at(index).name))
      continue;
    derived.resolved[index] = value;
    derived.at_default[index] = false;
  }
}

void SolverImpl::clear_sat_tuning()
{
  sat_tuning = SatTuningDefaults{};
  derived_options.generation = 0;
}

void SolverImpl::prepare_sat_tuning(std::string_view declared,
                                    bool incremental_session,
                                    bool reapply_options)
{
  const Flags& flags = mgr->bm->UserFlags;
  const bool incremental =
      flags.incremental_mode == Flags::IncrementalMode::ON ||
      (flags.incremental_mode == Flags::IncrementalMode::AUTO &&
       (incremental_session ||
        (sat_tuning.prepared && sat_tuning.incremental)));
  const std::string selected_logic =
      declared.empty()
          ? std::get<std::string>(options.resolved(index_of("logic")))
          : std::string(declared);
  // A stream can reveal its first push after some batch checks. Select again
  // until the persistent driver exists, then retain that driver's profile
  // through checks, relief rebuilds and manager activation switches.
  if (!sat_tuning.prepared || (!stp->hasIncrementalSolver() &&
                               (sat_tuning.logic != selected_logic ||
                                sat_tuning.incremental != incremental ||
                                sat_tuning.backend != flags.solver_to_use)))
  {
    SatTuningDefaults selected;
    selected.prepared = true;
    selected.logic = selected_logic;
    selected.incremental = incremental;
    selected.backend = flags.solver_to_use;
    const Profile& profile =
        select_profile(selected.backend, selected.logic, selected.incremental);
    selected.profile = profile.name;
    for (const Setting& setting : profile.settings)
    {
      const OptionSpec* spec = find_option(setting.option);
      selected.entries.emplace_back(option_index(spec),
                                    parse_option_text(*spec, setting.value));
    }
    sat_tuning = std::move(selected);
    derived_options.generation = 0;
  }
  // Native checks already reapply explicit options each time. Parsed checks
  // refresh only tuning controls, and only for new contexts or changed options.
  if (reapply_options || derived_options.generation != options.generation)
    apply_options("SAT tuning", !reapply_options);

  if (flags.stats_flag && sat_tuning.reported_generation != options.generation)
  {
    std::cerr << "SAT tuning: backend=" << backend_name(sat_tuning.backend)
              << " logic="
              << (sat_tuning.logic.empty() ? "unspecified" : sat_tuning.logic)
              << " session="
              << (sat_tuning.incremental ? "incremental" : "batch")
              << " profile="
              << (flags.sat_tuning_auto ? sat_tuning.profile : "off") << '\n';
    if (flags.sat_tuning_auto)
      for (const auto& [index, value] : sat_tuning.entries)
      {
        const OptionSpec& spec = spec_at(index);
        std::cerr << "SAT tuning: " << spec.name << '='
                  << option_text(spec, derived_options.resolved[index])
                  << (options.is_set[index] ? " (explicit)"
                      : derived_options.resolved[index] == value
                          ? " (automatic)"
                          : " (user configuration)")
                  << '\n';
      }
    sat_tuning.reported_generation = options.generation;
  }
}
} // namespace detail
} // namespace api
} // namespace stp

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
                              bool incremental, bool forced_incremental)
{
  // Initial full-corpus confirmation at a 24-second complete-session cutoff:
  // Kissat/QF_BV batch: 1.759 -> 1.577s mean PAR2 (46,191 files).
  // CaDiCaL/QF_ABV batch: 0.717 -> 0.685s (15,148 files).
  // CaDiCaL/QF_ABV incremental: 4.695 -> 2.806s (1,272 files).
  // Kissat/QF_ABV incremental: 4.469 -> 3.780s (1,272 files).
  // Incremental directories included single-check files; their multi-check
  // subset independently supported both QF_ABV profiles.
  // A follow-up on all multi-check QF_BV/QF_ABV inputs selected focused
  // QF_BV search, and found that QF_ABV benefits from pairing the in-house
  // encoding with disabled target phases, rephasing and Kissat probing.
  static const Profile baseline{"backend-defaults", {}};
  static const Profile kissat_bv_batch{"kissat-qf-bv-batch",
                                       {{"sat-phase", "0"},
                                        {"cnf-generation-effort", "auto"},
                                        {"kissat-adaptive-cnf", "true"},
                                        {"kissat-import-order", "2"},
                                        {"kissat-incremental-greedy", "4"},
                                        {"kissat-batch-only", "true"},
                                        {"bv-conditional-equality", "true"}}};
  static const Profile cadical_bv_batch{"cadical-qf-bv-batch",
                                        {{"sat-phase", "0"}}};
  static const Profile kissat_abv_batch{
      "kissat-qf-abv-batch",
      {{"cadical-factor", "off"},
       {"kissat-batch-only", "true"},
       {"kissat-one-shot-stable", "0"},
       {"cnf-auto-threshold", "0"},
       {"array-late-read-limit", "1024"},
       {"array-late-expansion-limit", "100000"},
       {"array-late-congruence-limit", "16000"},
       {"array-equality-gia-cnf", "true"},
       {"array-equality-gia-min-reads", "16"}}};
  static const Profile cadical_abv_batch{
      "cadical-qf-abv-batch",
      {{"search-bias", "unsat"},
       {"cnf-generation-effort", "gia-low"},
       {"cadical-factor", "off"}}};
  static const Profile cadical_abv_incremental{
      "cadical-qf-abv-incremental",
      {{"search-bias", "sat"},
       {"sat-target", "0"},
       {"cnf-generation-effort", "new-medium"},
       {"cadical-factor", "off"}}};
  static const Profile cadical_bv_incremental{
      "cadical-qf-bv-incremental", {{"sat-rephase", "0"}}};
  static const Profile kissat_bv_incremental{
      "kissat-qf-bv-incremental",
      {{"search-bias", "unsat"},
       {"cnf-generation-effort", "new-medium"},
       {"cadical-factor", "off"}}};
  static const Profile kissat_bv_forced_incremental = []
  {
    Profile profile = kissat_bv_incremental;
    profile.name = "kissat-qf-bv-forced-incremental";
    profile.settings.push_back({"kissat-incremental-greedy", "4"});
    return profile;
  }();
  static const Profile kissat_bvfp_forced_incremental{
      "kissat-qf-bvfp-forced-incremental",
      {{"kissat-incremental-greedy", "2"},
       {"kissat-greedy-conflicts", "0"},
       {"kissat-greedy-decisions", "0"},
       {"kissat-greedy-phase-cache", "true"},
       {"cadical-factor", "off"}}};
  static const Profile kissat_abv_incremental{
      "kissat-qf-abv-incremental",
      {{"search-bias", "sat"},
       {"kissat-stable", "2"},
       {"sat-target", "0"},
       {"sat-rephase", "0"},
       {"cnf-generation-effort", "new-medium"},
       {"kissat-probe", "false"},
       {"cadical-factor", "off"}}};
  static const Profile kissat_abv_forced_incremental = [] {
    Profile profile = kissat_abv_incremental;
    profile.name = "kissat-qf-abv-forced-incremental";
    profile.settings.push_back({"kissat-trail-reuse-mode", "2"});
    return profile;
  }();
  static const Profile cadical_abvfp_forced_incremental{
      "cadical-qf-abvfp-forced-incremental",
      {{"search-bias", "sat"},
       {"sat-phase", "0"},
       {"sat-target", "0"},
       {"cadical-factor", "off"}}};
  static const Profile kissat_abvfp_forced_incremental = []
  {
    Profile profile = kissat_abv_forced_incremental;
    profile.name = "kissat-qf-abvfp-forced-incremental";
    profile.settings.push_back({"kissat-incremental-greedy", "2"});
    profile.settings.push_back({"kissat-greedy-growth", "1"});
    return profile;
  }();

  if (backend == Flags::KISSAT_SOLVER && logic == "QF_BV" && !incremental)
    return kissat_bv_batch;
  if (backend == Flags::CADICAL_SOLVER && logic == "QF_BV" && !incremental)
    return cadical_bv_batch;
  if (backend == Flags::KISSAT_SOLVER && logic == "QF_ABV" && !incremental)
    return kissat_abv_batch;
  if (backend == Flags::CADICAL_SOLVER && logic == "QF_ABV" && !incremental)
    return cadical_abv_batch;
  if (logic == "QF_BV" && incremental)
  {
    if (backend == Flags::CADICAL_SOLVER)
      return cadical_bv_incremental;
    if (backend == Flags::KISSAT_SOLVER)
      return forced_incremental ? kissat_bv_forced_incremental
                                : kissat_bv_incremental;
  }
  if (backend == Flags::KISSAT_SOLVER && logic == "QF_BVFP" &&
      forced_incremental)
    return kissat_bvfp_forced_incremental;
  if (logic == "QF_ABV" && incremental)
  {
    if (backend == Flags::CADICAL_SOLVER)
      return cadical_abv_incremental;
    if (backend == Flags::KISSAT_SOLVER)
      return forced_incremental ? kissat_abv_forced_incremental
                                : kissat_abv_incremental;
  }
  if (logic == "QF_ABVFP" && forced_incremental)
  {
    if (backend == Flags::CADICAL_SOLVER)
      return cadical_abvfp_forced_incremental;
    if (backend == Flags::KISSAT_SOLVER)
      return kissat_abvfp_forced_incremental;
  }
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
         name == "kissat-stable" || name == "kissat-one-shot-stable";
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
    // The diagnostic core-only policy disables trail reuse. An explicitly
    // selected mode is already preserved by the presence check above.
    if (std::string_view(spec_at(index).name) == "kissat-trail-reuse-mode" &&
        std::get<bool>(options.resolved(index_of("incremental-core-only"))))
      continue;
    // An explicitly named search configuration owns its phase/mode policy.
    // Individual explicit phase/mode controls still override it normally.
    if (explicit_bias && search_setting(spec_at(index).name))
      continue;
    // A user-selected global mode also governs a complete one-shot copy.
    // A separately explicit one-shot mode still takes precedence normally.
    if (std::string_view(spec_at(index).name) == "kissat-one-shot-stable" &&
        options.is_set[index_of("kissat-stable")])
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
  const bool forced_incremental =
      flags.incremental_mode == Flags::IncrementalMode::ON;
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
                                sat_tuning.forced_incremental !=
                                    forced_incremental ||
                                sat_tuning.backend != flags.solver_to_use)))
  {
    SatTuningDefaults selected;
    selected.prepared = true;
    selected.logic = selected_logic;
    selected.incremental = incremental;
    selected.forced_incremental = forced_incremental;
    selected.backend = flags.solver_to_use;
    const Profile& profile =
        select_profile(selected.backend, selected.logic, selected.incremental,
                       selected.forced_incremental);
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

#include "stp/Sat/Kissat.h"
#include "KissatAllocations.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <limits>
#include <new>
#include <stdexcept>
#include <string>

namespace stp
{
struct Kissat::Allocations
{
  detail::KissatAllocations owner;
};

Kissat::Kissat(bool trail_reuse_allowed, int search_mode)
    : Kissat(trail_reuse_allowed, search_mode, true)
{
}

Kissat::Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed)
    : Kissat(trail_reuse_allowed, search_mode, probing_allowed, -1)
{
}

Kissat::Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed,
               int trail_reuse_mode)
    : Kissat(trail_reuse_allowed, search_mode, probing_allowed,
             trail_reuse_mode, -1)
{
}

Kissat::Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed,
               int trail_reuse_mode, int elimination)
    : allocations(new Allocations), solver(nullptr),
      trail_reuse_allowed(trail_reuse_allowed),
      trail_reuse_mode(trail_reuse_mode), search_mode(search_mode)
{
  if (trail_reuse_mode < -1 || trail_reuse_mode > 2)
    throw std::invalid_argument("Kissat trail reuse mode outside its range");
  if (elimination < -1 || elimination > 1)
    throw std::invalid_argument("Kissat elimination option outside its range");
  const kissat_allocator allocator = {
      &allocations->owner, detail::KissatAllocations::allocate,
      detail::KissatAllocations::resize, detail::KissatAllocations::deallocate};
  solver = kissat_init_with_allocator(&allocator);
  kissat_set_option(solver, "incremental", 1);
  kissat_set_option(solver, "factor", 0);
  kissat_set_option(solver, "quiet", 1);
  kissat_set_option(solver, "probe", probing_allowed ? 1 : 0);
  if (elimination >= 0)
    kissat_set_option(solver, "eliminate", elimination);
  // A selected mode can enable reuse before the driver's size-gated hint.
  // This matches the measured forced-incremental profile. The boolean opt-out
  // and a later one-shot configuration take precedence over this mode.
  if (trail_reuse_allowed && trail_reuse_mode >= 0)
    kissat_set_option(solver, "incrementalreuse", trail_reuse_mode);
  if (search_mode >= 0)
    kissat_set_option(solver, "stable", search_mode);
}

Kissat::~Kissat()
{
  if (!allocations->owner.failed)
    kissat_release(solver);
}

void Kissat::requireHealthy() const
{
  if (allocations->owner.failed)
    throw std::bad_alloc();
}

int Kissat::literal(Lit lit) const
{
  const int var = external.at(SATSolver::var(lit));
  return SATSolver::sign(lit) ? -var : var;
}

bool Kissat::okay() const
{
  requireHealthy();
  return !kissat_inconsistent(solver);
}

uint32_t Kissat::newVar()
{
  requireHealthy();
  // Kissat's factoring introduces external variables of its own. Allocate
  // after those too, so a later STP variable never aliases a factor variable.
  last_external = std::max(last_external, kissat_maximum_variable(solver));
  if (last_external >= (1 << 30) - 1)
    throw std::overflow_error("Kissat external variable limit reached");
  external.push_back(++last_external);
  frozen.push_back(false);
  return static_cast<uint32_t>(external.size() - 1);
}

bool Kissat::addClauseInternal(const vec_literals& clause)
{
  requireHealthy();
  if (one_shot && solve_calls)
    throw std::logic_error("clauses added after a one-shot Kissat search");
  for (int i = 0; i < clause.size(); ++i)
    kissat_add(solver, literal(clause[i]));
  kissat_add(solver, 0);
  return okay();
}

uint8_t Kissat::modelValue(uint32_t var) const
{
  requireHealthy();
  const int value = kissat_value(solver, external.at(var));
  return value > 0   ? true_literal()
         : value < 0 ? false_literal()
                     : undef_literal();
}

void Kissat::setFrozen(uint32_t var)
{
  requireHealthy();
  if (!frozen.at(var))
  {
    // The batch loader can request model-variable protection even when its
    // complete encoding needs no refinement. A one-shot solver reconstructs
    // its original-variable model itself and accepts no later clauses, so it
    // does not need Kissat's incremental-only protection API.
    if (!one_shot)
      kissat_protect(solver, external.at(var));
    frozen[var] = true;
  }
}

void Kissat::suggestPhase(uint32_t var, bool value)
{
  requireHealthy();
  const int lit = external.at(var);
  kissat_set_phase(solver, value ? lit : -lit);
}

int Kissat::terminate(void* state)
{
  return static_cast<Kissat*>(state)->timeLimitExpired();
}

bool Kissat::run(bool& timeout_expired)
{
  requireHealthy();
  if (one_shot && solve_calls)
    throw std::logic_error("a one-shot Kissat backend was searched twice");
  // Allocated STP variables need not occur in any current clause. Reserve
  // their IDs before BVA can use that apparently empty part of the namespace.
  if (kissat_get_option(solver, "factor") &&
      kissat_maximum_variable(solver) < last_external)
    kissat_reserve(solver, last_external);
  if (max_conflicts >= 0)
    kissat_set_conflict_limit(
        solver, static_cast<unsigned>(std::min<int64_t>(
                    max_conflicts, std::numeric_limits<unsigned>::max())));
  kissat_set_terminate(solver, this,
                       hasTimeLimit() || hasStopPoll() ? terminate : nullptr);
  ++solve_calls;
  const int result = kissat_solve(solver);
  if (result == 0)
    timeout_expired = true;
  return result == 10;
}

bool Kissat::solveInternal(bool& timeout_expired)
{
  return run(timeout_expired);
}

bool Kissat::solveWithAssumptionsInternal(const vec_literals& assumptions,
                                          bool& timeout_expired)
{
  requireHealthy();
  if (one_shot)
    throw std::logic_error("assumptions passed to a one-shot Kissat backend");
  for (int i = 0; i < assumptions.size(); ++i)
    kissat_assume(solver, literal(assumptions[i]));
  return run(timeout_expired);
}

void Kissat::unsatAssumptions(const vec_literals& assumptions,
                              std::vector<int>& out)
{
  requireHealthy();
  out.clear();
  for (int i = 0; i < assumptions.size(); ++i)
    if (kissat_failed(solver, literal(assumptions[i])))
      out.push_back(static_cast<int>(assumptions[i].x));
}

void Kissat::setSeed(uint64_t seed)
{
  requireHealthy();
  kissat_set_option(solver, "seed",
                    static_cast<int>(seed % std::numeric_limits<int>::max()));
}

void Kissat::printStats() const
{
  std::cerr << "Kissat search: phase=" << kissat_get_option(solver, "phase")
            << " forcephase=" << kissat_get_option(solver, "forcephase")
            << " rephase=" << kissat_get_option(solver, "rephase")
            << " target=" << kissat_get_option(solver, "target")
            << " stable=" << kissat_get_option(solver, "stable")
            << " probe=" << kissat_get_option(solver, "probe")
            << " eliminate=" << kissat_get_option(solver, "eliminate")
            << " trail-reuse=" << kissat_get_option(solver, "incrementalreuse")
            << '\n';
  std::cerr << "Kissat: variables=" << nVars()
            << " submitted-clauses=" << submittedClauses()
            << " solves=" << solve_calls << '\n';
}

void Kissat::setVerbosity(int)
{
  requireHealthy();
  // Kissat's reporter writes to C stdout. SMT results must be the only
  // output there; STP's diagnostics use printStats and the diagnostic sink.
  kissat_set_option(solver, "quiet", 1);
  kissat_set_option(solver, "verbose", 0);
}

bool Kissat::setSearchBiasInternal(SearchBias bias)
{
  requireHealthy();
  const char* config = bias == SearchBias::SAT     ? "sat"
                       : bias == SearchBias::UNSAT ? "unsat"
                                                   : "default";
  const bool supported = kissat_set_configuration(solver, config);
  kissat_set_option(solver, "incremental", one_shot ? 0 : 1);
  if (search_mode >= 0)
    kissat_set_option(solver, "stable", search_mode);
  return supported;
}

bool Kissat::enableBVAInternal()
{
  requireHealthy();
  kissat_set_option(solver, "factor", 1);
  return true;
}

bool Kissat::configureOneShot()
{
  requireHealthy();
  if (!configurationOpen() || solve_calls)
    throw std::logic_error("one-shot Kissat requires a fresh backend");
  kissat_set_option(solver, "incremental", 0);
  kissat_set_option(solver, "incrementalreuse", 0);
  one_shot = true;
  return true;
}

bool Kissat::setSearchOptionsInternal(const SatSearchOptions& options)
{
  requireHealthy();
  for (const auto& option : options.entries())
    if (option.value >= 0)
    {
      const int maximum = std::string(option.name) == "target" ? 2 : 1;
      if (option.value > maximum)
        throw std::invalid_argument("Kissat search option outside its range");
      kissat_set_option(solver, option.name, option.value);
      if (kissat_get_option(solver, option.name) != option.value)
        throw std::invalid_argument("Kissat rejected a search option");
    }
  return true;
}

bool Kissat::enableTrailReuseInternal(TrailReuse scope)
{
  requireHealthy();
  if (!trail_reuse_allowed || one_shot || trail_reuse_mode == 0)
    return false;
  const int requested = scope == TrailReuse::ALL ? 2 : 1;
  const int mode = trail_reuse_mode >= 0 ? trail_reuse_mode : requested;
  kissat_set_option(solver, "incrementalreuse", mode);
  return mode >= requested &&
         kissat_get_option(solver, "incrementalreuse") == mode;
}

bool Kissat::disableLuckyPhasesInternal()
{
  requireHealthy();
  kissat_set_option(solver, "luckyearly", 0);
  kissat_set_option(solver, "luckylate", 0);
  return true;
}
} // namespace stp

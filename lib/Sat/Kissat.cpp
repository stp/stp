#include "stp/Sat/Kissat.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <new>
#include <stdexcept>
#include <unordered_set>

namespace stp
{
// A failed C allocation must reach STP's RESOURCE handler. Own every block,
// including temporary inprocessing allocations, so an interrupted allocation
// can discard the partial C solver without walking its unfinished structures.
struct Kissat::Allocations
{
  std::unordered_set<void*> blocks;
  bool failed = false;

  ~Allocations()
  {
    for (void* block : blocks)
      std::free(block);
  }

  static void* allocate(void* state, size_t bytes)
  {
    auto& self = *static_cast<Allocations*>(state);
    void* block = std::malloc(bytes);
    if (!block)
    {
      self.failed = true;
      throw std::bad_alloc();
    }
    try
    {
      self.blocks.insert(block);
    }
    catch (...)
    {
      std::free(block);
      self.failed = true;
      throw;
    }
    return block;
  }

  static void* resize(void* state, void* ptr, size_t bytes)
  {
    if (!ptr)
      return allocate(state, bytes);
    auto& self = *static_cast<Allocations*>(state);
    auto node = self.blocks.extract(ptr);
    assert(!node.empty());
    void* block = std::realloc(ptr, bytes);
    if (!block)
    {
      // Reinserting an extracted node at the same size needs no allocation.
      self.blocks.insert(std::move(node));
      self.failed = true;
      throw std::bad_alloc();
    }
    node.value() = block;
    self.blocks.insert(std::move(node));
    return block;
  }

  static void deallocate(void* state, void* ptr)
  {
    auto& self = *static_cast<Allocations*>(state);
    self.blocks.erase(ptr);
    std::free(ptr);
  }
};

Kissat::Kissat(bool trail_reuse_allowed, int search_mode)
    : allocations(new Allocations), solver(nullptr),
      trail_reuse_allowed(trail_reuse_allowed), search_mode(search_mode)
{
  const kissat_allocator allocator = {allocations.get(), Allocations::allocate,
                                      Allocations::resize,
                                      Allocations::deallocate};
  solver = kissat_init_with_allocator(&allocator);
  kissat_set_option(solver, "incremental", 1);
  kissat_set_option(solver, "factor", 0);
  kissat_set_option(solver, "quiet", 1);
  if (search_mode >= 0)
    kissat_set_option(solver, "stable", search_mode);
}

Kissat::~Kissat()
{
  if (!allocations->failed)
    kissat_release(solver);
}

void Kissat::requireHealthy() const
{
  if (allocations->failed)
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
  kissat_set_option(solver, "incremental", 1);
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

bool Kissat::enableTrailReuseInternal(TrailReuse scope)
{
  requireHealthy();
  if (!trail_reuse_allowed)
    return false;
  const int mode = scope == TrailReuse::ALL ? 2 : 1;
  kissat_set_option(solver, "incrementalreuse", mode);
  return kissat_get_option(solver, "incrementalreuse") == mode;
}

bool Kissat::disableLuckyPhasesInternal()
{
  requireHealthy();
  kissat_set_option(solver, "luckyearly", 0);
  kissat_set_option(solver, "luckylate", 0);
  return true;
}
} // namespace stp

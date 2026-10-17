#include "stp/Sat/Kissat.h"
#include "KissatAllocations.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <climits>
#include <cstdlib>
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

struct Kissat::LuckyProbe
{
  static constexpr size_t maximumLiterals = 4000000;
  static constexpr int maximumVariable = 1000000;
  static constexpr uint64_t minimumAddedClauses = 100000;
  static constexpr uint64_t growthFactor = 4;

  // Original external literals, including a zero after each clause. Only the
  // incremental driver enables this journal; batch encodings do not keep it.
  std::vector<int> clauses;
  std::vector<lbool> model;
  LuckyProbeStatistics statistics;
  uint64_t clauses_at_last_solve = 0;
  bool recording = true;
  bool model_valid = false;

  void stopRecording()
  {
    recording = false;
    std::vector<int>().swap(clauses);
  }

  struct Backend
  {
    detail::KissatAllocations owner;
    kissat* solver = nullptr;
    const Kissat& parent;
    bool& interrupted;
    const std::chrono::steady_clock::time_point deadline;

    Backend(const Kissat& parent, bool& interrupted)
        : parent(parent), interrupted(interrupted),
          deadline(std::chrono::steady_clock::now() +
                   std::chrono::milliseconds(250))
    {
      const kissat_allocator allocator = {
          &owner, detail::KissatAllocations::allocate,
          detail::KissatAllocations::resize,
          detail::KissatAllocations::deallocate};
      solver = kissat_init_with_allocator(&allocator);
      kissat_set_option(solver, "quiet", 1);
      kissat_set_option(solver, "factor", 0);
      kissat_set_option(solver, "preprocess", 0);
      kissat_set_option(solver, "probe", 0);
      kissat_set_option(solver, "eliminate", 0);
      kissat_set_option(solver, "lucky", 1);
      kissat_set_option(solver, "luckyearly", 1);
      kissat_set_option(solver, "luckylate", 0);
      // The candidate pass may finish, but an unsuccessful pass must not
      // start an independent CDCL search before the persistent fallback.
      kissat_set_conflict_limit(solver, 0);
      kissat_set_decision_limit(solver, 0);
      kissat_set_terminate(solver, this, terminate);
    }

    bool stopped() const
    {
      if (parent.timeLimitExpired())
        interrupted = true;
      return interrupted || std::chrono::steady_clock::now() >= deadline;
    }

    static int terminate(void* state)
    {
      return static_cast<Backend*>(state)->stopped();
    }

    ~Backend()
    {
      if (solver && !owner.failed)
        kissat_release(solver);
    }
  };
};

#if defined(STP_KISSAT_HAS_CLAUSE_EXCHANGE)
// Learned clauses out and shared clauses in through the exchange extension
// of STP's Kissat fork. Kissat's external numbering is what both directions
// speak, which every copy forked at one point before the search shares:
// STP variable v is external v + 1 until the search starts, and factoring
// numbers its variables above everything allocated by then. Only clauses
// over the variables that existed when the exchange connected leave; Kissat
// keeps clauses over factoring's variables back itself.
struct Kissat::Exchange
{
  Exchange(SATSolver::ClauseExchange& target,
           const SATSolver::ExchangeSettings& settings, int variables)
      : target(target), settings(settings), variables(variables)
  {
  }

  static void learn(void* state, unsigned size, const int* clause)
  {
    auto& self = *static_cast<Exchange*>(state);
    for (unsigned i = 0; i < size; ++i)
      if (std::abs(clause[i]) > self.variables)
      {
        ++self.filtered;
        return;
      }
    self.target.learned(clause, size);
    ++self.exported;
  }
  static unsigned budget(void* state)
  {
    // The exchange learns the poll's real cap: with no budget set that is
    // this backend's own, the same as CaDiCaL's.
    auto& self = *static_cast<Exchange*>(state);
    const int cap =
        self.settings.importBudget > 0 ? self.settings.importBudget : 1 << 14;
    self.target.beginImport(size_t(cap));
    return unsigned(cap);
  }
  static const int* next(void* state, unsigned* size)
  {
    // A literal beyond the shared variables names something this copy
    // numbered on its own: such a clause is never handed over. INT_MIN has
    // no magnitude to compare, and a skipped clause is cleared before the
    // next, so an exchange that appends rather than assigns adds nothing.
    auto& self = *static_cast<Exchange*>(state);
    std::vector<int>& clause = self.buffer;
    clause.clear();
    while (self.target.next(clause))
    {
      bool shared = !clause.empty();
      for (int lit : clause)
        shared = shared && lit != 0 && lit != INT_MIN &&
                 std::abs(lit) <= self.variables;
      if (shared)
      {
        *size = static_cast<unsigned>(clause.size());
        return clause.data();
      }
      ++self.skipped;
      clause.clear();
    }
    return nullptr;
  }

  SATSolver::ClauseExchange& target;
  const SATSolver::ExchangeSettings settings;
  const int variables;
  std::vector<int> buffer;
  // Clauses kept back on export, and handed over but not shared on import.
  uint64_t exported = 0, filtered = 0, skipped = 0;
};
#else
struct Kissat::Exchange
{
};
#endif

bool Kissat::enableLuckyProbe()
{
  requireHealthy();
#ifndef KISSAT_HAS_INTERRUPTIBLE_LUCKY
  return false;
#else
  if (one_shot || !configurationOpen())
    return false;
  if (!lucky_probe)
    try
    {
      lucky_probe = std::make_unique<LuckyProbe>();
    }
    catch (const std::bad_alloc&)
    {
      return false;
    }
  return true;
#endif
}

Kissat::LuckyProbeStatistics Kissat::luckyProbeStatistics() const
{
  if (!lucky_probe)
    return {};
  auto result = lucky_probe->statistics;
  result.retained_literals = lucky_probe->clauses.size();
  return result;
}

bool Kissat::tryLuckyProbe(const vec_literals& assumptions,
                           bool& timeout_expired)
{
  if (!lucky_probe)
    return false;
  auto& probe = *lucky_probe;
  probe.model_valid = false;
  const uint64_t clauses = submittedClauses();
  const uint64_t previous = probe.clauses_at_last_solve;
  probe.clauses_at_last_solve = clauses;
  const uint64_t added = clauses - previous;
  if (!probe.recording || added < LuckyProbe::minimumAddedClauses ||
      added / LuckyProbe::growthFactor < previous || max_conflicts >= 0)
    return false;

  ++probe.statistics.attempts;
  try
  {
    LuckyProbe::Backend candidate(*this, timeout_expired);
    size_t polled = 0;
    for (int lit : probe.clauses)
    {
      if (!(polled++ & 1023) && candidate.stopped())
      {
        ++probe.statistics.inconclusive;
        return false;
      }
      kissat_add(candidate.solver, lit);
    }
    for (int i = 0; i < assumptions.size(); ++i)
    {
      if (!(i & 1023) && candidate.stopped())
      {
        ++probe.statistics.inconclusive;
        return false;
      }
      kissat_add(candidate.solver, literal(assumptions[i]));
      kissat_add(candidate.solver, 0);
    }
    if (kissat_solve(candidate.solver) != 10)
    {
      ++probe.statistics.inconclusive;
      return false;
    }

    std::vector<int8_t> values(static_cast<size_t>(last_external) + 1, 0);
    for (int var = 1; var <= last_external; ++var)
    {
      if (!(var & 1023) && candidate.stopped())
      {
        ++probe.statistics.inconclusive;
        return false;
      }
      const int value = kissat_value(candidate.solver, var);
      values[var] = value > 0 ? 1 : value < 0 ? -1 : 0;
    }
    const auto satisfied = [&values](int lit)
    {
      // An unassigned variable is completed with false. This also checks
      // clauses simplified away while the disposable formula was loaded.
      const bool value = values[static_cast<size_t>(std::abs(lit))] > 0;
      return value == (lit > 0);
    };
    bool clause_satisfied = false;
    for (int lit : probe.clauses)
    {
      if (!(polled++ & 1023) && candidate.stopped())
      {
        ++probe.statistics.inconclusive;
        return false;
      }
      if (lit)
        clause_satisfied |= satisfied(lit);
      else
      {
        if (!clause_satisfied)
        {
          ++probe.statistics.rejected_models;
          return false;
        }
        clause_satisfied = false;
      }
    }
    for (int i = 0; i < assumptions.size(); ++i)
      if (!satisfied(literal(assumptions[i])))
      {
        ++probe.statistics.rejected_models;
        return false;
      }

    std::vector<lbool> model;
    model.reserve(external.size());
    for (int var : external)
      model.push_back(values[var] > 0   ? true_literal()
                      : values[var] < 0 ? false_literal()
                                        : undef_literal());
    probe.model = std::move(model);
    if (candidate.stopped())
    {
      ++probe.statistics.inconclusive;
      return false;
    }
    probe.model_valid = true;
    ++probe.statistics.successes;
    return true;
  }
  catch (const std::bad_alloc&)
  {
    // Optional copying must not poison the persistent solver's allocator.
    // Abandon future copies and give their memory back to ordinary solving.
    probe.stopRecording();
    ++probe.statistics.inconclusive;
    return false;
  }
}

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
  if (allocations->owner.failed)
    return;
#if defined(STP_KISSAT_HAS_CLAUSE_EXCHANGE)
  if (exchange)
    exchange->target.closing(exchangeCounters());
#endif
  kissat_release(solver);
}

void Kissat::setGreedyOptions(const GreedyOptions& options)
{
  requireHealthy();
  if (!configurationOpen() || solve_calls)
    throw std::logic_error("Kissat greedy options require a fresh backend");
  if (options.mode < 0 || options.mode > 4 || options.conflicts < 0 ||
      options.decisions < 0 || options.growth < 1 || options.growth > 16)
    throw std::invalid_argument("Kissat greedy option outside its range");
  const struct
  {
    const char* name;
    int value;
  } settings[] = {{"incrementallucky", options.mode},
                  {"incrementalluckyinit", options.conflicts},
                  {"incrementalluckydecisions", options.decisions},
                  {"incrementalluckygrowth", options.growth},
                  {"incrementalluckyphasecache", options.phase_cache ? 1 : 0}};
  for (const auto& setting : settings)
  {
    kissat_set_option(solver, setting.name, setting.value);
    if (kissat_get_option(solver, setting.name) != setting.value)
      throw std::invalid_argument("Kissat rejected a greedy option");
  }
}

void Kissat::setImportOrder(int order)
{
  requireHealthy();
  if (!configurationOpen() || solve_calls)
    throw std::logic_error("Kissat import order requires a fresh backend");
  if (order < 0 || order > 2)
    throw std::invalid_argument("Kissat import order outside its range");
  import_order = order;
}

void Kissat::setOneShotSearchMode(int mode)
{
  requireHealthy();
  if (!configurationOpen() || solve_calls || one_shot)
    throw std::logic_error(
        "select the Kissat search mode before one-shot configuration");
  if (mode < -1 || mode > 2)
    throw std::invalid_argument(
        "Kissat one-shot search mode outside its range");
  one_shot_search_mode = mode;
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
  if (lucky_probe && last_external > LuckyProbe::maximumVariable)
    lucky_probe->stopRecording();
  return static_cast<uint32_t>(external.size() - 1);
}

bool Kissat::addClauseInternal(const vec_literals& clause)
{
  requireHealthy();
  if (one_shot && solve_calls)
    throw std::logic_error("clauses added after a one-shot Kissat search");
  // Reserve the currently allocated IDs before loading the first clause.
  // Variables allocated later keep the ordinary import path.
  if (import_order && submittedClauses() == 1 && last_external)
  {
    const int incremental = kissat_get_option(solver, "incremental");
    const int tumble = kissat_get_option(solver, "tumble");
    kissat_set_option(solver, "incremental", import_order == 2 ? 1 : 0);
    kissat_set_option(solver, "tumble", import_order == 1 ? 0 : tumble);
    kissat_reserve(solver, last_external);
    kissat_set_option(solver, "tumble", tumble);
    kissat_set_option(solver, "incremental", incremental);
  }
  if (lucky_probe)
  {
    auto& probe = *lucky_probe;
    probe.model_valid = false;
    if (probe.recording)
    {
      if (static_cast<size_t>(clause.size()) + 1 >
          LuckyProbe::maximumLiterals - probe.clauses.size())
        probe.stopRecording();
      else
        try
        {
          for (int i = 0; i < clause.size(); ++i)
            probe.clauses.push_back(literal(clause[i]));
          probe.clauses.push_back(0);
        }
        catch (const std::bad_alloc&)
        {
          probe.stopRecording();
        }
    }
  }
  for (int i = 0; i < clause.size(); ++i)
    kissat_add(solver, literal(clause[i]));
  kissat_add(solver, 0);
  return okay();
}

uint8_t Kissat::modelValue(uint32_t var) const
{
  requireHealthy();
  const int native_var = external.at(var);
  if (lucky_probe && lucky_probe->model_valid)
  {
    const auto& model = lucky_probe->model;
    if (var >= model.size())
      return undef_literal();
    // A model variable with no constraints can be completed with false.
    return frozen.at(var) && model[var] == undef_literal() ? false_literal()
                                                           : model[var];
  }
  const int value = kissat_value(solver, native_var);
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
  requireHealthy();
  const vec_literals assumptions;
  if (tryLuckyProbe(assumptions, timeout_expired))
  {
    ++solve_calls;
    return true;
  }
  if (timeout_expired || timeLimitExpired())
  {
    timeout_expired = true;
    return false;
  }
  return run(timeout_expired);
}

bool Kissat::solveWithAssumptionsInternal(const vec_literals& assumptions,
                                          bool& timeout_expired)
{
  requireHealthy();
  if (one_shot)
    throw std::logic_error("assumptions passed to a one-shot Kissat backend");
  if (tryLuckyProbe(assumptions, timeout_expired))
  {
    ++solve_calls;
    return true;
  }
  if (timeout_expired || timeLimitExpired())
  {
    timeout_expired = true;
    return false;
  }
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
            << " greedy=" << kissat_get_option(solver, "incrementallucky")
            << " greedy-conflicts="
            << kissat_get_option(solver, "incrementalluckyinit")
            << " greedy-decisions="
            << kissat_get_option(solver, "incrementalluckydecisions")
            << " greedy-growth="
            << kissat_get_option(solver, "incrementalluckygrowth")
            << " greedy-phase-cache="
            << kissat_get_option(solver, "incrementalluckyphasecache") << '\n';
  std::cerr << "Kissat: variables=" << nVars()
            << " submitted-clauses=" << submittedClauses()
            << " solves=" << solve_calls << '\n';
  if (lucky_probe)
  {
    const auto stats = luckyProbeStatistics();
    std::cerr << "Kissat lucky probe: attempts=" << stats.attempts
              << " successes=" << stats.successes
              << " inconclusive=" << stats.inconclusive
              << " rejected-models=" << stats.rejected_models
              << " retained-literals=" << stats.retained_literals << '\n';
  }
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
  const int mode = one_shot && one_shot_search_mode >= 0 ? one_shot_search_mode
                                                         : search_mode;
  if (mode >= 0)
    kissat_set_option(solver, "stable", mode);
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
  if (one_shot_search_mode >= 0)
    kissat_set_option(solver, "stable", one_shot_search_mode);
  lucky_probe.reset();
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

bool Kissat::connectClauseExchange(ClauseExchange* target,
                                   const ExchangeSettings& settings)
{
#if defined(STP_KISSAT_HAS_CLAUSE_EXCHANGE)
  requireHealthy();
  if (exchange)
  {
    // Connected only before the backend has searched (at its before-search
    // point), so the exchange replaced here has counted nothing.
    kissat_set_learn(solver, nullptr, 0, nullptr);
    kissat_set_import(solver, nullptr, 0, nullptr, nullptr);
    exchange.reset();
  }
  if (!target)
    return true;
  exchange.reset(new Exchange(*target, settings, last_external));
  kissat_set_learn(solver, exchange.get(), settings.maxSize, Exchange::learn);
  if (settings.import)
    kissat_set_import(solver, exchange.get(),
                      unsigned(std::max(settings.importInterval, 1)),
                      Exchange::budget, Exchange::next);
  return true;
#else
  (void)target;
  (void)settings;
  return false;
#endif
}

SATSolver::ExchangeCounters Kissat::exchangeCounters() const
{
  ExchangeCounters out;
#if defined(STP_KISSAT_HAS_CLAUSE_EXCHANGE)
  if (!exchange || allocations->owner.failed)
    return out;
  kissat_import_statistics in;
  kissat_get_import_statistics(solver, &in);
  out.connected = true;
  out.variables = uint64_t(exchange->variables);
  out.exported = exchange->exported;
  out.filtered = exchange->filtered;
  out.polls = in.polls;
  out.imported = in.clauses;
  out.units = in.units;
  out.dropped = in.dropped + exchange->skipped;
  out.satisfied = in.satisfied;
  out.backtracks = in.backtracks;
#endif
  return out;
}

bool Kissat::diversify(const Diversification& d)
{
#if defined(STP_KISSAT_HAS_CLAUSE_EXCHANGE)
  requireHealthy();
  // Before the first solve only (a SearchPoint is, by construction): the
  // first search reads the search mode. Kissat takes seeds from 0.
  if (solve_calls || d.seed < 0)
    return false;
  if (d.mode == 1 || d.mode == 2)
    kissat_set_option(solver, "stable", d.mode == 1 ? 0 : 2);
  kissat_diversify(solver, d.seed, d.phase, d.shuffle ? 1 : 0);
  return true;
#else
  (void)d;
  return false;
#endif
}

bool Kissat::disableLuckyPhasesInternal()
{
  requireHealthy();
  kissat_set_option(solver, "luckyearly", 0);
  kissat_set_option(solver, "luckylate", 0);
  return true;
}
} // namespace stp

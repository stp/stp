/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// Solver.cpp -- the solver over an STP: assertions, checks, results,
// interrupts, parsing and printing.

#include "Internal.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Globals/Globals.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "../Lra/LraFrontend.h"
#include "stp/NodeFactory/TypeChecker.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/Util/PreparationControl.h"
#include "stp/Util/RunTimes.h"
#include "stp/config.h"
#include "stp/cpp_interface.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <fstream>
#include <iostream>
#include <istream>
#include <mutex>
#include <optional>
#include <ostream>
#include <set>
#include <sstream>
#include <string_view>

extern int smt2lineno;

namespace stp
{
namespace api
{
namespace detail
{

std::mutex& parser_mutex()
{
  static std::mutex m;
  return m;
}

// The frontends answer on stdout ((error ...), unsupported, success); a parse
// driven by the API keeps that text for its diagnostics instead. The capture
// is a route of the calling thread's, so no other thread's output is taken
// with it; what goes to std::cerr, and a fatal error, go where they went
// without it.
class CoutCapture
{
public:
  explicit CoutCapture(bool on)
  {
    if (!on)
      return;
    const OutputSinks* outer = current_output_route();
    sinks_.out = &append_;
    sinks_.err = outer != nullptr ? outer->err : &to_cerr_;
    sinks_.fatal = outer != nullptr ? outer->fatal : nullptr;
    route_.emplace(&sinks_);
  }
  std::string text() const
  {
    std::string t = buf_;
    while (!t.empty() && (t.back() == '\n' || t.back() == ' '))
      t.pop_back();
    return t;
  }

private:
  std::string buf_;
  const std::function<void(std::string_view)> append_ = [this](std::string_view s) {
    buf_.append(s);
  };
  const std::function<void(std::string_view)> to_cerr_ = [](std::string_view s) { std::cerr << s; };
  OutputSinks sinks_;
  std::optional<OutputRoute> route_;
};

// What the engine checks of the entries only once they are applied: the
// CaDiCaL knobs against the backend and the build, and an explicit request
// for arithmetic decision polarity against what it needs. Refused at
// construction and at every check, in the engine's words.
void validate_engine_options(const UserDefinedFlags& flags)
{
  try
  {
    validateCadicalOptions(flags);
  }
  catch (const std::invalid_argument& e)
  {
    const CadicalOptions& c = flags.cadical_options;
    const char* name = c.elim.has_value()         ? "cadical-elim"
                       : c.elimmineff.has_value() ? "cadical-elimmineff"
                                                  : "cadical-elimmaxeff";
    const ErrorCode code = flags.solver_to_use != UserDefinedFlags::CADICAL_SOLVER
                               ? ErrorCode::OPTION_CONFLICT
                           : STP_BUILD_WITH_CADICAL == 0 ? ErrorCode::OPTION_UNAVAILABLE
                                                         : ErrorCode::OPTION_VALUE;
    fail_option(code, name, e.what());
  }
  // The default preference yields to what the backend can do; an explicit
  // request is refused when it cannot be honoured.
  if (flags.lra_decision_polarity && flags.lra_decision_polarity_explicit)
  {
    if (!flags.lra_theory_propagation)
      fail_option(ErrorCode::OPTION_CONFLICT, "lra-decision-polarity",
                  "--lra-decision-polarity requires --lra-theory-propagation=1");
    bool supported = false;
#if defined(USE_CADICAL) && defined(STP_CADICAL_HAS_DECISION_POLARITY)
    supported = flags.solver_to_use == UserDefinedFlags::CADICAL_SOLVER;
#endif
    if (!supported)
      fail_option(ErrorCode::OPTION_UNAVAILABLE, "lra-decision-polarity",
                  "--lra-decision-polarity requires CaDiCaL built with "
                  "cmake/deps-utils/cadical-decision-polarity.patch");
  }
}

// ------------------------------------------------------------ SolverImpl

SolverImpl::SolverImpl(ManagerImpl* m, const Options& o) : mgr(m)
{
  mgr->retain();
  options = *o.impl();
  bool registered = false;
  // the engine is built inside an engine scope: a failure there is INTERNAL
  detail::engine_call(mgr, "Solver", [&] {
  try
  {
    options.resolve("Solver");
    // The engine's stack and flags become this solver's: the active solver,
    // if any, shelves its levels first (it takes them back when next used).
    if (mgr->active != nullptr)
      mgr->active->deactivate();
    stp = new STP(mgr->bm);
    mgr->solvers.push_back(this);
    registered = true;
    mgr->bm->UserFlags.coverage = coverage; // a new solver has counted nothing
    mgr->active = this;
    mgr->bm->Push(); // the base level
    reapply_engine_defaults();
    validate_engine_options(mgr->bm->UserFlags);
  }
  catch (...)
  {
    // A refused option leaves the manager as it was: no live solver of ours,
    // no engine, no base level. (The destructor does not run for a
    // constructor that throws.) The solver shelved above stays shelved and is
    // installed again by its next use.
    if (stp != nullptr)
    {
      if (mgr->active == this)
      {
        while (mgr->bm->getAssertLevel() > 0)
          mgr->bm->Pop();
        mgr->active = nullptr;
      }
      stp->deleteObjects();
      delete stp;
      stp = nullptr;
    }
    if (registered)
      mgr->solvers.erase(std::find(mgr->solvers.begin(), mgr->solvers.end(), this));
    mgr->release();
    throw;
  }
  });
  constructed = true;
}

SolverImpl::~SolverImpl()
{
  model.reset();
  candidate.reset();
  last_assumptions.clear();
  last_failed_assumptions.clear();
  if (stp != nullptr)
  {
    // Engine work in a destructor, which cannot report a failure: an engine
    // failure here poisons the manager (every later call on it is STATE), the
    // engine object is left alone, and the teardown goes on. What the
    // teardown prints (a Real session's statistics) is this solver's.
    detail::EngineScope scope;
    detail::OutputRoute route(&route_sinks);
    try
    {
      if (mgr->active == this)
      {
        // The engine's stack is this solver's: leave it empty for the next
        // solver to be used, which installs its own levels.
        mgr->active = nullptr;
        mgr->bm->UserFlags.stop_poll = nullptr;
        mgr->bm->UserFlags.stop_poll_opaque = nullptr;
        while (mgr->bm->getAssertLevel() > 0)
          mgr->bm->Pop();
      }
      stp->deleteObjects();
      delete stp;
    }
    catch (const std::exception& e)
    {
      // EngineFatal, or anything else the engine threw: a destructor cannot
      // report it, so the manager refuses every later call instead
      if (!mgr->poisoned)
      {
        mgr->poisoned = true;
        mgr->poison_message = std::string("an engine failure while destroying a solver (") +
                              e.what() + ") may have left its state inconsistent";
      }
    }
    stp = nullptr;
  }
  shelf.clear();
  auto it = std::find(mgr->solvers.begin(), mgr->solvers.end(), this);
  if (it != mgr->solvers.end())
    mgr->solvers.erase(it);
  mgr->release();
}

void SolverImpl::check_alive(const char* fn) const
{
  mgr->check_alive(fn);
}

void SolverImpl::enter(const char* fn)
{
  check_alive(fn);
  // Activation replays the assertion stack and re-applies the options: engine
  // work, so an engine failure there is INTERNAL and poisons the manager.
  engine_call(mgr, fn, [&] { activate(); });
}

std::size_t SolverImpl::level_count() const
{
  return mgr->active == this ? mgr->bm->getAssertLevel() : shelf.size();
}

// The engine has one assertion stack and one set of flags per manager, and
// every solver mirrors its own levels. Switching the active solver is: shelve
// the current one's levels (its pending model is snapshotted first, since it
// reads the engine's tables), pop them, push this one's back, and re-apply
// this one's options over every registry default. The incremental engine is
// each solver's own STP object's and is handed its levels afresh at every
// check, so it does not notice the stack having been away.
void SolverImpl::activate()
{
  if (mgr->active == this)
    return;
  if (mgr->active != nullptr)
    mgr->active->deactivate();
  STPMgr* bm = mgr->bm;
  try
  {
    for (const std::vector<ASTNode>& level : shelf)
    {
      bm->Push();
      for (const ASTNode& a : level)
        bm->AddAssert(a);
    }
  }
  catch (const stp::EngineFatal&)
  {
    throw; // the caller's engine_call poisons the manager
  }
  catch (const std::exception& e)
  {
    // An assertion the engine took before is refused on re-installation: the
    // stack goes back to empty, the shelf is intact, and nothing is active.
    while (bm->getAssertLevel() > 0)
      bm->Pop();
    fail(ErrorCode::INTERNAL, "Solver",
         std::string("the engine refused to reinstall the assertion stack: ") + e.what());
  }
  shelf.clear();
  bm->UserFlags.coverage = coverage;
  mgr->active = this;
  reapply_engine_defaults();
}

void SolverImpl::deactivate()
{
  if (mgr->active != this)
    return;
  ensure_snapshot(); // a pending model reads the engine's tables and stack
  STPMgr* bm = mgr->bm;
  shelf.clear();
  for (const ASTVec* level : bm->AssertLevels())
    shelf.emplace_back(level->begin(), level->end());
  while (bm->getAssertLevel() > 0)
    bm->Pop();
  bm->publishFpCoverage(); // the floating-point counts not yet folded in are this solver's
  coverage = bm->UserFlags.coverage;
  backend_when_shelved = bm->UserFlags.solver_to_use;
  shelved_backend_known = true;
  bm->UserFlags.stop_poll = nullptr;
  bm->UserFlags.stop_poll_opaque = nullptr;
  mgr->active = nullptr;
}

namespace
{
// The engine's run-time categories (what the command line's -t prints) as
// the statistics' four phases, by index into SolverImpl::last_phase_ms;
// parsing, counterexample construction and array refinement are none.
int phase_of(RunTimes::Category c)
{
  switch (c)
  {
    case RunTimes::BitBlasting: return 1;
    case RunTimes::CNFConversion: return 2;
    case RunTimes::Solving:
    case RunTimes::SATSimplifying:
    case RunTimes::SendingToSAT: return 3;
    case RunTimes::Parsing:
    case RunTimes::CounterExampleGeneration:
    case RunTimes::ArrayReadRefinement:
    case RunTimes::CongruenceCandidates: return -1;
    default: return 0; // the simplifications and substitutions
  }
}

std::array<double, 4> phase_totals(RunTimes& times)
{
  std::array<double, 4> out{};
  for (const RunTimes::CategoryTotal& t : times.totals())
    if (const int phase = phase_of(t.category); phase >= 0)
      out[phase] += static_cast<double>(t.time_ms);
  return out;
}
} // namespace

void SolverImpl::reapply_engine_defaults()
{
  // UserDefinedFlags is not assignable: every registry entry goes back to its
  // default through the apply table, and the few explicit-marker flags and
  // manager constants by hand.
  UserDefinedFlags& flags = mgr->bm->UserFlags;
  flags.bv_term_abstraction_rounds_explicit = false;
  flags.bv_term_abstraction_schema_groups_explicit = false;
  flags.bv_term_abstraction_divmod_explicit = false;
  flags.cadical_factor_explicit = false;
  flags.uf_sort_width = mgr->config.uf_sort_width;
  flags.request_counterexample = true;
  mgr->array_equality_off = false;
  EngineTarget t{flags, mgr, this};
  apply_all_options(t, options, /*force_all=*/true);
}

void SolverImpl::apply_options(const char* fn)
{
  EngineTarget t{mgr->bm->UserFlags, mgr, this};
  engine_call(mgr, fn, [&] { apply_all_options(t, options); });
}

// An entry latched by another behaves as before-first-check while that one
// is true (fp-abstraction under fp-abstraction-incremental: the driver's
// session is prepared once).
Settable SolverImpl::effective_settable(const OptionSpec& spec) const
{
  if (spec.latched_by != nullptr && spec.settable == Settable::ANYTIME)
    if (const OptionSpec* latch = detail::find_option(spec.latched_by))
    {
      const OptionValue v = options.resolved(detail::option_index(latch));
      if (v.index() == 0 && std::get<bool>(v))
        return Settable::BEFORE_FIRST_CHECK;
    }
  return spec.settable;
}

bool SolverImpl::option_window_open(const OptionSpec& spec) const
{
  switch (effective_settable(spec))
  {
    case Settable::ANYTIME: return true;
    case Settable::BEFORE_FIRST_CHECK: return checks == 0;
    case Settable::CONSTRUCTION: return !constructed;
  }
  return false;
}

void SolverImpl::ensure_snapshot()
{
  if (model_pending && produce_models)
  {
    OutputRoute route(&route_sinks);
    model = engine_call(mgr, "Solver::model", [&] { return take_snapshot(Verdict::SAT); });
  }
  model_pending = false;
}

bool SolverImpl::poll_stop(void* opaque)
{
  SolverImpl* s = static_cast<SolverImpl*>(opaque);
  if (s->interrupt.load(std::memory_order_relaxed))
  {
    s->interrupt_consumed = true;
    return true;
  }
  const auto terminate = [s] {
    const InCallback callback;
    return s->terminator->terminate();
  };
  if (s->terminator != nullptr && terminate())
  {
    s->terminator_fired = true;
    return true;
  }
  return false;
}

namespace
{
bool observe_preparation(void* opaque, PreparationStage)
{
  return SolverImpl::poll_stop(opaque);
}

UnknownReason map_reason(::stp::UnknownReason r)
{
  switch (r)
  {
    case ::stp::UnknownReason::None: return UnknownReason::OTHER;
    case ::stp::UnknownReason::Timeout: return UnknownReason::TIMEOUT;
    case ::stp::UnknownReason::ConflictBudget: return UnknownReason::CONFLICT_LIMIT;
    case ::stp::UnknownReason::Incomplete: return UnknownReason::INCOMPLETE;
    case ::stp::UnknownReason::CarrierExhausted: return UnknownReason::CARRIER_EXHAUSTED;
    case ::stp::UnknownReason::AssumedInjectivity: return UnknownReason::ASSUMED_INJECTIVITY;
    case ::stp::UnknownReason::AIGBudget: return UnknownReason::RESOURCE_LIMIT;
    case ::stp::UnknownReason::StoppedAfterCnf: return UnknownReason::STOPPED_AFTER_CNF;
  }
  return UnknownReason::OTHER;
}

std::string reason_sentence(UnknownReason r, const std::string& detail)
{
  if (!detail.empty())
    return detail;
  switch (r)
  {
    case UnknownReason::TIMEOUT: return "the time budget expired";
    case UnknownReason::CONFLICT_LIMIT: return "the conflict budget expired";
    case UnknownReason::INTERRUPTED: return "the check was interrupted";
    case UnknownReason::INCOMPLETE: return "the decision procedure is incomplete for this input";
    case UnknownReason::RESOURCE_LIMIT: return "an internal resource budget was exhausted";
    case UnknownReason::CARRIER_EXHAUSTED: return "a declared sort ran out of carrier width (uf-sort-width)";
    case UnknownReason::ASSUMED_INJECTIVITY: return "the answer depended on an injectivity assumption";
    case UnknownReason::STOPPED_AFTER_CNF: return "stopped after CNF generation";
    default: return "no answer";
  }
}

// every level's assertions, base level first, without touching the levels
std::vector<ASTNode> flat_assertions(STPMgr* bm)
{
  std::vector<ASTNode> out;
  for (const ASTVec* level : bm->AssertLevels())
    out.insert(out.end(), level->begin(), level->end());
  return out;
}

// whether some node under `roots` satisfies `pred`
template <typename Pred>
bool any_node(const std::vector<ASTNode>& roots, Pred pred)
{
  ASTNodeSet seen;
  std::vector<ASTNode> stack(roots.begin(), roots.end());
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (n.IsNull() || !seen.insert(n).second)
      continue;
    if (pred(n))
      return true;
    for (const ASTNode& c : n.GetChildren())
      stack.push_back(c);
  }
  return false;
}

bool is_array_equality(const ASTNode& n)
{
  return n.GetKind() == ARRAY_EQ ||
         (n.GetKind() == EQ && n.Degree() == 2 && n[0].GetType() == ARRAY_TYPE);
}

bool is_uf_application(const ASTNode& n)
{
  return n.GetKind() == UF_APPLY;
}
} // namespace

// The adoption a script that ran left for the next call on the manager
// (ManagerImpl::pending_roots): engine reads, whose failure is the call's.
void ManagerImpl::settle(const char* fn)
{
  adoption_pending = false;
  const std::vector<ASTNode> roots = std::move(pending_roots);
  pending_roots.clear();
  engine_call(this, fn, [&] {
    if (any_node(roots, is_array_equality))
    {
      // what the script's content needs, as at the end of a parse
      array_equality_seen = true;
      bm->UserFlags.enable_array_equality = true;
    }
    adopt_engine_symbols(roots);
  });
}

// What one run of the engine (a check, or an input read with EXECUTE)
// sets up and takes down: every CNF the engine generates goes to the
// solver's CNF sink, and the mark of a run that ended at its first CNF
// starts clear.
struct CheckRun
{
  STPMgr* bm;
  explicit CheckRun(SolverImpl* s) : bm(s->mgr->bm)
  {
    bm->run_ended_after_cnf = false;
    if (s->cnf_sink)
      bm->cnf_listener = [s](const std::string& dimacs, ::stp::CnfExtent extent) {
        const CnfScope scope = extent == ::stp::CnfExtent::Partial ? CnfScope::PARTIAL
                               : extent == ::stp::CnfExtent::OverApproximation
                                   ? CnfScope::OVER_APPROXIMATION
                                   : CnfScope::WHOLE;
        // A sink's exception has nowhere to go inside the engine.
        try
        {
          const InCallback callback;
          s->cnf_sink(dimacs, scope);
        }
        catch (...)
        {
        }
      };
  }
  ~CheckRun() { bm->cnf_listener = nullptr; }
  CheckRun(const CheckRun&) = delete;
  CheckRun& operator=(const CheckRun&) = delete;
};

Result SolverImpl::run_check(const char* fn, const std::vector<ASTNode>& assumptions,
                             const std::optional<CheckBudget>& budget)
{
  check_alive(fn);
  OutputRoute route(&route_sinks);
  return engine_call(mgr, fn, [&] {
    activate();
    return run_check_impl(fn, assumptions, budget);
  });
}

Result SolverImpl::run_check_impl(const char* fn, const std::vector<ASTNode>& assumptions,
                                  const std::optional<CheckBudget>& budget)
{
  if (budget.has_value() && budget->time.has_value() && budget->time->count() < 0)
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "a check's time budget cannot be negative (0ms gives up at once; leave the field "
         "empty for no limit)");
  ensure_snapshot();
  // the options' consistency depends on them alone: established once per
  // generation (a refusal leaves it unestablished, and is raised again)
  if (consistent_generation != options.generation)
  {
    options.resolve(fn);
    consistent_generation = options.generation;
  }
  apply_options(fn);
  validate_engine_options(mgr->bm->UserFlags);

  STPMgr* bm = mgr->bm;
  for (const ASTNode& a : assumptions)
    if (a.GetSourceSort().kind() != SourceSort::Kind::Bool)
      fail(ErrorCode::SORT_MISMATCH, fn, "an assumption must be a Boolean term", std::nullopt,
           {make_term(mgr, a)});

  // Content a theory switch forced off cannot be decided: refused here, with
  // the solver as it was, where the engine would otherwise abort. (Under
  // `auto` the machinery was engaged when such content was built or parsed.)
  {
    UFContext* ctx = bm->getUFContextIfAny();
    const bool uf_off = !bm->UserFlags.enable_uninterpreted_functions && ctx != nullptr &&
                        !ctx->activeDeclarations().empty();
    if (uf_off || mgr->array_equality_off)
    {
      std::vector<ASTNode> roots = flat_assertions(bm);
      roots.insert(roots.end(), assumptions.begin(), assumptions.end());
      if (uf_off && any_node(roots, is_uf_application))
        fail(ErrorCode::UNSUPPORTED, fn,
             "the assertions apply an uninterpreted function, which "
             "uninterpreted-functions = off switched off");
      if (mgr->array_equality_off && any_node(roots, is_array_equality))
        fail(ErrorCode::UNSUPPORTED, fn,
             "the assertions compare arrays for equality, which array-equality = off "
             "switched off");
    }
  }

  have_last = false;
  model.reset();
  candidate.reset();
  model_pending = false;
  last_assumptions = assumptions;
  last_failed_assumptions.clear();
  ++checks;

  // an interrupt that arrived before the check is consumed by it
  if (interrupt.exchange(false))
  {
    last = Result(Verdict::UNKNOWN, UnknownReason::INTERRUPTED,
                  reason_sentence(UnknownReason::INTERRUPTED, ""));
    have_last = true;
    return last;
  }

  // the query the engine decides: assertions AND NOT query
  ASTNode query = bm->ASTFalse;
  if (assumptions.size() == 1)
    query = bm->defaultNodeFactory->CreateNode(NOT, assumptions[0]);
  else if (assumptions.size() > 1)
  {
    ASTVec kids(assumptions.begin(), assumptions.end());
    query = bm->defaultNodeFactory->CreateNode(NOT, bm->defaultNodeFactory->CreateNode(AND, kids));
  }

  // budgets for this check
  UserDefinedFlags& flags = bm->UserFlags;
  const std::int64_t saved_ms = flags.timeout_max_time_ms;
  const std::int64_t saved_confl = flags.timeout_max_conflicts;
  if (budget.has_value())
  {
    if (budget->time.has_value())
      flags.timeout_max_time_ms = budget->time->count();
    if (budget->conflicts.has_value())
      flags.timeout_max_conflicts = static_cast<std::int64_t>(*budget->conflicts);
  }
  flags.stop_poll = &SolverImpl::poll_stop;
  flags.stop_poll_opaque = this;
  interrupt_consumed = false;
  terminator_fired = false;
  const PreparationControl outer(PreparationControl::Clock::time_point::max(), nullptr,
                                 &observe_preparation, this);
  const PreparationControl* saved_control = bm->preparation_control;
  bm->preparation_control = &outer;
  GlobalParserBM = bm;

  struct Restore
  {
    UserDefinedFlags& flags;
    STPMgr* bm;
    std::int64_t ms, confl;
    const PreparationControl* control;
    ~Restore()
    {
      flags.timeout_max_time_ms = ms;
      flags.timeout_max_conflicts = confl;
      flags.stop_poll = nullptr;
      flags.stop_poll_opaque = nullptr;
      bm->preparation_control = control;
    }
  } restore{flags, bm, saved_ms, saved_confl, saved_control};
  const CheckRun run(this);

  const auto started = std::chrono::steady_clock::now();
  const std::array<double, 4> phases_before = phase_totals(*bm->GetRunTimes());
  // The last check's Real model does not describe this one.
  bm->InvalidateRealModel();
  stp->ClearAllTables();
  bm->clearUnknown();

  SOLVER_RETURN_TYPE out = SOLVER_UNDECIDED;
  last_incremental = false;
  try
  {
    bool active_real = lra::Frontend::containsRealSyntax(query);
    if (!active_real)
      for (const ASTNode& a : bm->GetAsserts())
        if (lra::Frontend::containsRealSyntax(a))
        {
          active_real = true;
          break;
        }
    active_real = active_real || !bm->AllRealSymbols().empty();

    const bool use_incremental =
        !batch_only && !active_real && stp->sessionIncremental &&
        (stp->incrementalFromStart ||
         IncrementalSolver::automaticEngagementReady(flags.incremental_auto_engage_at, false,
                                                     stp->incrementalSolvesRun));
    const bool first_forced =
        IncrementalSolver::forcedFirstSolve(stp->incrementalFromStart, stp->incrementalSolvesRun);
    stp->incrementalSolvesRun++;
    bool done = false;
    if (use_incremental)
    {
      // One formula per level, built without the engine's getVectorOfAsserts,
      // which rewrites each level into its conjunction as a side effect and
      // would make Solver::assertions() report one formula per level.
      ASTVec levels;
      levels.push_back(bm->ASTTrue);
      for (const ASTVec* level : bm->AssertLevels())
      {
        if (level->empty())
          levels.push_back(bm->ASTTrue);
        else if (level->size() == 1)
          levels.push_back((*level)[0]);
        else
          levels.push_back(bm->defaultNodeFactory->CreateNode(AND, *level));
      }
      levels.push_back(bm->defaultNodeFactory->CreateNode(NOT, query));
      IncrementalSolver* inc = stp->getIncrementalSolver();
      if (inc->canHandle(levels))
      {
        out = inc->checkSat(levels, !assumptions.empty(), first_forced);
        last_incremental = true;
        done = true;
      }
    }
    if (!done)
    {
      const ASTVec v = bm->GetAsserts();
      ASTNode input;
      if (v.empty())
        input = bm->ASTTrue;
      else if (v.size() == 1)
        input = v[0];
      else
        input = bm->defaultNodeFactory->CreateNode(AND, v);
      out = stp->TopLevelSTP(input, query);
    }
  }
  catch (const stp::EngineFatal&)
  {
    throw; // INTERNAL, and the manager is poisoned (run_check)
  }
  catch (const PreparationInterrupted&)
  {
    // the engine's own give-up (a deadline, stop-after-cnf), whose reason it
    // noted: this check has no answer
    out = SOLVER_UNDECIDED;
  }
  catch (const std::exception& e)
  {
    // Anything else that unwound through the engine -- a backend refusing
    // its configuration, a callback's exception, an allocation failing --
    // left its tables in no known state: INTERNAL, or RESOURCE for
    // std::bad_alloc, and the manager poisoned, as for an engine failure.
    fail_foreign(mgr, fn, e);
  }
  catch (...)
  {
    fail_engine(mgr, fn, "an exception that is not a std::exception unwound through the check");
  }
  last_wall = std::chrono::steady_clock::now() - started;
  const std::array<double, 4> phases_after = phase_totals(*bm->GetRunTimes());
  for (std::size_t i = 0; i < last_phase_ms.size(); ++i)
    last_phase_ms[i] = phases_after[i] - phases_before[i];

  Result r;
  switch (out)
  {
    case SOLVER_INVALID:
      r = Result(Verdict::SAT, UnknownReason::NONE, "");
      model_pending = true;
      break;
    case SOLVER_VALID:
    {
      // An unsat reached over a carrier too narrow for the query may be an
      // artefact of the encoding rather than a refutation: withheld, as the
      // command line withholds it.
      std::string short_carrier;
      if (!mgr->sorts_by_engine_id.empty())
      {
        ASTVec formulas = bm->GetAsserts();
        formulas.insert(formulas.end(), assumptions.begin(), assumptions.end());
        if (declaredSortCarrierMayBeShort(*bm, formulas, "uf-sort-width", short_carrier))
        {
          bm->noteUnknown(::stp::UnknownReason::CarrierExhausted, short_carrier);
          r = Result(Verdict::UNKNOWN, UnknownReason::CARRIER_EXHAUSTED,
                     reason_sentence(UnknownReason::CARRIER_EXHAUSTED, short_carrier));
          break;
        }
      }
      r = Result(Verdict::UNSAT, UnknownReason::NONE, "");
      // the driver's failed conjuncts, mapped back to the assumptions as the
      // SMT-LIB frontend maps them (flattened, distinct lowered, the whole
      // set when one does not map); the batch pipeline reports none
      if (last_incremental && stp->hasIncrementalSolver())
      {
        const ASTVec terms(assumptions.begin(), assumptions.end());
        for (std::size_t i : stp->getIncrementalSolver()->lastUnsatAssumptionIndices(terms))
          last_failed_assumptions.push_back(assumptions[i]);
      }
      else
        last_failed_assumptions = assumptions;
      break;
    }
    default:
    {
      UnknownReason reason = map_reason(bm->getUnknownReason());
      std::string detail = bm->getUnknownReasonDetail();
      if (interrupt_consumed || terminator_fired)
      {
        reason = UnknownReason::INTERRUPTED;
        detail.clear();
      }
      r = Result(Verdict::UNKNOWN, reason, reason_sentence(reason, detail));
      // a candidate model the engine left behind
      if (stp->Ctr_Example != nullptr && stp->Ctr_Example->CounterExampleSize() > 0 &&
          produce_models)
      {
        // A candidate the API cannot read (its own refusal) is no candidate;
        // an engine failure while it is taken is one like any other --
        // INTERNAL, the manager poisoned -- not a missing candidate.
        try
        {
          candidate = take_snapshot(Verdict::UNKNOWN);
        }
        catch (const Error&)
        {
          candidate.reset();
        }
      }
      break;
    }
  }
  if (interrupt_consumed)
    interrupt.store(false);
  last = r;
  have_last = true;
  return r;
}

void SolverImpl::rebuild_engine()
{
  // Called through enter(): this solver is the active one.
  model.reset();
  candidate.reset();
  model_pending = false;
  have_last = false;
  assertion_names.clear();
  engine_call(mgr, "Solver::reset", [&] {
  while (mgr->bm->getAssertLevel() > 0)
    mgr->bm->Pop();
  stp->deleteObjects();
  delete stp;
  stp = nullptr;
  stp = new STP(mgr->bm);
  mgr->bm->Push();
  checks = 0;
  constructed = false;
  reapply_engine_defaults();
  });
  constructed = true;
}

} // namespace detail

using detail::ManagerImpl;
using detail::SolverImpl;

// ============================================================ Result, Entailment

Result::Result() noexcept : verdict_(Verdict::UNKNOWN), reason_(UnknownReason::OTHER) {}
Result::Result(Verdict v, UnknownReason r, std::string m) noexcept
    : verdict_(v), reason_(v == Verdict::UNKNOWN ? r : UnknownReason::NONE), message_(std::move(m))
{
}
Verdict Result::verdict() const noexcept { return verdict_; }
bool Result::is_sat() const noexcept { return verdict_ == Verdict::SAT; }
bool Result::is_unsat() const noexcept { return verdict_ == Verdict::UNSAT; }
bool Result::is_unknown() const noexcept { return verdict_ == Verdict::UNKNOWN; }
UnknownReason Result::reason() const noexcept { return reason_; }
std::string Result::reason_message() const { return is_unknown() ? message_ : std::string(); }
std::string Result::str() const
{
  if (!is_unknown())
    return to_string(verdict_);
  return std::string("unknown (") + to_string(reason_) + ")";
}
std::ostream& operator<<(std::ostream& os, const Result& r) { return os << r.str(); }

Entailment::Entailment() noexcept : validity_(Validity::UNKNOWN), reason_(UnknownReason::OTHER) {}
Entailment::Entailment(Validity v, UnknownReason r, std::string m) noexcept
    : validity_(v), reason_(v == Validity::UNKNOWN ? r : UnknownReason::NONE), message_(std::move(m))
{
}
Entailment::Entailment(const Result& of_negation) noexcept
    : validity_(of_negation.is_unsat()  ? Validity::VALID
                : of_negation.is_sat() ? Validity::INVALID
                                       : Validity::UNKNOWN),
      reason_(of_negation.reason()), message_(of_negation.reason_message())
{
}
Validity Entailment::validity() const noexcept { return validity_; }
bool Entailment::is_valid() const noexcept { return validity_ == Validity::VALID; }
bool Entailment::is_invalid() const noexcept { return validity_ == Validity::INVALID; }
bool Entailment::is_unknown() const noexcept { return validity_ == Validity::UNKNOWN; }
UnknownReason Entailment::reason() const noexcept { return reason_; }
std::string Entailment::reason_message() const { return is_unknown() ? message_ : std::string(); }
std::string Entailment::str() const
{
  if (!is_unknown())
    return to_string(validity_);
  return std::string("unknown (") + to_string(reason_) + ")";
}
std::ostream& operator<<(std::ostream& os, const Entailment& e) { return os << e.str(); }

// ============================================================ SolverOptions

SolverOptions::SolverOptions(detail::SolverImpl* s) noexcept : solver_(s) {}

namespace
{
// The solver behind a live options view, which the solver's move leaves
// without one: refused as every entry of a moved-from solver is.
SolverImpl* viewed(SolverImpl* s, const char* fn)
{
  if (s == nullptr)
    detail::fail(ErrorCode::STATE, fn, "the solver was moved from");
  return s;
}

void live_write(SolverImpl* s, std::string_view name, const char* fn)
{
  viewed(s, fn)->enter(fn);
  const detail::OptionSpec* spec = detail::find_option(name);
  if (spec == nullptr)
    detail::fail_option(ErrorCode::OPTION_UNKNOWN, std::string(name), "unknown option");
  // Refused before the value is stored, so that the refusal leaves the live
  // options as they were (the applier would refuse it too, but only after
  // the write).
  if (spec->scope == OptionScope::MANAGER)
    detail::fail_option(ErrorCode::OPTION_VALUE, spec->name,
                        "manager-scoped: pass it to TermManager's constructor, not to a solver");
  if (!s->option_window_open(*spec))
  {
    const Settable window = s->effective_settable(*spec);
    detail::fail_option(ErrorCode::OPTION_TIMING, spec->name,
                        std::string("can only be set ") +
                            (window == Settable::CONSTRUCTION
                                 ? "at construction (pass it to Solver's constructor)"
                                 : "before the first check") +
                            (window != spec->settable
                                 ? std::string(" while ") + spec->latched_by + " is true"
                                 : std::string(" (settable = ") + to_string(spec->settable) + ")"));
  }
}

// A write reaches the engine as an application of the whole set, not of the
// one entry: the entries a composite switch implies (disable-simplifications,
// size-reducing-only) or that follow the written one change with it, and an
// entry going back to its default takes them back to theirs, since the set's
// application re-applies every entry the last one left off its default.
void apply_after_write(SolverImpl* s)
{
  s->apply_options("SolverOptions::set");
}
} // namespace

Options SolverOptions::copy() const
{
  Options o;
  *o.impl() = viewed(solver_, "SolverOptions::copy")->options;
  return o;
}
void SolverOptions::set(std::string_view name, std::string_view value)
{
  live_write(solver_, name, "SolverOptions::set");
  viewed(solver_, "SolverOptions::set")->options.set_text("SolverOptions::set", name, value);
  apply_after_write(solver_);
}
void SolverOptions::set_bool(std::string_view name, bool v)
{
  live_write(solver_, name, "SolverOptions::set_bool");
  viewed(solver_, "SolverOptions::set_bool")->options.set("SolverOptions::set_bool", name, v, detail::OptType::BOOL);
  apply_after_write(solver_);
}
void SolverOptions::set_int(std::string_view name, std::int64_t v)
{
  live_write(solver_, name, "SolverOptions::set_int");
  viewed(solver_, "SolverOptions::set_int")->options.set("SolverOptions::set_int", name, v, detail::OptType::INT);
  apply_after_write(solver_);
}
void SolverOptions::set_uint(std::string_view name, std::uint64_t v)
{
  live_write(solver_, name, "SolverOptions::set_uint");
  viewed(solver_, "SolverOptions::set_uint")->options.set("SolverOptions::set_uint", name, v, detail::OptType::UINT);
  apply_after_write(solver_);
}
void SolverOptions::set_str(std::string_view name, std::string_view v)
{
  live_write(solver_, name, "SolverOptions::set_str");
  viewed(solver_, "SolverOptions::set_str")->options.set("SolverOptions::set_str", name, std::string(v), detail::OptType::STRING);
  apply_after_write(solver_);
}
void SolverOptions::set_names(std::string_view name, const std::vector<std::string>& v)
{
  live_write(solver_, name, "SolverOptions::set_names");
  viewed(solver_, "SolverOptions::set_names")->options.set("SolverOptions::set_names", name, v, detail::OptType::SET);
  apply_after_write(solver_);
}
void SolverOptions::set_duration(std::string_view name, std::chrono::milliseconds v)
{
  live_write(solver_, name, "SolverOptions::set_duration");
  viewed(solver_, "SolverOptions::set_duration")->options.set("SolverOptions::set_duration", name, static_cast<std::int64_t>(v.count()),
                       detail::OptType::DURATION);
  apply_after_write(solver_);
}
void SolverOptions::set_bool(Option o, bool v) { set_bool(Options::name_of(o), v); }
void SolverOptions::set_int(Option o, std::int64_t v) { set_int(Options::name_of(o), v); }
void SolverOptions::set_uint(Option o, std::uint64_t v) { set_uint(Options::name_of(o), v); }
void SolverOptions::set_str(Option o, std::string_view v) { set_str(Options::name_of(o), v); }
void SolverOptions::set_duration(Option o, std::chrono::milliseconds v) { set_duration(Options::name_of(o), v); }
void SolverOptions::set_args(const std::vector<std::string>& argv)
{
  viewed(solver_, "SolverOptions::set_args")->enter("SolverOptions::set_args");
  // parse into a copy first so that a bad list changes nothing
  detail::OptionsImpl copy = viewed(solver_, "SolverOptions::set_args")->options;
  copy.set_args("SolverOptions::set_args", argv);
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (copy.is_set[i] && !(viewed(solver_, "SolverOptions::set_args")->options.is_set[i] && viewed(solver_, "SolverOptions::set_args")->options.values[i] == copy.values[i]))
      live_write(solver_, specs[i].name, "SolverOptions::set_args");
  viewed(solver_, "SolverOptions::set_args")->options = copy;
  viewed(solver_, "SolverOptions::set_args")->apply_options("SolverOptions::set_args");
}
void SolverOptions::set_args(int argc, const char* const* argv)
{
  std::vector<std::string> v;
  for (int i = 0; i < argc; ++i)
    v.emplace_back(argv[i]);
  set_args(v);
}
OptionValue SolverOptions::get(std::string_view name) const { return viewed(solver_, "SolverOptions::get")->options.get("SolverOptions::get", name, detail::OptType::PATH); }
bool SolverOptions::get_bool(std::string_view name) const { return std::get<bool>(viewed(solver_, "SolverOptions::get_bool")->options.get("SolverOptions::get_bool", name, detail::OptType::BOOL)); }
std::int64_t SolverOptions::get_int(std::string_view name) const
{
  const OptionValue& v = viewed(solver_, "SolverOptions::get_int")->options.get("SolverOptions::get_int", name, detail::OptType::INT);
  return v.index() == 2 ? static_cast<std::int64_t>(std::get<std::uint64_t>(v)) : std::get<std::int64_t>(v);
}
std::uint64_t SolverOptions::get_uint(std::string_view name) const
{
  const OptionValue& v = viewed(solver_, "SolverOptions::get_uint")->options.get("SolverOptions::get_uint", name, detail::OptType::UINT);
  return v.index() == 1 ? static_cast<std::uint64_t>(std::get<std::int64_t>(v)) : std::get<std::uint64_t>(v);
}
std::string SolverOptions::get_str(std::string_view name) const { return std::get<std::string>(viewed(solver_, "SolverOptions::get_str")->options.get("SolverOptions::get_str", name, detail::OptType::STRING)); }
std::vector<std::string> SolverOptions::get_names(std::string_view name) const { return std::get<std::vector<std::string>>(viewed(solver_, "SolverOptions::get_names")->options.get("SolverOptions::get_names", name, detail::OptType::SET)); }
std::chrono::milliseconds SolverOptions::get_duration(std::string_view name) const { return std::chrono::milliseconds(std::get<std::int64_t>(viewed(solver_, "SolverOptions::get_duration")->options.get("SolverOptions::get_duration", name, detail::OptType::DURATION))); }
OptionValue SolverOptions::resolved(std::string_view name) const
{
  const detail::OptionSpec* s = detail::find_option(name);
  if (s == nullptr)
    detail::fail_option(ErrorCode::OPTION_UNKNOWN, std::string(name), "unknown option");
  return viewed(solver_, "SolverOptions::resolved")->options.resolved(detail::option_index(s));
}
bool SolverOptions::is_set(std::string_view name) const { return viewed(solver_, "SolverOptions::is_set")->options.info(name).is_set; }
void SolverOptions::reset(std::string_view name)
{
  live_write(solver_, name, "SolverOptions::reset");
  viewed(solver_, "SolverOptions::reset")->options.reset(name);
  apply_after_write(solver_);
}
void SolverOptions::reset_all()
{
  SolverImpl* s = viewed(solver_, "SolverOptions::reset_all");
  s->enter("SolverOptions::reset_all");
  // All or nothing, as set_args: an entry whose window has closed refuses
  // the call unless it already holds its default.
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (s->options.is_set[i] &&
        detail::option_text(specs[i], s->options.values[i]) != specs[i].default_text)
      live_write(s, specs[i].name, "SolverOptions::reset_all");
  s->options.reset_all();
  s->apply_options("SolverOptions::reset_all");
}
OptionInfo SolverOptions::info(std::string_view name) const { return viewed(solver_, "SolverOptions::info")->options.info(name); }
std::vector<std::string> SolverOptions::names(std::optional<Tier> tier) const { return viewed(solver_, "SolverOptions::names")->options.names(tier); }
std::string SolverOptions::help(std::optional<Tier> tier) const { return viewed(solver_, "SolverOptions::help")->options.help(tier); }
void SolverOptions::resolve() const { viewed(solver_, "SolverOptions::resolve")->options.resolve("SolverOptions::resolve"); }

// ============================================================ Solver

namespace
{
// The solver behind an entry that touches the engine: alive, and made the
// active one (its assertion levels installed, its options applied).
SolverImpl* live(const Solver& s, const char* fn)
{
  SolverImpl* impl = s.impl();
  if (impl == nullptr)
    detail::fail(ErrorCode::STATE, fn, "the solver was moved from");
  impl->enter(fn);
  return impl;
}

// The solver behind a reader that touches nothing of the engine's (a
// snapshot, the mirrored stack, the option store): alive, not activated, so
// reading several solvers in turn replays no stacks.
SolverImpl* live_read(const Solver& s, const char* fn)
{
  SolverImpl* impl = s.impl();
  if (impl == nullptr)
    detail::fail(ErrorCode::STATE, fn, "the solver was moved from");
  impl->check_alive(fn);
  return impl;
}

ASTNode own_bool(SolverImpl* s, const Term& t, const char* fn, int arg)
{
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the term is null", arg);
  if (t.impl_manager() != s->mgr)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager", arg);
  const ASTNode n = detail::node_of(t);
  if (n.GetSourceSort().kind() != SourceSort::Kind::Bool)
    detail::fail(ErrorCode::SORT_MISMATCH, fn, "expected a Boolean term", arg, {t}, {t.sort()});
  return n;
}
} // namespace

Solver::Solver(TermManager tm, Options options) : impl_(nullptr), options_view_(nullptr)
{
  ManagerImpl* m = tm.impl();
  if (m == nullptr)
    detail::fail(ErrorCode::STATE, "Solver", "the term manager handle was moved from");
  m->check_alive("Solver");
  impl_ = new SolverImpl(m, options);
  options_view_.solver_ = impl_;
}

Solver::Solver(Solver&& o) noexcept : impl_(o.impl_), options_view_(o.impl_)
{
  o.impl_ = nullptr;
  o.options_view_.solver_ = nullptr;
}

Solver& Solver::operator=(Solver&& o) noexcept
{
  if (this != &o)
  {
    delete impl_;
    impl_ = o.impl_;
    options_view_.solver_ = impl_;
    o.impl_ = nullptr;
    o.options_view_.solver_ = nullptr;
  }
  return *this;
}

Solver::~Solver()
{
  delete impl_;
}

TermManager Solver::manager() const
{
  return TermManager(live_read(*this, "Solver::manager")->mgr);
}

SolverOptions& Solver::options()
{
  live_read(*this, "Solver::options");
  return options_view_;
}

const SolverOptions& Solver::options() const
{
  live_read(*this, "Solver::options");
  return options_view_;
}

void Solver::assert_formula(const Term& t)
{
  SolverImpl* s = live(*this, "Solver::assert_formula");
  detail::OutputRoute route(&s->route_sinks);
  const ASTNode n = own_bool(s, t, "Solver::assert_formula", 0);
  // The last check's model is taken while the engine still holds it: the
  // assertion resets the exact Real model, and the certified UF model below.
  s->ensure_snapshot();
  detail::engine_call(s->mgr, "Solver::assert_formula", [&] {
    try
    {
      s->mgr->bm->AddAssert(n);
    }
    catch (const stp::EngineFatal&)
    {
      throw;
    }
    catch (const std::exception& failure)
    {
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::assert_formula",
                   std::string("the engine refused the assertion: ") + failure.what(), 0, {t});
    }
    if (s->stp->Ctr_Example != nullptr && s->stp->Ctr_Example->getUFTheoryAdapter() != nullptr)
      s->stp->Ctr_Example->getUFTheoryAdapter()->invalidateCertifiedModel();
  });
}

void Solver::push(std::uint32_t n)
{
  SolverImpl* s = live(*this, "Solver::push");
  detail::OutputRoute route(&s->route_sinks);
  s->ensure_snapshot();
  detail::engine_call(s->mgr, "Solver::push", [&] {
  for (std::uint32_t i = 0; i < n; ++i)
  {
    s->pushed = true;
    if (s->mgr->bm->UserFlags.incremental_mode != UserDefinedFlags::IncrementalMode::OFF)
      s->stp->sessionIncremental = true;
    s->stp->ClearAllTables();
    try
    {
      s->mgr->bm->Push();
    }
    catch (const stp::EngineFatal&)
    {
      throw;
    }
    catch (const std::exception& failure)
    {
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::push",
                   std::string("the engine refused the push: ") + failure.what());
    }
  }
  });
}

void Solver::pop(std::uint32_t n)
{
  SolverImpl* s = live(*this, "Solver::pop");
  detail::OutputRoute route(&s->route_sinks);
  if (n > level())
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Solver::pop",
                 "cannot pop " + std::to_string(n) + " levels: the solver is at level " +
                     std::to_string(level()),
                 0);
  s->ensure_snapshot();
  detail::engine_call(s->mgr, "Solver::pop", [&] {
  for (std::uint32_t i = 0; i < n; ++i)
  {
    try
    {
      s->mgr->bm->Pop();
      if (s->assertion_names.size() > s->mgr->bm->getAssertLevel())
        s->assertion_names.resize(s->mgr->bm->getAssertLevel());
    }
    catch (const stp::EngineFatal&)
    {
      throw;
    }
    catch (const std::exception& failure)
    {
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::pop",
                   std::string("the engine refused the pop: ") + failure.what());
    }
    if (s->stp->Ctr_Example != nullptr && s->stp->Ctr_Example->getUFTheoryAdapter() != nullptr)
      s->stp->Ctr_Example->getUFTheoryAdapter()->invalidateCertifiedModel();
  }
  });
}

std::uint32_t Solver::level() const noexcept
{
  if (impl_ == nullptr)
    return 0;
  const std::size_t n = impl_->level_count();
  return n == 0 ? 0 : static_cast<std::uint32_t>(n - 1);
}

std::vector<Term> Solver::assertions() const
{
  SolverImpl* s = live_read(*this, "Solver::assertions");
  std::vector<Term> out;
  if (s->mgr->active == s)
  {
    for (const ASTVec* level : s->mgr->bm->AssertLevels())
      for (const ASTNode& a : *level)
        out.push_back(detail::make_term(s->mgr, a));
  }
  else
  {
    for (const std::vector<ASTNode>& level : s->shelf)
      for (const ASTNode& a : level)
        out.push_back(detail::make_term(s->mgr, a));
  }
  return out;
}

void Solver::reset_assertions()
{
  SolverImpl* s = live(*this, "Solver::reset_assertions");
  detail::OutputRoute route(&s->route_sinks);
  s->ensure_snapshot();
  STPMgr* bm = s->mgr->bm;
  detail::engine_call(s->mgr, "Solver::reset_assertions", [&] {
    while (bm->getAssertLevel() > 0)
      bm->Pop();
    bm->Push();
    s->stp->ClearAllTables();
    s->stp->resetIncrementalSolver();
    s->stp->discardRealSession();
    bm->clearUnknown();
  });
  s->have_last = false;
  s->assertion_names.clear();
  s->model.reset();
  s->candidate.reset();
}

void Solver::reset()
{
  SolverImpl* s = live(*this, "Solver::reset");
  detail::OutputRoute route(&s->route_sinks);
  s->options.reset_all();
  s->rebuild_engine();
}

Result Solver::check_sat()
{
  return check_sat({}, std::nullopt);
}

Result Solver::check_sat(const std::vector<Term>& assumptions, std::optional<CheckBudget> budget)
{
  SolverImpl* s = live(*this, "Solver::check_sat");
  std::vector<ASTNode> nodes;
  for (std::size_t i = 0; i < assumptions.size(); ++i)
    nodes.push_back(own_bool(s, assumptions[i], "Solver::check_sat", static_cast<int>(i)));
  return s->run_check("Solver::check_sat", nodes, budget);
}

Entailment Solver::entails(const Term& formula, std::optional<CheckBudget> budget)
{
  SolverImpl* s = live(*this, "Solver::entails");
  const ASTNode f = own_bool(s, formula, "Solver::entails", 0);
  const ASTNode negated = s->mgr->bm->defaultNodeFactory->CreateNode(NOT, f);
  return Entailment(s->run_check("Solver::entails", {negated}, budget));
}

std::vector<Term> Solver::unsat_assumptions() const
{
  SolverImpl* s = live_read(*this, "Solver::unsat_assumptions");
  if (!s->have_last || !s->last.is_unsat())
    detail::fail(ErrorCode::STATE, "Solver::unsat_assumptions",
                 std::string("no unsat assumptions: the last check answered ") +
                     (s->have_last ? s->last.str() : "nothing yet"));
  std::vector<Term> out;
  for (const ASTNode& a : s->last_failed_assumptions)
    out.push_back(detail::make_term(s->mgr, a));
  return out;
}

Model Solver::model() const
{
  // A pending model can only belong to the active solver (a switch snapshots
  // it), so no activation is needed to read one.
  SolverImpl* s = live_read(*this, "Solver::model");
  if (!s->have_last || !s->last.is_sat())
    detail::fail(ErrorCode::NO_MODEL, "Solver::model",
                 std::string("no model: the last check answered ") +
                     (s->have_last ? s->last.str() : "nothing yet"));
  if (!s->produce_models)
    detail::fail(ErrorCode::NO_MODEL, "Solver::model", "no model: produce-models is off");
  if (!s->model)
  {
    if (!s->model_pending)
      detail::fail(ErrorCode::NO_MODEL, "Solver::model", "no model: the engine kept none");
    s->ensure_snapshot();
  }
  if (!s->model)
    detail::fail(ErrorCode::NO_MODEL, "Solver::model", "no model");
  return Model(s->model);
}

std::optional<Model> Solver::candidate_model() const
{
  SolverImpl* s = live_read(*this, "Solver::candidate_model");
  if (!s->candidate)
    return std::nullopt;
  return Model(s->candidate);
}

void Solver::interrupt() noexcept
{
  if (impl_ != nullptr)
    impl_->interrupt.store(true);
}

void Solver::clear_interrupt() noexcept
{
  if (impl_ != nullptr)
    impl_->interrupt.store(false);
}

bool Solver::interrupt_pending() const noexcept
{
  return impl_ != nullptr && impl_->interrupt.load();
}

void Solver::set_terminator(Terminator* t)
{
  live_read(*this, "Solver::set_terminator")->terminator = t;
}

std::optional<Term> Solver::symbol(std::string_view name) const
{
  return manager().symbol(name);
}

// ------------------------------------------------------------ parsing

namespace
{
// The grammar resolves names through the parser interface's frames, not the
// manager: every symbol the API declared has to be introduced to a fresh
// interface before a script can refer to it. Original function names live in
// the UF context; aliases need a parser binding to that same declaration.
void seed_parser_symbols(Cpp_interface& pi, ManagerImpl* m)
{
  for (const auto& entry : m->definitions)
    pi.addFunction(entry.second);
  // The manager's declared sorts, whichever door declared them: a script
  // names one as it names a declared symbol.
  for (std::uint32_t index : m->declared_sort_order)
  {
    const detail::SortRec& r = m->rec(index);
    pi.addSortAlias(r.name, r.source);
  }
  for (const std::string& name : m->symbol_order)
  {
    const detail::SymbolRec& rec = m->symbols.at(name);
    if (rec.is_function)
    {
      if (rec.decl != nullptr && name != rec.decl->name())
        pi.addUninterpretedFunctionAlias(name, rec.decl);
      continue;
    }
    ASTNode node = rec.node;
    // a bind_symbol alias goes in under its own name
    if (name == node.GetName())
      pi.addSymbol(node);
    else
      pi.addSymbolAlias(name, node);
  }
}

// The grammar refuses a declaration of a name already declared at the name,
// with the command line's own text: "unexpected TERMID_TOK, expecting
// STRING_TOK  token: x" (FORMID_TOK for a Boolean, *_FUNCTIONID_TOK for a
// function). The API's error says what that means as well.
std::string explain_redeclaration(const std::string& message)
{
  static const std::string expecting = ", expecting STRING_TOK  token: ";
  const std::size_t at = message.find(expecting);
  if (at == std::string::npos)
    return message;
  const std::size_t unexpected = message.rfind("unexpected ", at);
  if (unexpected == std::string::npos)
    return message;
  const std::string token = message.substr(unexpected + 11, at - unexpected - 11);
  if (token != "TERMID_TOK" && token != "FORMID_TOK" &&
      (token.size() < 15 || token.compare(token.size() - 15, 15, "_FUNCTIONID_TOK") != 0))
    return message;
  const std::string name = message.substr(at + expecting.size());
  return "the name '" + name + "' is already declared (" + message + ")";
}

// Where a parse reads its input: a script in memory, or a stream read as far
// as the parser needs it.
struct ParseSource
{
  std::string_view text;
  std::istream* stream = nullptr;
};

// A stream that failed while a lexer read it; the parse ends there.
struct InputFailed
{
};

// The lexer's reader over a stream (setSMT2Reader): what the
// stream's buffer holds after at most one refill, so that input arriving
// over a pipe is parsed as it arrives rather than once a block has filled.
std::size_t read_stream(char* buf, std::size_t max, void* opaque)
{
  std::istream& in = *static_cast<std::istream*>(opaque);
  if (max == 0)
    return 0;
  // the stream's buffer is the caller's code: a text source, a pipe reader
  const detail::InCallback callback;
  // A stream the caller set to throw (exceptions()) reports by exception
  // what the state bits report otherwise: one that went bad -- its buffer
  // failed, whose own exception the stream rethrows -- is the input failing,
  // IO; one that only reached its end has ended the input.
  try
  {
    if (std::char_traits<char>::eq_int_type(in.peek(), std::char_traits<char>::eof()))
    {
      if (in.bad())
        throw InputFailed();
      return 0;
    }
    std::streamsize n = in.readsome(buf, static_cast<std::streamsize>(max));
    if (n <= 0)
    {
      // a stream buffer that cannot say how much it holds: one character
      char c;
      if (!in.get(c))
      {
        if (in.bad())
          throw InputFailed();
        return 0;
      }
      buf[0] = c;
      n = 1;
    }
    return static_cast<std::size_t>(n);
  }
  catch (const InputFailed&)
  {
    throw;
  }
  catch (...)
  {
    if (in.bad())
      throw InputFailed();
    if (in.eof())
      return 0;
    throw;
  }
}

// The lexer's reader is a process global: set for one parse, then cleared.
struct ReaderScope
{
  explicit ReaderScope(std::istream* in)
  {
    if (in != nullptr)
      setSMT2Reader(&read_stream, in);
  }
  ~ReaderScope() { setSMT2Reader(nullptr, nullptr); }
  ReaderScope(const ReaderScope&) = delete;
  ReaderScope& operator=(const ReaderScope&) = delete;
};

// Runs the SMT-LIB 2 parser over the input, asserting into the solver's
// stack. DECLARE_AND_ASSERT is the API's own reading of a script: every
// theory's keywords live, check-sat skipped, the frontend's responses kept
// for the diagnostics of a failure. EXECUTE and PARSE_ONLY read it as the
// stp command line does: under the script's own set-logic, answering to the
// output sink, and failing only where the parser gives up.
void run_parser(SolverImpl* s, const ParseSource& source, Format format, ParseMode mode,
                const char* fn)
{
  STPMgr* bm = s->mgr->bm;
  s->ensure_snapshot();
  if (format != Format::AUTO && format != Format::SMTLIB2)
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "parse reads SMT-LIB 2 only (SMTLIB2 or AUTO)");
  if (mode != ParseMode::DECLARE_AND_ASSERT && mode != ParseMode::EXECUTE &&
      mode != ParseMode::PARSE_ONLY)
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "not a parse mode");
  const bool runs = mode != ParseMode::DECLARE_AND_ASSERT;
  detail::OutputRoute route(&s->route_sinks);
  std::lock_guard<std::mutex> hold(detail::parser_mutex());
  // The frontend's own refusals unwind to the parse entry and come back as a
  // failed parse (PARSE below, with the stack put back); an engine failure
  // inside the script is caught where the parser is called.
  detail::EngineScope engine_scope;
  const std::vector<ASTNode> before = detail::flat_assertions(bm);
  const std::string script = source.stream == nullptr ? std::string(source.text) : std::string();
  // The frontend asserts, pushes and pops as it goes, so a script that fails
  // part way has already changed the stack; the stack is recorded here, level
  // for level, and put back before the failure is reported, which is what
  // makes PARSE recoverable. A script that only added is cut back; one that
  // popped a level, or conjoined one (a check-sat does), has the stack
  // rebuilt as a solver's shelved stack is reinstalled (activate), which
  // re-enters each level's frame as well as its formulas.
  std::vector<ASTVec> stack_before;
  for (const ASTVec* level : bm->AssertLevels())
    stack_before.push_back(*level);
  auto restore_stack = [&] {
    // A failed EXECUTE parse may already have solved its temporary stack.
    // Its encoding and core provenance cannot survive rolling that stack
    // back, even when the only assertion changes were additions.
    s->stp->ClearAllTables();
    s->stp->resetIncrementalSolver();
    s->stp->discardRealSession();
    bool only_added = bm->getAssertLevel() >= stack_before.size();
    for (std::size_t i = 0; i < stack_before.size() && only_added; ++i)
    {
      const ASTVec& now = *bm->AssertLevels()[i];
      only_added = now.size() >= stack_before[i].size() &&
                   std::equal(stack_before[i].begin(), stack_before[i].end(), now.begin());
    }
    if (only_added)
    {
      while (bm->getAssertLevel() > stack_before.size())
        bm->Pop();
      for (std::size_t i = 0; i < stack_before.size(); ++i)
        bm->AssertLevels()[i]->resize(stack_before[i].size());
      return;
    }
    while (bm->getAssertLevel() > 0)
      bm->Pop();
    for (const ASTVec& level : stack_before)
    {
      bm->Push();
      for (const ASTNode& a : level)
        bm->AddAssert(a);
    }
  };

  const unsigned array_equality_refusals = bm->array_equality_refusals;
  std::set<const UFDecl*> active_before;
  if (UFContext* ctx = bm->getUFContextIfAny())
    for (const UFDecl* d : ctx->activeDeclarations())
      active_before.insert(d);

  // The frontend's switches for the length of the run: which language it
  // answers in, and whether it answers at all. CheckRun hands the run's CNFs
  // to the CNF sink.
  struct RunFlags
  {
    UserDefinedFlags& flags;
    bool print_output, smt2;
    ~RunFlags()
    {
      flags.print_output_flag = print_output;
      flags.smtlib2_parser_flag = smt2;
    }
  } run_flags{bm->UserFlags, bm->UserFlags.print_output_flag,
              bm->UserFlags.smtlib2_parser_flag};
  bm->UserFlags.print_output_flag = runs;
  bm->UserFlags.smtlib2_parser_flag = true;
  const detail::CheckRun run(s);
  input_status = NOT_DECLARED;

  // A check the input runs answers interrupt() and the terminator as
  // check_sat does: the stop poll and the preparation observer are in place
  // for the whole run. A check that reported an interrupt consumes it (at
  // the next check's start, or at the end of the run), so one pending when
  // the run starts stops its first check, and one that arrives after its
  // last check stays pending for the next.
  struct StopHooks
  {
    SolverImpl* s;
    const PreparationControl* control;
    StopHooks(SolverImpl* solver, const PreparationControl* outer) : s(solver), control(outer) {}
    StopHooks(const StopHooks&) = delete;
    StopHooks& operator=(const StopHooks&) = delete;
    ~StopHooks()
    {
      UserDefinedFlags& flags = s->mgr->bm->UserFlags;
      flags.stop_poll = nullptr;
      flags.stop_poll_opaque = nullptr;
      s->mgr->bm->preparation_control = control;
      if (s->interrupt_consumed)
        s->interrupt.store(false);
    }
  };
  // The observer's control latches once it has stopped a check, so each
  // check gets it afresh (arm_stop, at its start).
  std::optional<PreparationControl> stop_control;
  const auto arm_stop = [&stop_control, s] {
    stop_control.emplace(PreparationControl::Clock::time_point::max(), nullptr,
                         &detail::observe_preparation, s);
  };
  std::optional<StopHooks> stop_hooks;
  if (runs)
  {
    s->interrupt_consumed = false;
    s->terminator_fired = false;
    bm->UserFlags.stop_poll = &SolverImpl::poll_stop;
    bm->UserFlags.stop_poll_opaque = s;
    stop_hooks.emplace(s, bm->preparation_control);
    arm_stop();
    bm->preparation_control = &*stop_control;
  }

  // Everything the frontend needs lives in this block: its destructor puts
  // back the switches the script's set-logic turned on, so what the script's
  // content needs is switched on again after it.
  bool keep_uf = false;
  bool array_equality = false;
  {
  // What an SMT-LIB 2 script declared, kept past its end (see the adoption).
  // Declared before the interface, which may tear its frames down again as it
  // is destroyed, and detached from it once read.
  ASTVec declared_at_end;
  Cpp_interface::SortMap sorts_at_end;
  Cpp_interface::FunctionMap definitions_at_end;
  Cpp_interface::AssertionNames assertion_names_at_end;
  // The command line's parse: the manager's factory behind the type checker.
  ::TypeChecker checker(*s->mgr->factory(), *bm);
  Cpp_interface pi(*bm, &checker);
  pi.enableProtocolChecks(runs);
  pi.keepDeclaredSymbolsAtCleanup(&declared_at_end);
  pi.keepSortAliasesAtCleanup(&sorts_at_end);
  pi.keepFunctionsAtCleanup(&definitions_at_end);
  pi.keepAssertionNamesAtCleanup(&assertion_names_at_end);
  // Parser scopes may forget a name, but the manager and its live handles
  // cannot. Refuse a conflicting identity while the parser can still roll
  // back, before adoption would merge sorts by name or hide a new symbol
  // behind an existing binding. An ordinary symbol redeclared at the same
  // source sort is already the same interned node and remains admissible.
  pi.onSymbolDeclaration([mgr = s->mgr](const std::string& name, const ASTNode& node) {
    if (mgr->definitions.count(name) != 0)
      return false;
    const detail::SymbolRec* existing = mgr->find_symbol(name);
    return existing == nullptr || existing->node == node;
  });
  pi.onFunctionDefinition([mgr = s->mgr](const std::string& name) {
    return mgr->find_symbol(name) == nullptr && mgr->definitions.count(name) == 0;
  });
  pi.onSortDeclaration([mgr = s->mgr](const std::string& name, const SourceSort& sort) {
    const auto existing = mgr->sorts_by_name.find(name);
    return existing == mgr->sorts_by_name.end() ||
           mgr->rec(existing->second).source == sort;
  });
  // A script's (reset) empties the manager's Real registries, which the
  // manager's own Real symbols -- declared, made with mk_fresh, adopted from
  // an earlier script -- outlive: each is recorded again there, or every
  // later model reads it as 0. A script that fails after its (reset) keeps
  // them the same way.
  pi.onPublicReset([bm, mgr = s->mgr] {
    bool any = false;
    for (const auto& entry : mgr->symbols)
    {
      const ASTNode& n = entry.second.node;
      if (!entry.second.is_function && n.GetKind() == SYMBOL &&
          n.GetSourceSort().kind() == SourceSort::Kind::Real)
      {
        bm->RecordRealSymbol(n);
        any = true;
      }
    }
    if (any)
      bm->noteReal();
  });
  pi.onCheck([s, &stop_control, &arm_stop] {
    if (s->interrupt_consumed)
      s->interrupt.store(false); // the last check reported it, and ended in an exception
    s->interrupt_consumed = false;
    s->terminator_fired = false;
    if (stop_control)
      arm_stop(); // the same place, so bm->preparation_control still points at it
    // an interrupt already pending is this check's, and answers it at once,
    // as run_check_impl answers one of the API's own checks
    return s->interrupt.exchange(false);
  });
  // The interrupt a check reported is taken back as the check ends, before
  // its answer is written: one requested while it is written (from the output
  // sink, say) is the next check's.
  pi.onCheckEnd([s] {
    if (s->interrupt_consumed)
      s->interrupt.store(false);
    s->interrupt_consumed = false;
  });
  GlobalParserInterface = &pi;
  GlobalSTP = s->stp;
  GlobalParserBM = bm;
  // The frontend's check-sat stops the Parsing timer the CLI started before
  // handing it the file and restarts it afterwards; the bracket has to be
  // balanced here the same way, or the category stack underflows on the
  // first executed check-sat.
  const std::size_t timer_depth = bm->GetRunTimes()->depth();
  bm->GetRunTimes()->start(RunTimes::Parsing);
  struct Restore
  {
    STPMgr* bm;
    std::size_t timer_depth;
    bool uf_before, ax_before;
    ~Restore()
    {
      // An exception out of an executed check-sat leaves the bracket open
      // the other way (the check stopped Parsing, and its own phases never
      // stopped): the stack is cut back to where the parse found it.
      RunTimes* times = bm->GetRunTimes();
      if (times->depth() == timer_depth + 1 && times->innermostIs(RunTimes::Parsing))
        times->stop(RunTimes::Parsing);
      else
        times->unwindTo(timer_depth);
      GlobalParserInterface = nullptr;
      GlobalSTP = nullptr;
      bm->UserFlags.enable_uninterpreted_functions = uf_before;
      bm->UserFlags.enable_array_equality = ax_before;
    }
  } restore{bm, timer_depth, bm->UserFlags.enable_uninterpreted_functions,
            bm->UserFlags.enable_array_equality};
  const ReaderScope reader(source.stream);
  seed_parser_symbols(pi, s->mgr);
  // No set-logic gates the API's own reading: every theory's keywords are
  // live. A run reads the script as the command line does.
  pi.all_theory_tokens = !runs;
  // Declare-and-assert parses are silent; a run answers to the output sink.
  detail::CoutCapture capture(!runs);
  // The interface is per call, the assertion stack is the manager's: give it
  // a frame for every level already pushed (by the API or an earlier script)
  // so that a (pop) in this script can take one back.
  pi.adoptAssertLevels();
  pi.adoptAssertionNames(s->assertion_names);
  // A function the script declares is scoped to the frontend's frame, which
  // deactivates it when the frame goes -- at a (pop), rightly, but also at
  // the end of the script, where the CLI's session ends and this one does
  // not: adopted below, it is the manager's, like a function the API
  // declared. A script that fails is another matter (see the failure paths).
  pi.retainUFDeclarations(true);

  int status = 0;
  std::vector<ASTNode> roots;
  // The grammar admits a function declaration with arguments, an
  // application and a declared sort only while the first switch is on,
  // and the node factory builds an equality between arrays only while
  // the second is (the CLI has set-logic, or -u and -x, turn them on).
  // The API's own reading parses them whatever the logic line says, as
  // its own construction builds them; the switches' values afterwards are
  // decided below. A run leaves them to the script and the options.
  if (!runs)
  {
    bm->UserFlags.enable_uninterpreted_functions = true;
    bm->UserFlags.enable_array_equality = true;
    pi.setPrintSuccess(false);
  }
  if (mode != ParseMode::EXECUTE)
    pi.ignoreCheckSat();
  // The lexer's line counter is a process global that nothing resets
  // between scans; a parse error's line is relative to this script.
  smt2lineno = 1;
  if (source.stream == nullptr)
    SMT2ScanString(script.c_str());
  else
    setSMT2In(nullptr);
  try
  {
    status = SMT2Parse();
  }
  catch (const stp::EngineFatal& e)
  {
    // The engine failed inside the script (a check it ran, a node it
    // built), not the grammar: the manager's state is suspect, so this
    // is INTERNAL and the manager is poisoned, with the stack put back
    // for what it is worth.
    smt2lex_destroy();
    pi.retainUFDeclarations(false);
    restore_stack();
    detail::fail_engine(s->mgr, fn, e.what());
  }
  catch (const InputFailed&)
  {
    smt2lex_destroy();
    pi.abortCurrentCommand();
    pi.retainUFDeclarations(false);
    restore_stack();
    detail::fail(ErrorCode::IO, fn, "reading the input failed");
  }
  catch (const std::exception& e)
  {
    // anything else the engine threw inside the script, reported as
    // engine_call reports it, with the stack put back
    smt2lex_destroy();
    pi.retainUFDeclarations(false);
    restore_stack();
    detail::fail_foreign(s->mgr, fn, e);
  }
  smt2lex_destroy();
  // A command the frontend answered with (error ...) and then skipped (an
  // ill-typed extract, say) leaves the parse "successful" with the
  // command's assertion silently dropped. STP's error behaviour is
  // immediate-exit; for the API's own reading that is a failed parse,
  // stack put back. A run has answered it already, as the command line
  // does, and fails only where the parser gave up.
  if (!runs && status == 0 && !pi.last_error_message.empty())
    status = 1;
  if (status != 0)
  {
    // the interface's teardown deactivates what the failed script declared
    pi.retainUFDeclarations(false);
    restore_stack();
    // A run reads the script as the command line does, where an equality
    // between whole arrays needs array-equality = on (--array-equality):
    // refused, it is the UNSUPPORTED the API's own reading gives under
    // off, not a malformed script.
    if (runs && bm->array_equality_refusals != array_equality_refusals)
      detail::fail(ErrorCode::UNSUPPORTED, fn,
                   "the script compares arrays for equality, which a run decides "
                   "only with array-equality = on");
    detail::fail_parse(fn, smt2lineno, 0,
                       pi.last_error_message.empty()
                           ? "syntax error"
                           : explain_redeclaration(pi.last_error_message));
  }
  // adopt the symbols the script declared
  const std::vector<ASTNode> after = detail::flat_assertions(bm);
  ASTNodeSet old(before.begin(), before.end());
  for (const ASTNode& a : after)
    if (old.count(a) == 0)
      roots.push_back(a);
  if (UFContext* ctx = bm->getUFContextIfAny())
    for (const UFDecl* d : ctx->activeDeclarations())
      roots.push_back(d->identityNode());
  // and the ones no assertion mentions: a script may declare a symbol for a
  // later script, a parse_term or a model read to use (an SMT-LIB 2 script's
  // end has torn its frames down, keeping their symbols in declared_at_end)
  for (const ASTNode& declared : pi.getDeclaredSymbols())
    roots.push_back(declared);
  pi.keepDeclaredSymbolsAtCleanup(nullptr);
  roots.insert(roots.end(), declared_at_end.begin(), declared_at_end.end());
  // and the sorts it declared, which the manager keeps whether or not a
  // symbol of one survives (sort_of_source adopts each by its engine id)
  pi.keepSortAliasesAtCleanup(nullptr);
  sorts_at_end.insert(pi.sortAliases().begin(), pi.sortAliases().end());
  for (const auto& alias : sorts_at_end)
    if (alias.second.arity == 0 &&
        alias.second.body.sourceSort().kind() == SourceSort::Kind::Uninterpreted)
      s->mgr->sort_of_source(alias.second.body.sourceSort(), fn);
  if (runs)
  {
    // A script that ran has answered its questions: what is left is the
    // manager's, and is adopted by the next call on it.
    s->mgr->pending_roots = std::move(roots);
    s->mgr->adoption_pending = true;
  }
  else
  {
    // An assertion made without a run may be refused, so the content is
    // needed now.
    array_equality = detail::any_node(roots, detail::is_array_equality);
    if (!runs && array_equality && s->mgr->array_equality_off)
    {
      // The script is well formed; the switch refuses its content, and the
      // solver stays as it was: the stack put back, and the functions the
      // script declared deactivated (the frontend's end-of-script teardown
      // left them active, for adoption).
      if (UFContext* ctx = bm->getUFContextIfAny())
        for (const UFDecl* d : ctx->activeDeclarations())
          if (active_before.count(d) == 0)
          {
            std::string ignored;
            ctx->deactivate(d, &ignored);
          }
      restore_stack();
      detail::fail(ErrorCode::UNSUPPORTED, fn,
                   "the script compares arrays for equality, which array-equality = off "
                   "switched off");
    }
    s->mgr->adopt_engine_symbols(roots);
    if (array_equality)
      s->mgr->array_equality_seen = true;
  }
  if (UFContext* ctx = bm->getUFContextIfAny())
    keep_uf = !ctx->activeDeclarations().empty();
  // Commit definitions only after every parse/content check succeeded. A
  // failed parse leaves the manager's prior table intact. Definitions popped
  // or reset within this script are absent, while names retained from an
  // earlier call keep their manager lifetime just like declared symbols.
  pi.keepFunctionsAtCleanup(nullptr);
  for (const auto& entry : pi.definedFunctions())
    definitions_at_end.emplace(entry.first, entry.second);
  s->mgr->adopt_definitions(std::move(definitions_at_end));
  pi.keepAssertionNamesAtCleanup(nullptr);
  if (!pi.assertionNames().empty())
    assertion_names_at_end = pi.assertionNames();
  s->assertion_names = std::move(assertion_names_at_end);
  }
  // The switches a script's set-logic turns on are turned back when the
  // interface goes (the CLI keeps its interface alive through the solve);
  // keep what the script's content needs, as the API's own declare and
  // equality do.
  if (keep_uf)
    bm->UserFlags.enable_uninterpreted_functions = true;
  if (array_equality)
    bm->UserFlags.enable_array_equality = true;

  // What the command line did once the input was read, the Parsing timer
  // stopped: nothing more for a script, which ran as it was read, but the
  // timing report for --parse-only. A run that ended at its first CNF says
  // nothing more.
  if (!runs || bm->run_ended_after_cnf)
    return;
  if (mode == ParseMode::PARSE_ONLY && bm->UserFlags.quick_statistics_flag)
    bm->GetRunTimes()->print();
}
} // namespace

void Solver::parse_smt2(std::string_view script, ParseMode mode)
{
  SolverImpl* s = live(*this, "Solver::parse_smt2");
  run_parser(s, ParseSource{script, nullptr}, Format::SMTLIB2, mode, "Solver::parse_smt2");
}

void Solver::parse(std::string_view text, Format format)
{
  SolverImpl* s = live(*this, "Solver::parse");
  run_parser(s, ParseSource{text, nullptr}, format, ParseMode::DECLARE_AND_ASSERT,
             "Solver::parse");
}

void Solver::parse(std::istream& in, Format format, ParseMode mode)
{
  SolverImpl* s = live(*this, "Solver::parse");
  run_parser(s, ParseSource{std::string_view(), &in}, format, mode, "Solver::parse");
}

void Solver::parse_file(std::string_view path, Format format)
{
  SolverImpl* s = live(*this, "Solver::parse_file");
  const std::string p(path);
  std::ifstream in(p, std::ios::binary);
  if (!in)
    detail::fail(ErrorCode::IO, "Solver::parse_file", "cannot open '" + p + "'", 0);
  std::stringstream buffer;
  buffer << in.rdbuf();
  const std::string text = buffer.str();
  run_parser(s, ParseSource{text, nullptr}, format, ParseMode::DECLARE_AND_ASSERT,
             "Solver::parse_file");
}

namespace
{
// Whether `text` is one SMT-LIB 2 term as the lexer (smt2.lex) reads it: an
// atom or one parenthesised expression, with nothing but whitespace and
// comments around it. A string literal ("" is its only escape), a quoted
// symbol (|...|, no bar inside) and a comment (; to the end of the line) are
// read as units, since any of them may hold a parenthesis. parse_term puts
// the text inside a command of its own, so this is what keeps a ')' in it
// from closing that command and running whatever follows.
bool is_one_smt2_term(std::string_view text)
{
  const std::size_t n = text.size();
  std::size_t i = 0;
  int depth = 0;
  bool started = false, finished = false;
  const auto delimits = [](char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '(' || c == ')' ||
           c == ';' || c == '"' || c == '|';
  };
  while (i < n)
  {
    const char c = text[i];
    if (c == ';')
    {
      while (i < n && text[i] != '\n')
        ++i;
      continue;
    }
    if (c == ' ' || c == '\t' || c == '\n' || c == '\r')
    {
      ++i;
      continue;
    }
    if (finished)
      return false; // something after the term
    started = true;
    if (c == '(')
    {
      ++depth;
      ++i;
      continue;
    }
    if (c == ')')
    {
      if (depth == 0)
        return false;
      --depth;
      ++i;
    }
    else if (c == '"')
    {
      for (++i;; ++i)
      {
        if (i >= n)
          return false; // unterminated
        if (text[i] == '"')
        {
          if (i + 1 < n && text[i + 1] == '"')
          {
            ++i; // the escaped quote
            continue;
          }
          ++i;
          break;
        }
      }
    }
    else if (c == '|')
    {
      const std::size_t close = text.find('|', i + 1);
      if (close == std::string_view::npos)
        return false;
      i = close + 1;
    }
    else
      while (i < n && !delimits(text[i]))
        ++i;
    if (depth == 0)
      finished = true;
  }
  return started && depth == 0;
}
} // namespace

Term Solver::parse_term(std::string_view text) const
{
  SolverImpl* s = live(*this, "Solver::parse_term");
  // One term and nothing else, before anything is parsed: the text goes
  // inside "(assert ...)", and a ')' in it would close that command and run
  // what followed against this solver ("true) (reset-assertions) ...").
  if (!is_one_smt2_term(text))
    detail::fail_parse("Solver::parse_term", 1, 0, "the text is not exactly one term");
  STPMgr* bm = s->mgr->bm;
  detail::OutputRoute route(&detail::kNoOutput);
  std::lock_guard<std::mutex> hold(detail::parser_mutex());
  s->ensure_snapshot();
  detail::EngineScope engine_scope; // as in run_parser
  // One attempt: parse `script` on a scratch level without folding and hand
  // back the node it asserted (null on a parse failure, with `error` set).
  // The frontend's (error ...) echo goes nowhere, with all else this thread
  // prints (the route above).
  auto attempt = [&](const std::string& script, std::string& error) -> ASTNode {
    bm->Push();
    const auto pushed = bm->getAssertLevel();
    struct Restore
    {
      STPMgr* bm;
      bool uf_before, ax_before;
      ~Restore()
      {
        GlobalParserInterface = nullptr;
        GlobalSTP = nullptr;
        if (bm->getAssertLevel() > 1)
          bm->Pop();
        bm->UserFlags.enable_uninterpreted_functions = uf_before;
        bm->UserFlags.enable_array_equality = ax_before;
      }
    } restore{bm, bm->UserFlags.enable_uninterpreted_functions,
              bm->UserFlags.enable_array_equality};
    // the grammar and the factory admit an application and an array
    // equality only while these are on (see run_parser)
    bm->UserFlags.enable_uninterpreted_functions = true;
    bm->UserFlags.enable_array_equality = true;
    // Over the type checker, as run_parser's parse is: without it an
    // ill-sorted term was handed out, and deciding one could abort.
    ::TypeChecker checker(*bm->hashingNodeFactory, *bm);
    Cpp_interface pi(*bm, &checker);
    GlobalParserInterface = &pi;
    GlobalSTP = s->stp;
    GlobalParserBM = bm;
    seed_parser_symbols(pi, s->mgr);
    pi.all_theory_tokens = true;
    pi.adoptAssertLevels();
    const bool saved_smt2 = bm->UserFlags.smtlib2_parser_flag;
    bm->UserFlags.smtlib2_parser_flag = true;
    pi.ignoreCheckSat();
    pi.setPrintSuccess(false);
    smt2lineno = 1;
    SMT2ScanString(script.c_str());
    int status = 0;
    try
    {
      status = SMT2Parse();
    }
    catch (const stp::EngineFatal& e)
    {
      // an engine failure, not the grammar's refusal: INTERNAL, manager poisoned
      smt2lex_destroy();
      bm->UserFlags.smtlib2_parser_flag = saved_smt2;
      detail::fail_engine(s->mgr, "Solver::parse_term", e.what());
    }
    catch (const std::exception& e)
    {
      smt2lex_destroy();
      bm->UserFlags.smtlib2_parser_flag = saved_smt2;
      detail::fail_foreign(s->mgr, "Solver::parse_term", e);
    }
    smt2lex_destroy();
    bm->UserFlags.smtlib2_parser_flag = saved_smt2;
    // an (error ...) response the frontend recovered from is a failure here (see run_parser)
    if (status == 0 && !pi.last_error_message.empty())
      status = 1;
    if (status != 0)
    {
      error = pi.last_error_message.empty() ? "syntax error" : pi.last_error_message;
      return ASTNode();
    }
    // One assertion on the level pushed for it, as one term makes; the
    // check before parsing is what guarantees it.
    const ASTVec& top = *bm->AssertLevels().back();
    if (bm->getAssertLevel() != pushed || top.size() != 1)
    {
      error = "the text is not exactly one term";
      return ASTNode();
    }
    return top.back();
  };
  std::string error;
  // A Boolean term is asserted as it stands. Any other sort goes through
  // "(= t t)", whose first operand is t (a Boolean t cannot: the factory
  // makes one operand of the two, and the grammar refuses that).
  // (Each copy of the text ends its line, so that a comment closing it
  // cannot swallow the parentheses after it.)
  ASTNode t = attempt("(assert " + std::string(text) + "\n)", error);
  if (t.IsNull())
  {
    const ASTNode eq =
        attempt("(assert (= " + std::string(text) + "\n " + std::string(text) + "\n))", error);
    if (eq.IsNull())
      detail::fail_parse("Solver::parse_term", smt2lineno, 0, error);
    if (eq.Degree() != 2)
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::parse_term",
                   "parse_term cannot recover a term of this sort (arrays and Reals fold)");
    t = eq[0];
  }
  s->mgr->adopt_engine_symbols({t});
  if (detail::any_node({t}, detail::is_array_equality))
    s->mgr->array_equality_seen = true; // what array-equality = auto engages
  // Parsed without folding (so that the equality survived); fold now, as
  // the manager's own construction would have.
  Term parsed = detail::make_term(s->mgr, t);
  return s->mgr->config.simplify ? TermManager(s->mgr).simplify(parsed) : parsed;
}

// ------------------------------------------------------------ printing

namespace
{
void collect_symbols(const std::vector<ASTNode>& roots, std::vector<ASTNode>& symbols,
                     std::vector<SourceSort>& required_sorts,
                     bool& has_fp, bool& has_array, bool& has_uf, bool& has_real)
{
  ASTNodeSet seen;
  std::unordered_set<SourceSort, SourceSort::Hasher> seen_sorts;
  std::vector<ASTNode> stack(roots.begin(), roots.end());
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (n.IsNull() || !seen.insert(n).second)
      continue;
    const SourceSort ss = n.GetSourceSort();
    // A sort can occur only in an assertion, for example the index sort of
    // a constant array. Keep these in traversal order for their declarations.
    if ((ss.kind() == SourceSort::Kind::Array || ss.kind() == SourceSort::Kind::Uninterpreted) &&
        seen_sorts.insert(ss).second)
      required_sorts.push_back(ss);
    if (ss.usesFloatingPointTheory())
      has_fp = true;
    if (ss.kind() == SourceSort::Kind::Array)
      has_array = true;
    if (ss.kind() == SourceSort::Kind::Real || n.isRealTerm())
      has_real = true;
    // a declared sort needs a UF logic as much as a function does
    if (n.GetKind() == UF_APPLY || ss.kind() == SourceSort::Kind::Uninterpreted)
      has_uf = true;
    if (n.GetKind() == SYMBOL)
      symbols.push_back(n);
    for (const ASTNode& c : n.GetChildren())
      stack.push_back(c);
  }
}
} // namespace

std::string Solver::to_smt2(bool with_check_sat) const
{
  SolverImpl* s = live(*this, "Solver::to_smt2");
  ManagerImpl* m = s->mgr;
  STPMgr* bm = m->bm;
  std::ostringstream os;
  std::vector<ASTNode> roots = detail::flat_assertions(bm);
  for (const auto& entry : m->definitions)
  {
    roots.push_back(entry.second.function);
    roots.insert(roots.end(), entry.second.params.begin(), entry.second.params.end());
  }
  std::vector<ASTNode> symbols;
  std::vector<SourceSort> required_sorts;
  bool has_fp = false, has_array = false, has_uf = false, has_real = false;
  bool has_bv = false;
  collect_symbols(roots, symbols, required_sorts, has_fp, has_array, has_uf, has_real);
  for (const std::string& name : m->symbol_order)
    symbols.push_back(m->symbols.at(name).node);
  // Declarations, in first-seen order without duplicates. They are written
  // before the logic is chosen, because the logic must admit them as well as
  // the assertions: a declared symbol no assertion mentions still names its
  // sort, and a script that declares a Real under QF_BV is refused.
  std::ostringstream decls;
  std::unordered_set<std::uint32_t> visited_sorts;
  const std::function<void(std::uint32_t)> visit_sort = [&](std::uint32_t sort) {
    if (!visited_sorts.insert(sort).second)
      return;
    const detail::SortRec& r = m->rec(sort);
    switch (r.kind)
    {
      case SortKind::BV:
        has_bv = true;
        break;
      case SortKind::FP:
      case SortKind::RM:
        has_fp = true;
        break;
      case SortKind::REAL:
        has_real = true;
        break;
      case SortKind::ARRAY:
        has_array = true;
        visit_sort(r.index);
        visit_sort(r.element);
        break;
      case SortKind::UNINTERPRETED:
        has_uf = true;
        decls << "(declare-sort " << detail::quote_symbol(r.name) << " 0)\n";
        break;
      case SortKind::FUN:
        has_uf = true;
        for (std::uint32_t d : r.domain)
          visit_sort(d);
        visit_sort(r.codomain);
        break;
      default:
        break;
    }
  };
  ASTNodeSet declared;
  // Preserve explicitly declared sorts, even unused ones, then declare fresh
  // sorts needed by assertions or symbol signatures. This does not add fresh
  // sorts to the source manager's declared_sorts() list.
  for (std::uint32_t index : m->declared_sort_order)
    visit_sort(index);
  for (const SourceSort& sort : required_sorts)
    visit_sort(m->sort_of_source(sort, "Solver::to_smt2"));
  for (const ASTNode& sym : symbols)
  {
    if (!declared.insert(sym).second)
      continue;
    // the engine's own symbols are not declared, except that a function's
    // identity node is one of them and the function is the user's
    if (bm->FoundIntroducedSymbolSet(sym) && m->decl_of(sym) == nullptr)
      continue;
    if (m->is_const_array(sym))
      continue;
    std::string name;
    auto it = m->names_by_node.find(sym);
    if (it != m->names_by_node.end())
      name = it->second;
    else if (const UFDecl* d = m->decl_of(sym))
      name = d->name();
    else
      name = sym.GetName();
    const std::uint32_t sort = m->sort_of_node(sym, "Solver::to_smt2");
    const detail::SortRec& r = m->rec(sort);
    visit_sort(sort);
    if (r.kind == SortKind::FUN)
    {
      decls << "(declare-fun " << detail::quote_symbol(name) << " (";
      for (std::size_t i = 0; i < r.domain.size(); ++i)
        decls << (i ? " " : "") << m->sort_text(r.domain[i]);
      decls << ") " << m->sort_text(r.codomain) << ")\n";
    }
    else
      decls << "(declare-fun " << detail::quote_symbol(name) << " () " << m->sort_text(sort) << ")\n";
  }
  // the logic
  std::string logic = s->logic;
  if (logic.empty())
  {
    if (has_real && (has_bv || has_fp || has_array))
      // These combinations exceed the named linear-Real fragments. ALL
      // selects the solver's supported combination without misclassifying
      // bit-vectors as part of QF_AUFLRA or inventing a standard logic name.
      logic = "ALL";
    else if (has_real)
      logic = has_uf ? "QF_UFLRA" : "QF_LRA";
    else
    {
      logic = "QF_";
      if (has_array)
        logic += "A";
      if (has_uf)
        logic += "UF";
      logic += "BV";
      if (has_fp)
        logic += "FP";
      if (logic == "QF_ABV" && !has_fp)
        logic = "QF_ABV";
    }
  }
  // The options set on the solver. produce-models is SMT-LIB's own; the rest
  // are STP's, which no reader takes from a script, so they print as
  // comments: the script reads back, and the settings stay on record.
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (s->options.is_set[i] && specs[i].scope == OptionScope::SOLVER)
    {
      const std::string name = specs[i].name;
      std::string text = detail::option_text(specs[i], s->options.values[i]);
      if (name == "produce-models")
        os << "(set-option :produce-models " << text << ")\n";
      else if (name != "logic")
      {
        // one comment line, whatever a string value holds
        for (char& c : text)
          if (c == '\n' || c == '\r')
            c = ' ';
        os << "; " << name << " = " << text << "\n";
      }
    }
  os << "(set-logic " << logic << ")\n";
  os << decls.str();
  for (const auto& entry : m->definitions)
    os << detail::print_definition(m, entry.second);
  // the assertion stack
  bool first_level = true;
  for (const ASTVec* level : bm->AssertLevels())
  {
    if (!first_level)
      os << "(push 1)\n";
    first_level = false;
    for (const ASTNode& a : *level)
    {
      os << "(assert ";
      printer::SMTLIB2_PrintTerm(os, bm, a);
      os << ")\n";
    }
  }
  if (with_check_sat)
    os << "(check-sat)\n";
  return os.str();
}

std::string Solver::to_string(Format f) const
{
  SolverImpl* s = live(*this, "Solver::to_string");
  detail::OutputRoute route(&s->route_sinks);
  ManagerImpl* m = s->mgr;
  STPMgr* bm = m->bm;
  const std::vector<ASTNode> roots = detail::flat_assertions(bm);
  std::ostringstream os;
  switch (f)
  {
    case Format::AUTO:
    case Format::SMTLIB2:
      return to_smt2(false);
    case Format::DOT:
    case Format::GDL:
    {
      ASTNode all = roots.empty() ? bm->ASTTrue
                    : roots.size() == 1 ? roots[0]
                                        : bm->hashingNodeFactory->CreateNode(AND, ASTVec(roots.begin(), roots.end()));
      detail::engine_call(m, "Solver::to_string", [&] {
        if (f == Format::DOT)
          printer::Dot_Print(os, all);
        else
          printer::GDL_Print(os, all);
      });
      return os.str();
    }
  }
  detail::fail(ErrorCode::INVALID_ARGUMENT, "Solver::to_string", "not a format");
}

CnfScope Solver::write_cnf(std::ostream& os) const
{
  SolverImpl* s = live(*this, "Solver::write_cnf");
  STPMgr* bm = s->mgr->bm;
  // Run the batch pipeline up to its first CNF; the check itself is
  // abandoned with STOPPED_AFTER_CNF. The export is not a
  // check: what the last check left is the caller's and is put back however
  // the export ends -- its result, its assumptions and the failed ones, its
  // model (snapshotted first, since the export's pipeline refills the tables
  // a pending model is read from), the candidate, and the count of solves
  // that engages the incremental driver -- and an interrupt pending when it
  // starts is left for the next check.
  if (s->model_pending)
    s->ensure_snapshot();
  struct LastCheck
  {
    SolverImpl* s;
    Result last;
    bool have_last;
    std::vector<ASTNode> assumptions, failed;
    std::shared_ptr<const detail::ModelSnapshot> model, candidate;
    std::chrono::steady_clock::duration wall;
    std::array<double, 4> phase_ms;
    bool incremental;
    std::size_t checks;
    std::size_t solves_run;
    bool interrupt;
    ~LastCheck()
    {
      s->last = last;
      s->have_last = have_last;
      s->last_assumptions = std::move(assumptions);
      s->last_failed_assumptions = std::move(failed);
      s->model_pending = false;
      s->model = std::move(model);
      s->candidate = std::move(candidate);
      s->last_wall = wall;
      s->last_phase_ms = phase_ms;
      s->last_incremental = incremental;
      s->checks = checks;
      s->stp->incrementalSolvesRun = solves_run;
      if (interrupt)
        s->interrupt.store(true);
    }
  } kept{s,
         s->last,
         s->have_last,
         s->last_assumptions,
         s->last_failed_assumptions,
         s->model,
         s->candidate,
         s->last_wall,
         s->last_phase_ms,
         s->last_incremental,
         s->checks,
         s->stp->incrementalSolvesRun,
         s->interrupt.exchange(false)};
  // The first CNF and its scope -- how it relates to the assertions -- come
  // from the listener the engine tells of every CNF, which is the export's
  // for the call: the solver's own sink sees the CNFs checks hand to the SAT
  // solver, and this one is not handed over.
  std::string cnf;
  std::optional<CnfScope> scope;
  struct Restore
  {
    SolverImpl* s;
    STPMgr* bm;
    bool stop;
    std::function<void(std::string_view, CnfScope)> sink;
    ~Restore()
    {
      bm->UserFlags.stop_after_cnf = stop;
      s->batch_only = false;
      s->cnf_sink = std::move(sink);
    }
  } restore{s, bm, bm->UserFlags.stop_after_cnf, std::move(s->cnf_sink)};
  s->cnf_sink = [&cnf, &scope](std::string_view dimacs, CnfScope c) {
    if (scope.has_value())
      return;
    cnf.assign(dimacs);
    scope = c;
  };
  bm->UserFlags.stop_after_cnf = true;
  s->batch_only = true; // the batch pipeline is where the CNF is written
  Result r = s->run_check("Solver::write_cnf", {}, std::nullopt);
  if (!scope.has_value())
  {
    if (r.is_unsat())
      os << "c decided before CNF generation: unsat\np cnf 1 2\n1 0\n-1 0\n";
    else if (r.is_sat())
      os << "c decided before CNF generation: sat\np cnf 0 0\n";
    else if (r.reason() == UnknownReason::INTERRUPTED || r.reason() == UnknownReason::TIMEOUT ||
             r.reason() == UnknownReason::RESOURCE_LIMIT)
      detail::fail(ErrorCode::STATE, "Solver::write_cnf",
                   "the export stopped before its CNF: " + r.reason_message());
    else
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::write_cnf",
                   "the problem has no CNF form: " + r.reason_message());
    return CnfScope::WHOLE;
  }
  os << cnf;
  return *scope;
}

void Solver::set_diagnostic_sink(std::function<void(std::string_view)> sink)
{
  live_read(*this, "Solver::set_diagnostic_sink")->diagnostic_sink = std::move(sink);
}

void Solver::set_output_sink(std::function<void(std::string_view)> sink)
{
  live_read(*this, "Solver::set_output_sink")->output_sink = std::move(sink);
}

void Solver::set_fatal_error_handler(std::function<void(std::string_view)> handler)
{
  live_read(*this, "Solver::set_fatal_error_handler")->fatal_handler = std::move(handler);
}

void Solver::set_cnf_sink(std::function<void(std::string_view, CnfScope)> sink)
{
  live_read(*this, "Solver::set_cnf_sink")->cnf_sink = std::move(sink);
}

Statistics Solver::statistics() const
{
  // Read without activating: a shelved solver's counts are its own record,
  // and activating it would replay its whole stack. One never activated has
  // no record yet, and is activated (its options applied) as before.
  SolverImpl* s = live_read(*this, "Solver::statistics");
  if (s->mgr->active != s && !s->shelved_backend_known)
    s = live(*this, "Solver::statistics");
  STPMgr* bm = s->mgr->bm;
  // the engine holds the active solver's counts; another solver's are its own
  const bool active = s->mgr->active == s;
  if (active)
    bm->publishFpCoverage();
  const UserDefinedFlags::EncodingCoverage& c = active ? bm->UserFlags.coverage : s->coverage;
  typedef UserDefinedFlags UF;
  std::map<std::string, StatisticValue> e;
  e["time.total_ms"] =
      std::chrono::duration<double, std::milli>(s->last_wall).count();
  e["time.simplify_ms"] = s->last_phase_ms[0];
  e["time.bitblast_ms"] = s->last_phase_ms[1];
  e["time.cnf_ms"] = s->last_phase_ms[2];
  e["time.sat_ms"] = s->last_phase_ms[3];
  e["cnf.variables"] = static_cast<std::uint64_t>(c.last_cnf_variables);
  e["cnf.clauses"] = static_cast<std::uint64_t>(c.last_cnf_clauses);
  e["aig.nodes"] = static_cast<std::uint64_t>(c.last_blast_nodes);
  e["checks.total"] = static_cast<std::uint64_t>(s->checks);
  e["checks.bitblasted"] = static_cast<std::uint64_t>(c.queries_bitblasted);
  const char* backend = "minisat";
  switch (active || !s->shelved_backend_known ? bm->UserFlags.solver_to_use : s->backend_when_shelved)
  {
    case UF::CRYPTOMINISAT5_SOLVER: backend = "cryptominisat"; break;
    case UF::CADICAL_SOLVER: backend = "cadical"; break;
    case UF::SIMPLIFYING_MINISAT_SOLVER: backend = "simplifying-minisat"; break;
    default: break;
  }
  e["sat.backend"] = std::string(backend);
  e["incremental.engaged"] = static_cast<std::uint64_t>(s->last_incremental ? 1 : 0);
  static const char* const kinds[] = {"eq", "compare", "ite", "plus", "mult", "divmod"};
  static const int kind_index[] = {UF::ABSTRACT_EQ, UF::ABSTRACT_COMPARE, UF::ABSTRACT_ITE,
                                   UF::ABSTRACT_PLUS, UF::ABSTRACT_MULT, UF::ABSTRACT_DIVMOD};
  for (int i = 0; i < 6; ++i)
  {
    e[std::string("bv.candidates.") + kinds[i]] = static_cast<std::uint64_t>(c.bv_candidates[kind_index[i]]);
    e[std::string("bv.abstracted.") + kinds[i]] = static_cast<std::uint64_t>(c.bv_abstracted[kind_index[i]]);
  }
  e["bv.refinement_rounds"] = static_cast<std::uint64_t>(c.bv_refinement_rounds);
  e["bv.blocking_lemmas"] = static_cast<std::uint64_t>(c.bv_blocking_lemmas);
  e["bv.schema_lemmas"] = static_cast<std::uint64_t>(c.bv_schema_lemmas);
  e["bv.exact.escalations"] = static_cast<std::uint64_t>(c.bv_exact_escalations);
  e["bv.exact.escalations_mult"] = static_cast<std::uint64_t>(c.bv_exact_escalations_mult);
  e["bv.exact.escalations_divmod"] = static_cast<std::uint64_t>(c.bv_exact_escalations_divmod);
  e["bv.exact.clauses"] = static_cast<std::uint64_t>(c.bv_exact_clauses);
  e["bv.exact.variables"] = static_cast<std::uint64_t>(c.bv_exact_variables);
  e["bv.exact.microseconds"] = static_cast<std::uint64_t>(c.bv_exact_microseconds);
  e["bv.schema.clauses"] = static_cast<std::uint64_t>(c.bv_schema_clauses);
  e["bv.schema.variables"] = static_cast<std::uint64_t>(c.bv_schema_variables);
  e["bv.schema.microseconds"] = static_cast<std::uint64_t>(c.bv_schema_microseconds);
  // The schema lemmas by group: all of them as 'group=count,...' in the
  // engine's order, and each group's count as a statistic of its own, named
  // as bv-term-abstraction-schema-groups names the group.
  std::string by_group;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    const std::string group = bvSchemaGroupName(static_cast<BVSchemaGroup>(i));
    const std::uint64_t lemmas = c.bv_schema_group_lemmas[i];
    by_group += (by_group.empty() ? "" : ",") + group + "=" + std::to_string(lemmas);
    e["bv.schema_group." + group + ".lemmas"] = lemmas;
  }
  e["bv.schema_group.lemmas"] = by_group;
  e["uf.applications_lowered"] = static_cast<std::uint64_t>(c.uf_applications_lowered);
  e["uf.constraints_installed"] = static_cast<std::uint64_t>(c.uf_constraints_installed);
  e["fp.candidates"] = static_cast<std::uint64_t>(c.fp_candidates);
  e["fp.abstracted"] = static_cast<std::uint64_t>(c.fp_abstracted);
  e["fp.shared"] = static_cast<std::uint64_t>(c.fp_shared);
  e["fp.chained"] = static_cast<std::uint64_t>(c.fp_chained);
  e["fp.rule_lemmas"] = static_cast<std::uint64_t>(c.fp_rule_lemmas);
  e["fp.cross_rules"] = static_cast<std::uint64_t>(c.fp_cross_rules);
  e["fp.checks"] = static_cast<std::uint64_t>(c.fp_checks);
  e["fp.skipped_checks"] = static_cast<std::uint64_t>(c.fp_skipped_checks);
  e["fp.inconsistent"] = static_cast<std::uint64_t>(c.fp_inconsistent);
  e["fp.value_lemmas"] = static_cast<std::uint64_t>(c.fp_value_lemmas);
  e["fp.box_lemmas"] = static_cast<std::uint64_t>(c.fp_box_lemmas);
  e["fp.shape_lemmas"] = static_cast<std::uint64_t>(c.fp_shape_lemmas);
  e["fp.relational_lemmas"] = static_cast<std::uint64_t>(c.fp_relational_lemmas);
  e["fp.releases"] = static_cast<std::uint64_t>(c.fp_releases);
  e["fp.refinement_rounds"] = static_cast<std::uint64_t>(c.fp_refinement_rounds);
  e["fp.restarts"] = static_cast<std::uint64_t>(c.fp_restarts);
  e["fp.repairs"] = static_cast<std::uint64_t>(c.fp_repairs);
  e["fp.lemma_microseconds"] = static_cast<std::uint64_t>(c.fp_lemma_microseconds);
  return Statistics(std::move(e));
}

// ============================================================ Statistics

namespace
{
struct StatSpec
{
  const char* name;
  enum class StatType
  {
    UINT64,
    DOUBLE,
    STRING
  } type;
  Tier tier;
  const char* help;
};
using StatType = StatSpec::StatType;
const StatSpec kStatSpecs[] = {
#include "gen/stat_table.inc"
};

const StatSpec* stat_spec(std::string_view name)
{
  for (const StatSpec& s : kStatSpecs)
    if (name == s.name)
      return &s;
  // bv.schema_group.<group>.lemmas, one per schema group: the table's
  // bv.schema_group.lemmas entry describes the family
  static const StatSpec kGroupLemmas{"bv.schema_group.<group>.lemmas", StatType::UINT64,
                                     Tier::EXPERT, "the lemmas of one schema group"};
  const std::string_view prefix = "bv.schema_group.", suffix = ".lemmas";
  if (name.size() > prefix.size() + suffix.size() && name.substr(0, prefix.size()) == prefix &&
      name.substr(name.size() - suffix.size()) == suffix)
  {
    const std::string_view group =
        name.substr(prefix.size(), name.size() - prefix.size() - suffix.size());
    for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
      if (group == bvSchemaGroupName(static_cast<BVSchemaGroup>(i)))
        return &kGroupLemmas;
  }
  return nullptr;
}
} // namespace

Statistics::Statistics() = default;
Statistics::Statistics(std::map<std::string, StatisticValue> e) : entries_(std::move(e)) {}
const std::map<std::string, StatisticValue>& Statistics::entries() const { return entries_; }
StatisticValue Statistics::get(std::string_view name) const
{
  auto it = entries_.find(std::string(name));
  if (it != entries_.end())
    return it->second;
  const StatSpec* spec = stat_spec(name);
  if (spec == nullptr)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Statistics::get",
                 "unknown statistic '" + std::string(name) + "'", 0);
  switch (spec->type)
  {
    case StatType::DOUBLE: return 0.0;
    case StatType::STRING: return std::string();
    default: return std::uint64_t(0);
  }
}
std::uint64_t Statistics::uint64(std::string_view name) const
{
  const StatisticValue v = get(name);
  if (v.index() == 0)
    return std::get<std::uint64_t>(v);
  if (v.index() == 1)
    return static_cast<std::uint64_t>(std::get<double>(v));
  detail::fail(ErrorCode::INVALID_ARGUMENT, "Statistics::uint64", "not a numeric statistic", 0);
}
double Statistics::real(std::string_view name) const
{
  const StatisticValue v = get(name);
  if (v.index() == 1)
    return std::get<double>(v);
  if (v.index() == 0)
    return static_cast<double>(std::get<std::uint64_t>(v));
  detail::fail(ErrorCode::INVALID_ARGUMENT, "Statistics::real", "not a numeric statistic", 0);
}
std::string Statistics::str(std::string_view name) const
{
  const StatisticValue v = get(name);
  switch (v.index())
  {
    case 0: return std::to_string(std::get<std::uint64_t>(v));
    case 1: return std::to_string(std::get<double>(v));
    default: return std::get<std::string>(v);
  }
}
Tier Statistics::tier(std::string_view name) const
{
  const StatSpec* spec = stat_spec(name);
  if (spec == nullptr)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Statistics::tier",
                 "unknown statistic '" + std::string(name) + "'", 0);
  return spec->tier;
}
std::ostream& operator<<(std::ostream& os, const Statistics& s)
{
  for (const auto& e : s.entries_)
    os << e.first << " = " << s.str(e.first) << "\n";
  return os;
}

} // namespace api
} // namespace stp

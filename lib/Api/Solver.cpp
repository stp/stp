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
#include "stp/Printer/AssortedPrinters.h"
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
#include <fstream>
#include <iostream>
#include <istream>
#include <mutex>
#include <ostream>
#include <set>
#include <sstream>

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
// driven by the API keeps that text for its diagnostics instead.
struct CoutCapture
{
  std::streambuf* saved = nullptr;
  std::ostringstream buf;
  explicit CoutCapture(bool on)
  {
    if (on)
      saved = std::cout.rdbuf(buf.rdbuf());
  }
  ~CoutCapture()
  {
    if (saved != nullptr)
      std::cout.rdbuf(saved);
  }
  std::string text() const
  {
    std::string t = buf.str();
    while (!t.empty() && (t.back() == '\n' || t.back() == ' '))
      t.pop_back();
    return t;
  }
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
  forget_input_question();
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

bool SolverImpl::option_window_open(const OptionSpec& spec) const
{
  switch (spec.settable)
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
  if (s->terminator != nullptr && s->terminator->terminate())
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
  options.resolve(fn);
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
  // The last check's Real model does not describe this one.
  bm->InvalidateRealModel();
  stp->ClearAllTables();
  bm->clearUnknown();

  SOLVER_RETURN_TYPE out = SOLVER_UNDECIDED;
  std::string failure;
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
        !active_real && stp->sessionIncremental &&
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
  catch (const std::exception& e)
  {
    failure = e.what();
    out = SOLVER_UNDECIDED;
  }
  last_wall = std::chrono::steady_clock::now() - started;

  Result r;
  switch (out)
  {
    case SOLVER_INVALID:
      r = Result(Verdict::SAT, UnknownReason::NONE, "");
      model_pending = true;
      break;
    case SOLVER_VALID:
      r = Result(Verdict::UNSAT, UnknownReason::NONE, "");
      if (last_incremental && stp->hasIncrementalSolver() &&
          stp->getIncrementalSolver()->lastUnsatHasAssumptionGranularity())
      {
        const std::vector<ASTNode> failed = stp->getIncrementalSolver()->lastUnsatAssumptionConjuncts();
        for (const ASTNode& a : assumptions)
          if (std::find(failed.begin(), failed.end(), a) != failed.end())
            last_failed_assumptions.push_back(a);
      }
      else
        last_failed_assumptions = assumptions;
      break;
    default:
    {
      UnknownReason reason = map_reason(bm->getUnknownReason());
      std::string detail = bm->getUnknownReasonDetail();
      if (interrupt_consumed || terminator_fired)
      {
        reason = UnknownReason::INTERRUPTED;
        detail.clear();
      }
      else if (!failure.empty())
      {
        reason = UnknownReason::INCOMPLETE;
        detail = failure;
      }
      r = Result(Verdict::UNKNOWN, reason, reason_sentence(reason, detail));
      // a candidate model the engine left behind
      if (stp->Ctr_Example != nullptr && stp->Ctr_Example->CounterExampleSize() > 0 &&
          produce_models)
      {
        try
        {
          candidate = take_snapshot(Verdict::UNKNOWN);
        }
        catch (...)
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

void SolverImpl::forget_input_question()
{
  input_asserts = ASTNode();
  input_query = ASTNode();
  input_question = ASTNode();
  have_input_question = false;
}

void SolverImpl::rebuild_engine()
{
  // Called through enter(): this solver is the active one.
  model.reset();
  candidate.reset();
  model_pending = false;
  have_last = false;
  forget_input_question();
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
void live_write(SolverImpl* s, std::string_view name, const char* fn)
{
  s->enter(fn);
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
    detail::fail_option(ErrorCode::OPTION_TIMING, spec->name,
                        std::string("can only be set ") +
                            (spec->settable == Settable::CONSTRUCTION
                                 ? "at construction (pass it to Solver's constructor)"
                                 : "before the first check") +
                            " (settable = " + to_string(spec->settable) + ")");
}

void apply_one(SolverImpl* s, std::string_view name)
{
  const detail::OptionSpec* spec = detail::find_option(name);
  detail::EngineTarget t{s->mgr->bm->UserFlags, s->mgr, s};
  const std::size_t index = detail::option_index(spec);
  // a reset entry goes back to its default, which is no request
  t.explicit_value = s->options.is_set[index];
  const OptionValue r = s->options.resolved(index);
  detail::engine_call(s->mgr, "SolverOptions::set", [&] {
    detail::apply_option_to_engine(t, index, *spec, r);
  });
  // the entries that follow this one reach the engine with the next
  // application of the whole set (apply_all_options)
  if (index < s->engine_off_default.size())
    s->engine_off_default[index] =
        s->options.is_set[index] || detail::option_text(*spec, r) != spec->default_text;
}
} // namespace

Options SolverOptions::copy() const
{
  Options o;
  *o.impl() = solver_->options;
  return o;
}
void SolverOptions::set(std::string_view name, std::string_view value)
{
  live_write(solver_, name, "SolverOptions::set");
  solver_->options.set_text("SolverOptions::set", name, value);
  apply_one(solver_, name);
}
void SolverOptions::set_bool(std::string_view name, bool v)
{
  live_write(solver_, name, "SolverOptions::set_bool");
  solver_->options.set("SolverOptions::set_bool", name, v, detail::OptType::BOOL);
  apply_one(solver_, name);
}
void SolverOptions::set_int(std::string_view name, std::int64_t v)
{
  live_write(solver_, name, "SolverOptions::set_int");
  solver_->options.set("SolverOptions::set_int", name, v, detail::OptType::INT);
  apply_one(solver_, name);
}
void SolverOptions::set_uint(std::string_view name, std::uint64_t v)
{
  live_write(solver_, name, "SolverOptions::set_uint");
  solver_->options.set("SolverOptions::set_uint", name, v, detail::OptType::UINT);
  apply_one(solver_, name);
}
void SolverOptions::set_str(std::string_view name, std::string_view v)
{
  live_write(solver_, name, "SolverOptions::set_str");
  solver_->options.set("SolverOptions::set_str", name, std::string(v), detail::OptType::STRING);
  apply_one(solver_, name);
}
void SolverOptions::set_names(std::string_view name, const std::vector<std::string>& v)
{
  live_write(solver_, name, "SolverOptions::set_names");
  solver_->options.set("SolverOptions::set_names", name, v, detail::OptType::SET);
  apply_one(solver_, name);
}
void SolverOptions::set_duration(std::string_view name, std::chrono::milliseconds v)
{
  live_write(solver_, name, "SolverOptions::set_duration");
  solver_->options.set("SolverOptions::set_duration", name, static_cast<std::int64_t>(v.count()),
                       detail::OptType::DURATION);
  apply_one(solver_, name);
}
void SolverOptions::set_bool(Option o, bool v) { set_bool(Options::name_of(o), v); }
void SolverOptions::set_int(Option o, std::int64_t v) { set_int(Options::name_of(o), v); }
void SolverOptions::set_uint(Option o, std::uint64_t v) { set_uint(Options::name_of(o), v); }
void SolverOptions::set_str(Option o, std::string_view v) { set_str(Options::name_of(o), v); }
void SolverOptions::set_duration(Option o, std::chrono::milliseconds v) { set_duration(Options::name_of(o), v); }
void SolverOptions::set_args(const std::vector<std::string>& argv)
{
  solver_->enter("SolverOptions::set_args");
  // parse into a copy first so that a bad list changes nothing
  detail::OptionsImpl copy = solver_->options;
  copy.set_args("SolverOptions::set_args", argv);
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (copy.is_set[i] && !(solver_->options.is_set[i] && solver_->options.values[i] == copy.values[i]))
      live_write(solver_, specs[i].name, "SolverOptions::set_args");
  solver_->options = copy;
  solver_->apply_options("SolverOptions::set_args");
}
void SolverOptions::set_args(int argc, const char* const* argv)
{
  std::vector<std::string> v;
  for (int i = 0; i < argc; ++i)
    v.emplace_back(argv[i]);
  set_args(v);
}
OptionValue SolverOptions::get(std::string_view name) const { return solver_->options.get("SolverOptions::get", name, detail::OptType::PATH); }
bool SolverOptions::get_bool(std::string_view name) const { return std::get<bool>(solver_->options.get("SolverOptions::get_bool", name, detail::OptType::BOOL)); }
std::int64_t SolverOptions::get_int(std::string_view name) const
{
  const OptionValue& v = solver_->options.get("SolverOptions::get_int", name, detail::OptType::INT);
  return v.index() == 2 ? static_cast<std::int64_t>(std::get<std::uint64_t>(v)) : std::get<std::int64_t>(v);
}
std::uint64_t SolverOptions::get_uint(std::string_view name) const
{
  const OptionValue& v = solver_->options.get("SolverOptions::get_uint", name, detail::OptType::UINT);
  return v.index() == 1 ? static_cast<std::uint64_t>(std::get<std::int64_t>(v)) : std::get<std::uint64_t>(v);
}
std::string SolverOptions::get_str(std::string_view name) const { return std::get<std::string>(solver_->options.get("SolverOptions::get_str", name, detail::OptType::STRING)); }
std::vector<std::string> SolverOptions::get_names(std::string_view name) const { return std::get<std::vector<std::string>>(solver_->options.get("SolverOptions::get_names", name, detail::OptType::SET)); }
std::chrono::milliseconds SolverOptions::get_duration(std::string_view name) const { return std::chrono::milliseconds(std::get<std::int64_t>(solver_->options.get("SolverOptions::get_duration", name, detail::OptType::DURATION))); }
OptionValue SolverOptions::resolved(std::string_view name) const
{
  const detail::OptionSpec* s = detail::find_option(name);
  if (s == nullptr)
    detail::fail_option(ErrorCode::OPTION_UNKNOWN, std::string(name), "unknown option");
  return solver_->options.resolved(detail::option_index(s));
}
bool SolverOptions::is_set(std::string_view name) const { return solver_->options.info(name).is_set; }
void SolverOptions::reset(std::string_view name)
{
  live_write(solver_, name, "SolverOptions::reset");
  solver_->options.reset(name);
  apply_one(solver_, name);
}
void SolverOptions::reset_all()
{
  solver_->enter("SolverOptions::reset_all");
  solver_->options.reset_all();
  solver_->apply_options("SolverOptions::reset_all");
}
OptionInfo SolverOptions::info(std::string_view name) const { return solver_->options.info(name); }
std::vector<std::string> SolverOptions::names(std::optional<Tier> tier) const { return solver_->options.names(tier); }
std::string SolverOptions::help(std::optional<Tier> tier) const { return solver_->options.help(tier); }
void SolverOptions::resolve() const { solver_->options.resolve("SolverOptions::resolve"); }

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
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager", arg,
                 {t});
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
Format guess_format(std::string_view path)
{
  const std::size_t dot = path.rfind('.');
  std::string ext = dot == std::string_view::npos ? "" : std::string(path.substr(dot + 1));
  for (char& c : ext)
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
  if (ext == "smt2")
    return Format::SMTLIB2;
  if (ext == "smt")
    return Format::SMTLIB1;
  if (ext == "cvc" || ext == "stp")
    return Format::CVC;
  return Format::SMTLIB2;
}

// The grammar resolves names through the parser interface's frames, not the
// manager: every symbol the API declared has to be introduced to a fresh
// interface before a script can refer to it. Function symbols are found by
// name in the UF context and need no seeding.
void seed_parser_symbols(Cpp_interface& pi, ManagerImpl* m)
{
  for (const std::string& name : m->symbol_order)
  {
    const detail::SymbolRec& rec = m->symbols.at(name);
    if (rec.is_function)
      continue;
    ASTNode node = rec.node;
    pi.addSymbol(node);
  }
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

// The lexers' reader over a stream (setSMT2Reader and its twins): what the
// stream's buffer holds after at most one refill, so that input arriving
// over a pipe is parsed as it arrives rather than once a block has filled.
std::size_t read_stream(char* buf, std::size_t max, void* opaque)
{
  std::istream& in = *static_cast<std::istream*>(opaque);
  if (max == 0)
    return 0;
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

// The lexer readers are process globals: set for one parse, then cleared.
struct ReaderScope
{
  ReaderScope(Format f, std::istream* in)
  {
    if (in == nullptr)
      return;
    if (f == Format::SMTLIB1)
      setSMTReader(&read_stream, in);
    else if (f == Format::CVC)
      setCVCReader(&read_stream, in);
    else
      setSMT2Reader(&read_stream, in);
  }
  ~ReaderScope()
  {
    setSMTReader(nullptr, nullptr);
    setCVCReader(nullptr, nullptr);
    setSMT2Reader(nullptr, nullptr);
  }
  ReaderScope(const ReaderScope&) = delete;
  ReaderScope& operator=(const ReaderScope&) = delete;
};

// A CVC or SMT-LIB 1 input's refusal of itself where the command line's
// FatalError reported it (an input with no query): reported the same way,
// and a failed parse rather than an engine failure.
[[noreturn]] void refuse_input(const char* fn, const char* report)
{
  stp::ReportFatalError(report);
  std::string what(report);
  while (!what.empty() && what.back() == '\n')
    what.pop_back();
  detail::fail_parse(fn, 0, 0, what);
}

// Runs one of the three parsers over the input, asserting into the solver's
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
  if (format == Format::AUTO)
    format = Format::SMTLIB2;
  if (format != Format::SMTLIB2 && format != Format::SMTLIB1 && format != Format::CVC)
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "parse takes SMTLIB2, SMTLIB1 or CVC");
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
  // The frontend asserts and pushes as it goes, so a script that fails part
  // way has already changed the stack; its shape is recorded here and put
  // back before the failure is reported, which is what makes PARSE
  // recoverable.
  const std::size_t levels_before = bm->getAssertLevel();
  std::vector<std::size_t> sizes_before;
  for (const ASTVec* level : bm->AssertLevels())
    sizes_before.push_back(level->size());
  auto restore_stack = [&] {
    while (bm->getAssertLevel() > levels_before)
      bm->Pop();
    const std::vector<ASTVec*>& levels = bm->AssertLevels();
    for (std::size_t i = 0; i < levels.size() && i < sizes_before.size(); ++i)
      if (levels[i]->size() > sizes_before[i])
        levels[i]->resize(sizes_before[i]);
  };

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
    bool print_output, smt1, smt2;
    ~RunFlags()
    {
      flags.print_output_flag = print_output;
      flags.smtlib1_parser_flag = smt1;
      flags.smtlib2_parser_flag = smt2;
    }
  } run_flags{bm->UserFlags, bm->UserFlags.print_output_flag,
              bm->UserFlags.smtlib1_parser_flag, bm->UserFlags.smtlib2_parser_flag};
  bm->UserFlags.print_output_flag = runs;
  bm->UserFlags.smtlib1_parser_flag = format == Format::SMTLIB1;
  bm->UserFlags.smtlib2_parser_flag = format == Format::SMTLIB2;
  const detail::CheckRun run(s);
  input_status = NOT_DECLARED;

  // Everything the frontend needs lives in this block: its destructor puts
  // back the switches the script's set-logic turned on, so what the script's
  // content needs is switched on again after it.
  bool keep_uf = false;
  bool array_equality = false;
  ASTVec question; // a CVC or SMT-LIB 1 input's assertions and query
  {
  // What an SMT-LIB 2 script declared, kept past its end (see the adoption).
  // Declared before the interface, which may tear its frames down again as it
  // is destroyed, and detached from it once read.
  ASTVec declared_at_end;
  // The command line's parse: the manager's factory behind the type checker.
  ::TypeChecker checker(*s->mgr->factory(), *bm);
  Cpp_interface pi(*bm, &checker);
  pi.keepDeclaredSymbolsAtCleanup(&declared_at_end);
  GlobalParserInterface = &pi;
  GlobalSTP = s->stp;
  GlobalParserBM = bm;
  // The frontend's check-sat stops the Parsing timer the CLI started before
  // handing it the file and restarts it afterwards; the bracket has to be
  // balanced here the same way, or the category stack underflows on the
  // first executed check-sat.
  bm->GetRunTimes()->start(RunTimes::Parsing);
  struct Restore
  {
    STPMgr* bm;
    bool uf_before, ax_before;
    ~Restore()
    {
      bm->GetRunTimes()->stop(RunTimes::Parsing);
      GlobalParserInterface = nullptr;
      GlobalSTP = nullptr;
      bm->UserFlags.enable_uninterpreted_functions = uf_before;
      bm->UserFlags.enable_array_equality = ax_before;
    }
  } restore{bm, bm->UserFlags.enable_uninterpreted_functions,
            bm->UserFlags.enable_array_equality};
  const ReaderScope reader(format, source.stream);
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
  // A function the script declares is scoped to the frontend's frame, which
  // deactivates it when the frame goes -- at a (pop), rightly, but also at
  // the end of the script, where the CLI's session ends and this one does
  // not: adopted below, it is the manager's, like a function the API
  // declared. A script that fails is another matter (see the failure paths).
  pi.retainUFDeclarations(true);

  int status = 0;
  std::vector<ASTNode> roots;
  switch (format)
  {
    case Format::SMTLIB2:
    {
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
        detail::fail_parse(fn, smt2lineno, 0,
                           pi.last_error_message.empty() ? "syntax error"
                                                         : pi.last_error_message);
      }
      break;
    }
    case Format::SMTLIB1:
    case Format::CVC:
    {
      ASTVec out;
      // These grammars refuse a malformed input through FatalError itself
      // (a zero-width bit-vector, too few operands), which is the parse's
      // own refusal here, not an engine failure: a failed parse, like a
      // syntax error.
      try
      {
        if (format == Format::SMTLIB1)
        {
          if (source.stream == nullptr)
            SMTScanString(script.c_str());
          else
            setSMTIn(nullptr);
          status = SMTParse(&out);
          smtlex_destroy();
        }
        else
        {
          if (source.stream == nullptr)
            CVCScanString(script.c_str());
          else
            setCVCIn(nullptr);
          status = CVCParse(&out);
          cvclex_destroy();
        }
      }
      catch (const stp::EngineFatal& e)
      {
        if (format == Format::SMTLIB1)
          smtlex_destroy();
        else
          cvclex_destroy();
        status = 1;
        pi.last_error_message = e.what();
      }
      catch (const InputFailed&)
      {
        if (format == Format::SMTLIB1)
          smtlex_destroy();
        else
          cvclex_destroy();
        pi.retainUFDeclarations(false);
        restore_stack();
        detail::fail(ErrorCode::IO, fn, "reading the input failed");
      }
      catch (const std::exception& e)
      {
        if (format == Format::SMTLIB1)
          smtlex_destroy();
        else
          cvclex_destroy();
        pi.retainUFDeclarations(false);
        restore_stack();
        detail::fail_foreign(s->mgr, fn, e);
      }
      if (status != 0)
      {
        pi.retainUFDeclarations(false);
        restore_stack();
        detail::fail_parse(fn, 0, 0,
                           !pi.last_error_message.empty() ? pi.last_error_message
                           : !capture.text().empty()      ? capture.text()
                                                          : std::string("syntax error"));
      }
      // The input's question, for input_to_string and for a run to decide.
      s->forget_input_question();
      if (out.size() == 2)
      {
        s->input_asserts = out[0];
        s->input_query = out[1];
        s->have_input_question = true;
      }
      if (runs)
      {
        question = out;
        break;
      }
      // the parser asserted the assumptions itself; the query becomes an
      // assertion of its negation, so that check_sat answers the file's
      // question: unsat is "valid". QUERY(FALSE), the CVC spelling of "just
      // the assertions", negates to true and adds nothing; a query that is or
      // folds to TRUE negates to false, which is asserted.
      if (out.size() >= 2 && !out[1].IsNull())
      {
        const ASTNode negated = bm->defaultNodeFactory->CreateNode(NOT, out[1]);
        if (negated.GetKind() != TRUE)
          bm->AddAssert(negated);
      }
      break;
    }
    default:
      break;
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
  if (UFContext* ctx = bm->getUFContextIfAny())
    keep_uf = !ctx->activeDeclarations().empty();
  if (array_equality)
    s->mgr->array_equality_seen = true;
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
  // stopped: nothing more for an SMT-LIB 2 script, which ran as it was read;
  // the timing report for --parse-only; a CVC or SMT-LIB 1 query decided and
  // answered. A run that ended at its first CNF says nothing more.
  if (!runs || bm->run_ended_after_cnf)
    return;
  if (mode == ParseMode::PARSE_ONLY)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();
    return;
  }
  if (format == Format::SMTLIB2)
    return;
  if (question.empty())
    refuse_input(fn, "Input is Empty. Please enter some asserts and query\n");
  if (question.size() != 2)
    refuse_input(fn, "Input must contain a query\n");
  try
  {
    // As before any check: nothing of an earlier one's tables or reason.
    s->stp->ClearAllTables();
    bm->clearUnknown();
    const SOLVER_RETURN_TYPE ret = s->stp->TopLevelSTP(question[0], question[1]);
    if (bm->run_ended_after_cnf)
      return;
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();
    ToSATBase::PrintOutput(bm, ret);
  }
  catch (const stp::EngineFatal& e)
  {
    detail::fail_engine(s->mgr, fn, e.what());
  }
  catch (const std::exception& e)
  {
    detail::fail_foreign(s->mgr, fn, e);
  }
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
  run_parser(s, ParseSource{text, nullptr}, format == Format::AUTO ? guess_format(path) : format,
             ParseMode::DECLARE_AND_ASSERT, "Solver::parse_file");
}

Term Solver::parse_term(std::string_view text) const
{
  SolverImpl* s = live(*this, "Solver::parse_term");
  STPMgr* bm = s->mgr->bm;
  detail::OutputRoute route(&detail::kNoOutput);
  std::lock_guard<std::mutex> hold(detail::parser_mutex());
  s->ensure_snapshot();
  detail::EngineScope engine_scope; // as in run_parser
  // One attempt: parse `script` on a scratch level without folding and hand
  // back the node it asserted (null on a parse failure, with `error` set).
  // `quiet` keeps the frontend's (error ...) echo off stdout for a
  // speculative attempt.
  auto attempt = [&](const std::string& script, bool quiet, std::string& error) -> ASTNode {
    bm->Push();
    struct Restore
    {
      STPMgr* bm;
      std::streambuf* saved_cout;
      bool uf_before, ax_before;
      ~Restore()
      {
        if (saved_cout != nullptr)
          std::cout.rdbuf(saved_cout);
        GlobalParserInterface = nullptr;
        GlobalSTP = nullptr;
        if (bm->getAssertLevel() > 1)
          bm->Pop();
        bm->UserFlags.enable_uninterpreted_functions = uf_before;
        bm->UserFlags.enable_array_equality = ax_before;
      }
    } restore{bm, nullptr, bm->UserFlags.enable_uninterpreted_functions,
              bm->UserFlags.enable_array_equality};
    // the grammar and the factory admit an application and an array
    // equality only while these are on (see run_parser)
    bm->UserFlags.enable_uninterpreted_functions = true;
    bm->UserFlags.enable_array_equality = true;
    Cpp_interface pi(*bm, bm->hashingNodeFactory);
    GlobalParserInterface = &pi;
    GlobalSTP = s->stp;
    GlobalParserBM = bm;
    seed_parser_symbols(pi, s->mgr);
  pi.all_theory_tokens = true;
  detail::CoutCapture capture(true);
    pi.adoptAssertLevels();
    const bool saved_smt2 = bm->UserFlags.smtlib2_parser_flag;
    bm->UserFlags.smtlib2_parser_flag = true;
    pi.ignoreCheckSat();
    pi.setPrintSuccess(false);
    std::ostringstream sink;
    if (quiet)
      restore.saved_cout = std::cout.rdbuf(sink.rdbuf());
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
    if (restore.saved_cout != nullptr)
    {
      std::cout.rdbuf(restore.saved_cout);
      restore.saved_cout = nullptr;
    }
    // an (error ...) response the frontend recovered from is a failure here (see run_parser)
    if (status == 0 && !pi.last_error_message.empty())
      status = 1;
    if (status != 0)
    {
      error = pi.last_error_message.empty() ? "syntax error" : pi.last_error_message;
      return ASTNode();
    }
    const ASTVec& top = *bm->AssertLevels().back();
    if (top.empty())
    {
      error = "the text is not a term";
      return ASTNode();
    }
    return top.back();
  };
  std::string error;
  // A Boolean term is asserted as it stands. Any other sort goes through
  // "(= t t)", whose first operand is t (a Boolean t cannot: the factory
  // makes one operand of the two, and the grammar refuses that).
  ASTNode t = attempt("(assert " + std::string(text) + ")", true, error);
  if (t.IsNull())
  {
    const ASTNode eq =
        attempt("(assert (= " + std::string(text) + " " + std::string(text) + "))", false, error);
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
                     bool& has_fp, bool& has_array, bool& has_uf, bool& has_real)
{
  ASTNodeSet seen;
  std::vector<ASTNode> stack(roots.begin(), roots.end());
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (n.IsNull() || !seen.insert(n).second)
      continue;
    const SourceSort ss = n.GetSourceSort();
    if (ss.usesFloatingPointTheory())
      has_fp = true;
    if (ss.kind() == SourceSort::Kind::Array)
      has_array = true;
    if (ss.kind() == SourceSort::Kind::Real || n.isRealTerm())
      has_real = true;
    if (n.GetKind() == UF_APPLY)
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
  std::vector<ASTNode> symbols;
  bool has_fp = false, has_array = false, has_uf = false, has_real = false;
  collect_symbols(roots, symbols, has_fp, has_array, has_uf, has_real);
  for (const std::string& name : m->symbol_order)
    symbols.push_back(m->symbols.at(name).node);
  // the logic
  std::string logic = s->logic;
  if (logic.empty())
  {
    if (has_real && has_fp)
      // the LRA variants of the floating-point logics (fp.to_real, a Real
      // literal under to_fp): the widest one the content needs
      logic = std::string("QF_") + (has_array ? "A" : "") + (has_uf ? "UF" : "") + "BVFPLRA";
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
  os << "(set-logic " << logic << ")\n";
  // options that differ from their defaults
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
    if (s->options.is_set[i] && specs[i].scope == OptionScope::SOLVER)
    {
      const std::string name = specs[i].name;
      const std::string text = detail::option_text(specs[i], s->options.values[i]);
      if (name == "produce-models")
        os << "(set-option :produce-models " << text << ")\n";
      else if (name != "logic")
        os << "(set-option :stp." << name << " " << text << ")\n";
    }
  // declarations, in first-seen order without duplicates
  ASTNodeSet declared;
  for (std::uint32_t index : m->declared_sort_order)
    os << "(declare-sort " << detail::quote_symbol(m->rec(index).name) << " 0)\n";
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
    if (r.kind == SortKind::FUN)
    {
      os << "(declare-fun " << detail::quote_symbol(name) << " (";
      for (std::size_t i = 0; i < r.domain.size(); ++i)
        os << (i ? " " : "") << m->sort_text(r.domain[i]);
      os << ") " << m->sort_text(r.codomain) << ")\n";
    }
    else
      os << "(declare-fun " << detail::quote_symbol(name) << " () " << m->sort_text(sort) << ")\n";
  }
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
    case Format::CVC:
    {
      std::vector<ASTNode> symbols;
      bool has_fp = false, has_array = false, has_uf = false, has_real = false;
      collect_symbols(roots, symbols, has_fp, has_array, has_uf, has_real);
      if (has_fp || has_real || has_uf)
        detail::fail(ErrorCode::UNSUPPORTED, "Solver::to_string",
                     "the CVC presentation language has no floating-point, Real or "
                     "uninterpreted-function syntax");
      ASTNodeSet declared;
      for (const ASTNode& sym : symbols)
      {
        if (!declared.insert(sym).second || bm->FoundIntroducedSymbolSet(sym))
          continue;
        const SourceSort ss = sym.GetSourceSort();
        switch (ss.kind())
        {
          case SourceSort::Kind::Bool:
            os << sym.GetName() << " : BOOLEAN;\n";
            break;
          case SourceSort::Kind::BitVector:
            os << sym.GetName() << " : BITVECTOR(" << ss.bitVectorWidth() << ");\n";
            break;
          case SourceSort::Kind::Array:
            os << sym.GetName() << " : ARRAY BITVECTOR(" << ss.index().packedWidth()
               << ") OF BITVECTOR(" << ss.element().packedWidth() << ");\n";
            break;
          default:
            break;
        }
      }
      for (const ASTNode& a : roots)
      {
        os << "ASSERT(";
        detail::engine_call(m, "Solver::to_string", [&] { printer::PL_Print(os, a, bm); });
        os << ");\n";
      }
      os << "QUERY(FALSE);\n";
      return os.str();
    }
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
    case Format::SMTLIB1:
      break;
  }
  detail::fail(ErrorCode::UNSUPPORTED, "Solver::to_string", "there is no SMT-LIB 1 printer");
}

void Solver::write_cnf(std::ostream& os) const
{
  SolverImpl* s = live(*this, "Solver::write_cnf");
  STPMgr* bm = s->mgr->bm;
  // Run the pipeline up to the first CNF with the sink installed; the check
  // itself is abandoned with STOPPED_AFTER_CNF and leaves the last result and
  // model as they were.
  const Result saved_last = s->last;
  const bool saved_have = s->have_last;
  auto saved_model = s->model;
  auto saved_candidate = s->candidate;
  const bool saved_pending = s->model_pending;
  const bool saved_incremental = s->stp->sessionIncremental;
  const bool saved_stop = bm->UserFlags.stop_after_cnf;
  const std::size_t saved_checks = s->checks;
  std::ostringstream buffer;
  bm->cnf_sink = &buffer;
  bm->UserFlags.stop_after_cnf = true;
  s->stp->sessionIncremental = false; // the batch pipeline is where the CNF is written
  struct Restore
  {
    SolverImpl* s;
    STPMgr* bm;
    bool incremental, stop;
    ~Restore()
    {
      bm->cnf_sink = nullptr;
      bm->UserFlags.stop_after_cnf = stop;
      s->stp->sessionIncremental = incremental;
    }
  } restore{s, bm, saved_incremental, saved_stop};
  if (saved_pending)
    s->ensure_snapshot();
  Result r = s->run_check("Solver::write_cnf", {}, std::nullopt);
  s->last = saved_last;
  s->have_last = saved_have;
  s->model = saved_model;
  s->candidate = saved_candidate;
  s->model_pending = false;
  s->checks = saved_checks;
  const std::string cnf = buffer.str();
  if (cnf.empty())
  {
    if (r.is_unsat())
      os << "c decided before CNF generation: unsat\np cnf 1 2\n1 0\n-1 0\n";
    else if (r.is_sat())
      os << "c decided before CNF generation: sat\np cnf 0 0\n";
    else
      detail::fail(ErrorCode::UNSUPPORTED, "Solver::write_cnf",
                   "the problem has no CNF form: " + r.reason_message());
    return;
  }
  os << cnf;
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

std::string Solver::input_to_string(Format f) const
{
  SolverImpl* s = live(*this, "Solver::input_to_string");
  if (f != Format::CVC && f != Format::SMTLIB2 && f != Format::GDL && f != Format::DOT)
    detail::fail(ErrorCode::UNSUPPORTED, "Solver::input_to_string",
                 "an input prints back as CVC, SMTLIB2, GDL or DOT");
  if (!s->have_input_question)
    detail::fail(ErrorCode::STATE, "Solver::input_to_string",
                 "this solver has read no CVC or SMT-LIB 1 input");
  // The engine's print-back printers write to std::cout: the text is kept
  // here, and the rest of what the engine says goes where the solver's does.
  std::string text;
  const std::function<void(std::string_view)> keep = [&text](std::string_view chunk) {
    text.append(chunk.data(), chunk.size());
  };
  const detail::OutputSinks sinks{&keep, &s->diagnostic_sink, &s->fatal_handler};
  detail::OutputRoute route(&sinks);
  STPMgr* bm = s->mgr->bm;
  detail::engine_call(s->mgr, "Solver::input_to_string", [&] {
    // What the command line printed back: the question, built with the
    // engine's folding factory, whatever the input was parsed with.
    if (s->input_question.IsNull())
      s->input_question =
          bm->CreateNode(AND, bm->CreateNode(NOT, s->input_query), s->input_asserts);
    const ASTNode& question = s->input_question;
    switch (f)
    {
      case Format::CVC: print_STPInput_Back(question, bm); break;
      case Format::SMTLIB2: printer::SMTLIB2_PrintBack(std::cout, question, bm); break;
      case Format::GDL: printer::GDL_Print(std::cout, question); break;
      default: printer::Dot_Print(std::cout, question); break;
    }
    std::cout.flush();
  });
  return text;
}

Statistics Solver::statistics() const
{
  SolverImpl* s = live(*this, "Solver::statistics");
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

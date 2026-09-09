/********************************************************************
  *
 * BEGIN DATE: May, 2022
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

#include "stp/Sat/Cadical.h"
#include <unordered_set>
#include <algorithm>
#include <cstdlib>
#include <deque>
#include <limits>
using std::vector;

namespace stp
{

// The single external propagator CaDiCaL permits, doing both of the jobs STP
// has from inside a search.
//
// preferDecisions(): proposes the hinted literals, in order, whenever
// CaDiCaL asks it for a decision, until each has been proposed once.
// Proposing a hint again after every backtrack was measured to pin the
// search to the seeded values for its whole length: two refutations that
// take a few seconds without hints ran past a minute with it. Seeded once,
// the values persist only as CaDiCaL's own saved phases, which its search
// may then overrule.
//
// connectTheoryPropagator(): forwards the notifications to a theory and
// streams back whatever clauses it asks for. With no hints queued and no
// theory connected this propagates nothing, adds no clauses and accepts
// every model, so CaDiCaL's search is its own except for where it starts.
//
// CaDiCaL requires a proposed literal to be unassigned: proposing an
// assigned or root-fixed one is an API violation, not a no-op. So the
// propagator keeps the assignment of every variable it observes from the
// notifications, in the shape the IPASIR-UP contract lays them out: a
// batch of assignments per notification, a mark per new decision level, and
// a backtrack that unassigns everything above a level. Root-level
// assignments arrive the same way -- a variable fixed before it was
// observed is notified when it is, and CaDiCaL repeats the root level after
// compacting, hence the idempotence -- so a fixed variable stays assigned
// here and is never proposed. Chronological backtracking keeps some
// assignments that were notified above the level it returns to; CaDiCaL
// notifies those again afterwards, which the same idempotence absorbs.
//
// Only on the 3.x line, whose propagator interface this is written to; an
// older CaDiCaL declines every hint in preferDecisions() below and never
// constructs one of these, so it needs only a complete type to destroy.
#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
class Cadical::PropagatorBridge : public CaDiCaL::ExternalPropagator
{
public:
  explicit PropagatorBridge(const Cadical& owner) : owner(owner) {}

  // A literal in CaDiCaL's external numbering.
  void hint(int lit)
  {
    grow(std::abs(lit));
    queue.push_back(lit);
  }

  void setTheory(SATSolver::TheoryPropagator* connected)
  {
    theory = connected;
    clause.clear();
    clause_position = 0;
  }

  bool hasTheory() const { return theory != NULL; }

  void notify_assignment(const std::vector<int>& lits) override
  {
    if (theory != NULL)
      forwarded.clear();
    for (int lit : lits)
    {
      const int v = std::abs(lit);
      grow(v);
      const int8_t value = lit < 0 ? -1 : 1;
      if (assigned[v] != 0)
      {
        assert(assigned[v] == value && "an observed variable notified twice "
                                       "with different values");
        continue;
      }
      assigned[v] = value;
      trail.push_back(v);
      // Only what was new here is forwarded: the theory is told each
      // assignment once, which is what lets it keep an undo stack that
      // matches the notified backtracks one for one.
      if (theory != NULL)
        forwarded.push_back(owner.stpLiteralOfExternal(lit));
    }
    if (theory != NULL && !forwarded.empty())
      theory->notifyAssignments(forwarded);
  }

  void notify_new_decision_level() override
  {
    levels.push_back(trail.size());
    if (theory != NULL)
      theory->notifyNewDecisionLevel();
  }

  void notify_backtrack(size_t new_level) override
  {
    // The theory is told even when this level is one nothing was notified
    // at: it keeps its own stack of levels, and skipping the call would
    // leave that stack deeper than the search's.
    if (theory != NULL)
      theory->notifyBacktrack(new_level);
    if (new_level >= levels.size())
      return; // nothing above that level was ever notified
    const size_t keep = levels[new_level];
    levels.resize(new_level);
    while (trail.size() > keep)
    {
      const int v = trail.back();
      trail.pop_back();
      assigned[v] = 0;
    }
  }

  bool cb_check_found_model(const std::vector<int>& /*model*/) override
  {
    return theory == NULL || theory->checkFinalModel();
  }

  int cb_decide() override
  {
    while (!queue.empty())
    {
      const int lit = queue.front();
      queue.pop_front();
      if (assigned[std::abs(lit)] == 0)
        return lit;
    }
    return 0;
  }

  int cb_propagate() override { return 0; }
  int cb_add_reason_clause_lit(int /*propagated_lit*/) override { return 0; }

  bool cb_has_external_clause(bool& is_forgettable) override
  {
    if (theory == NULL)
      return false;
    // A clause is handed over one literal at a time, so one that is still
    // being read out has to be answered for before the theory is asked for
    // another.
    // Theory consequences of the query, not of the search: irredundant means
    // a lemma is derived once however often the search passes back through
    // the assignment that exposed it. Set on both paths -- CaDiCaL clears
    // the flag before each call, so leaving it alone would work, but not
    // visibly.
    is_forgettable = false;
    if (clause_position < clause.size())
      return true;
    std::vector<uint32_t> next;
    if (!theory->nextClause(next))
      return false;
    clause.clear();
    clause_position = 0;
    clause.reserve(next.size());
    for (uint32_t literal : next)
      clause.push_back(owner.externalLiteralOfStp(literal));
    return true;
  }

  int cb_add_external_clause_lit() override
  {
    if (clause_position >= clause.size())
    {
      clause.clear();
      clause_position = 0;
      return 0; // the closing zero
    }
    return clause[clause_position++];
  }

private:
  void grow(int v)
  {
    if ((size_t)v >= assigned.size())
      assigned.resize((size_t)v + 1, 0);
  }

  const Cadical& owner;
  SATSolver::TheoryPropagator* theory = NULL;
  std::vector<uint32_t> forwarded; // scratch, STP literals
  std::vector<int> clause;         // the clause being handed over
  size_t clause_position = 0;

  std::vector<int8_t> assigned; // by variable: the current value, 0 open
  std::vector<int> trail;       // observed variables in assignment order
  std::vector<size_t> levels;   // trail size at each decision level
  std::deque<int> queue;        // literals to propose, oldest first
};
#else
class Cadical::PropagatorBridge
{
};
#endif

uint32_t Cadical::nVars() const
{
  // Unlike other solvers Cadical doesn't need to be told about the variable in advance.
  return next_variable;
}

bool Cadical::simplify()
{
  s->simplify();
  return false;
}

int Cadical::nClauses()
{
  // Active irredundant clauses: what remains of the input after CaDiCaL's
  // preprocessing, which is the post-simplify() count nClauses() promises.
  // Learnt clauses are counted separately (redundant()) and excluded.
  return (int)s->irredundant();
}

void Cadical::setMaxConflicts(int64_t _max_confl)
{
  assert(_max_confl >= 0);
  max_confl = _max_confl;
}

 //    0 = UNSOLVED     (limit reached or interrupted through 'terminate')
 //   10 = SATISFIABLE
 //   20 = UNSATISFIABLE
bool Cadical::solveInternal(bool& timeout_expired)
{
  // Cadical's conflict limit only applies to the next solve() call and is
  // reset once it returns, so it has to be re-armed here. Cadical exposes no
  // count of the conflicts it has used, so unlike the time budget this one
  // cannot be made to span the whole query: each call gets the full figure.
  if (max_confl >= 0)
  {
    const int budget =
        (int)std::min(max_confl, (int64_t)std::numeric_limits<int>::max());
    s->limit("conflicts", budget);
  }

  // The Terminator reads the query's deadline from the base class, so this
  // only needs connecting -- there is nothing to re-arm.
  if (hasTimeLimit())
  {
    s->connect_terminator(&time_limit);
  }

  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();

  searched = true;
  auto ret = s->solve();
  if (ret == 0)
  {
    timeout_expired = true;
  }
  return ret == 10;
}

bool Cadical::solveWithAssumptionsInternal(const vec_literals& assumps,
                                           bool& timeout_expired)
{
  // Assumptions hold for the next solve() call only, which is exactly the
  // semantics solveWithAssumptions promises. Literal conversion as in
  // addClause -- including the factor translation: an assumption placed
  // under a raw STP index would bind a different CaDiCaL variable than the
  // clauses use, silently constraining nothing. Declaration must also
  // happen before the assumption names the variable, not first inside
  // solveInternal: an assumed variable no clause has mentioned yet would
  // otherwise be imported undeclared, and the range declared for it
  // afterwards would map it elsewhere for the rest of the session.
  //
  // Guarded exactly as the other two call sites are: declareNewVariables()
  // asserts that factoring is on and that there is a gap to close, so an
  // unguarded call aborts on the first assumption solve of a build without
  // factoring -- which is every default build.
  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();
  for (int i = 0; i < assumps.size(); i++)
  {
    uint32_t var = assumps[i].x >> 1;
    uint32_t polarity = assumps[i].x & 1;
    if (factor_enabled)
      var = (uint32_t)ext_of_stp[var];
    s->assume(polarity ? -(int)var : (int)var);
  }

  return solveInternal(timeout_expired);
}

Cadical::Cadical() : time_limit(*this)
{
  s = new CaDiCaL::Solver ();
  s->set("quiet",1);
  // Probe for the "inprobing" option (CaDiCaL 3.x) while the
  // configuration window is certainly open: setting it to its current
  // value changes nothing but reports whether the option exists, which
  // lets a caller decide about a LIVE solver without touching it.
  inprobing_control = s->set("inprobing", s->get("inprobing"));
}

Cadical::~Cadical()
{
  // The propagator, if any, outlives the solver: `bridge` is destroyed after
  // this body, and CaDiCaL's own destructor never calls back into it.
  delete s;
  s = nullptr;
}

void Cadical::printStats() const
{
#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
  // These counters remain available in the UNKNOWN state produced by our
  // Terminator. Keep this compact: CaDiCaL's full reporter is several hundred
  // lines, while these are the search quantities benchmark logs consume.
  std::cerr << "CaDiCaL conflicts: "
            << s->get_statistic_value("conflicts") << std::endl;
  std::cerr << "CaDiCaL decisions: "
            << s->get_statistic_value("decisions") << std::endl;
  std::cerr << "CaDiCaL search propagations: "
            << s->get_statistic_value("propagations") << std::endl;
  std::cerr << "CaDiCaL search ticks: "
            << s->get_statistic_value("ticks") << std::endl;
#else
  // get_statistic_value() is unavailable in the oldest supported releases.
  s->statistics();
#endif
}

uint32_t Cadical::newVar()
{
  return ++next_variable;
}

void Cadical::setFrozen(uint32_t var)
{
  // Deliberately not s->freeze(var). Refinement encodes clauses over
  // these variables in later solve calls, which is safe here without
  // freezing: Cadical restores an eliminated variable the moment a new
  // clause mentions it, and extends every model over the eliminated
  // variables, so both the added clauses and the values the refinement
  // loop reads stay correct. Freezing instead would keep every
  // refinement-visible variable out of inprocessing whether or not any
  // lemma ever mentions it, which measures ~25% slower on the
  // wchains array-equality benchmarks (three-run A/B on wchains016ue:
  // 19.9-20.5s frozen against 15.9-16.0s restored). Solvers without
  // restoration (the simplifying Minisat family) genuinely need their
  // setFrozen; this one is a documented decision, not an omission.
  (void)var;
}

void Cadical::protectFromElimination(uint32_t var)
{
  // The real freeze, for the variables a theory propagator will observe.
  // CaDiCaL only accepts an observation on a clean variable, and there is no
  // moment between "the clauses that would restore an eliminated one have
  // been added" and "the search that restores them has begun" at which it
  // could be observed -- so such a variable has to be kept whole from the
  // start. Nothing melts it again: the query owns these for its lifetime.
  if (var == 0 || var > next_variable)
    return;
  uint32_t external = var;
  if (factor_enabled)
  {
    if (ext_of_stp.size() <= next_variable)
      declareNewVariables();
    external = (uint32_t)ext_of_stp[var];
  }
  s->freeze((int)external);
}

int Cadical::simplifyOnly()
{
  // Rounds of CaDiCaL's own preprocessing. It is allowed to decide the
  // formula outright, which is a perfectly good outcome for the caller:
  // what it wants is whatever ends up fixed at the root, and a solved
  // formula fixes everything.
  searched = true;
  return s->simplify();
}

int Cadical::rootFixed(unsigned x)
{
  // The same translation modelValue performs, and for the same reason:
  // bounded variable addition renumbers, so a variable STP names is not
  // necessarily the one CaDiCaL knows. newVar() already hands out
  // one-based numbers, so there is nothing further to add here -- an
  // off-by-one would read the neighbouring variable's verdict, which is a
  // fact about some other atom entirely.
  if (factor_enabled)
    x = (x < ext_of_stp.size()) ? (uint32_t)ext_of_stp[x] : 0;
  if (x == 0)
    return 0;
  return s->fixed((int)x);
}


bool Cadical::setSearchBiasInternal(SearchBias bias)
{
  // Cadical has named configurations of its own, so this is a straight
  // translation. "unsat" turns off stabilising search and the local-search
  // walker, keeping Cadical in focused, restart-heavy search; "sat" leaves it
  // stabilising and spends more effort on elimination and subsumption.
  //
  // Cadical only accepts a configuration "right after initialization", which
  // is why this is applied here rather than at solve time. Setting "quiet" in
  // the constructor doesn't spoil that: quiet and verbose are exempt from
  // Cadical's state check, and only adding a clause leaves the configuring
  // state.
  const char* config = nullptr;
  switch (bias)
  {
    case SearchBias::SAT:
      config = "sat";
      break;
    case SearchBias::UNSAT:
      config = "unsat";
      break;
    case SearchBias::NONE:
      return true; // nothing to do, which counts as honouring the request.
  }

  return s->configure(config);
}

void Cadical::setVerbosity(int v)
{
  if (v ==0)
    {
      s->set("quiet",1);
      s->set("verbose",0);
    }
  else
    {
      s->set("quiet",0);
      s->set("verbose",1);
    }

}

bool Cadical::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->state() != CaDiCaL::State::UNSATISFIED; 
}

// Enabling factor commits every later clause and model lookup to the
// translation table (see the header): declared variables are the only ones
// factor's contract allows, and CaDiCaL places each declared range itself.
// Only ever called while the solver is still empty (CONFIGURING), which is
// the one state "factor" may be set in.
bool Cadical::enableBVAInternal()
{
#ifdef STP_CADICAL_HAS_FACTOR
  s->set("factor", 1);
  factor_enabled = true;
  return true;
#else
  // Building against a pre-3.0 CaDiCaL, where enabling factor was either
  // impossible or untested; solving is unaffected.
  return false;
#endif
}

// Incremental lazy backtracking, CaDiCaL's "ilb". Mode 1: on a new solve
// whose assumptions extend a prefix of the previous call's, CaDiCaL
// backtracks only to the first difference and keeps the shared trail,
// instead of re-deciding and re-propagating everything from the root -- and
// a call with no assumptions keeps nothing (sort_and_reuse_assumptions
// backtracks to the root outright). Mode 2 keeps the whole trail whether or
// not the call carries assumptions, so a clause added between calls unwinds
// it only as far as the level that falsifies the clause. The incremental
// driver asks for mode 1, measured equal to mode 2 on the many-small-queries
// workloads it targets, where every call carries assumptions; the batch
// pipeline's refinement loop asks for mode 2, because its calls carry none.
bool Cadical::enableTrailReuseInternal(TrailReuse scope)
{
  // Like factor, "ilb" may only be set while the solver is still in its
  // configuration window; the driver's size gate therefore works by
  // rebuilding onto a fresh solver rather than by toggling. A CaDiCaL whose
  // "ilb" is a plain switch (the 2.x line) declines the value 2, which the
  // caller reads as the hint being declined.
  return s->set("ilb", scope == TrailReuse::ALL ? 2 : 1);
}

bool Cadical::supportsInprobingControl() const
{
  return inprobing_control;
}

bool Cadical::disableInprobingInternal()
{
  // Configuration-window-only, like factor and ilb: the incremental
  // driver's retirement therefore rebuilds onto a fresh solver and
  // applies this there.
  return s->set("inprobing", 0);
}

bool Cadical::disableEliminationAndShrinkingInternal()
{
  const bool a = s->set("elim", 0);
  const bool b = s->set("shrink", 0);
  return a && b;
}

bool Cadical::disableLuckyPhasesInternal()
{
  return s->set("lucky", 0);
}

void Cadical::unsatAssumptions(const vec_literals& assumps,
                               std::vector<int>& out)
{
  // failed() answers per assumed literal, in CaDiCaL's external numbering
  // -- so the query literal travels through the factor translation exactly
  // as the assumption itself did.
  out.clear();
  for (int i = 0; i < assumps.size(); i++)
  {
    uint32_t var = assumps[i].x >> 1;
    uint32_t polarity = assumps[i].x & 1;
    if (factor_enabled)
      var = (uint32_t)ext_of_stp[var];
    if (s->failed(polarity ? -(int)var : (int)var))
      out.push_back(assumps[i].x);
  }
}

void Cadical::declarePendingVariables()
{
  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();
}

#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
void Cadical::refreshExternalInverse()
{
  if (!factor_enabled)
    return;
  for (uint32_t var = 1; var < ext_of_stp.size(); var++)
  {
    const size_t external = (size_t)ext_of_stp[var];
    if (stp_of_ext.size() <= external)
      stp_of_ext.resize(external + 1, 0);
    stp_of_ext[external] = var;
  }
}

int Cadical::externalLiteralOfStp(uint32_t literal) const
{
  uint32_t var = literal >> 1;
  if (factor_enabled)
  {
    assert(var < ext_of_stp.size() && "an untranslated variable in a theory "
                                      "clause: it was never declared");
    var = (uint32_t)ext_of_stp[var];
  }
  return (literal & 1) != 0 ? -(int)var : (int)var;
}

uint32_t Cadical::stpLiteralOfExternal(int literal) const
{
  uint32_t var = (uint32_t)std::abs(literal);
  if (factor_enabled)
  {
    assert(var < stp_of_ext.size() && stp_of_ext[var] != 0 &&
           "CaDiCaL notified an external variable STP never declared");
    var = stp_of_ext[var];
  }
  return 2 * var + (literal < 0 ? 1u : 0u);
}

Cadical::PropagatorBridge& Cadical::propagatorBridge()
{
  if (!bridge)
  {
    bridge.reset(new PropagatorBridge(*this));
    s->connect_external_propagator(bridge.get());
  }
  return *bridge;
}

bool Cadical::connectTheoryPropagator(TheoryPropagator* theory)
{
  if (theory == NULL)
    return false;
  // Declaring here rather than at the first observeVariable: declaring can
  // reset a model extension, and doing it once at connection keeps that out
  // of the middle of a batch of observations.
  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();
  refreshExternalInverse();
  propagatorBridge().setTheory(theory);
  return true;
}

void Cadical::disconnectTheoryPropagator()
{
  if (bridge)
    bridge->setTheory(NULL);
}

bool Cadical::observeVariable(uint32_t var)
{
  if (!bridge || var == 0 || var > next_variable)
    return false;
  // Unlike a decision hint this is allowed after a search has run: what
  // CaDiCaL requires is that the variable has not been eliminated, and a
  // variable minted for a lemma between two solve calls has not been. A
  // caller observing an older variable is asking for one inprocessing may
  // already have taken, which is why the UF propagator only ever observes
  // what its own round created.
  uint32_t external = var;
  if (factor_enabled)
  {
    if (ext_of_stp.size() <= next_variable)
      declareNewVariables();
    refreshExternalInverse();
    external = (uint32_t)ext_of_stp[var];
  }
  s->add_observed_var((int)external);
  return true;
}
#else
void Cadical::refreshExternalInverse() {}

int Cadical::externalLiteralOfStp(uint32_t literal) const
{
  const uint32_t var = literal >> 1;
  return (literal & 1) != 0 ? -(int)var : (int)var;
}

uint32_t Cadical::stpLiteralOfExternal(int literal) const
{
  return 2 * (uint32_t)std::abs(literal) + (literal < 0 ? 1u : 0u);
}

Cadical::PropagatorBridge& Cadical::propagatorBridge()
{
  if (!bridge)
    bridge.reset(new PropagatorBridge());
  return *bridge;
}

bool Cadical::connectTheoryPropagator(TheoryPropagator*)
{
  return false;
}

void Cadical::disconnectTheoryPropagator() {}

bool Cadical::observeVariable(uint32_t)
{
  return false;
}
#endif

bool Cadical::preferDecisions(const std::vector<DecisionHint>& wanted)
{
#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
  // Observing is only allowed on a variable inprocessing has not touched,
  // and only the first search is certain to find every variable untouched.
  if (searched || wanted.empty())
    return false;

  // As for a phase hint: the observed variable has to be the one the
  // clauses use, which under factor is the declared translation.
  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();

  PropagatorBridge& connected = propagatorBridge();
  refreshExternalInverse();
  for (const DecisionHint& h : wanted)
  {
    assert(h.var >= 1 && h.var <= next_variable);
    uint32_t var = h.var;
    if (factor_enabled)
      var = (uint32_t)ext_of_stp[var];
    s->add_observed_var((int)var);
    connected.hint(h.value ? (int)var : -(int)var);
  }
  return true;
#else
  // The propagator interface this relies on -- batched assignment
  // notification, observed variables -- is the 3.x shape.
  (void)wanted;
  return false;
#endif
}

void Cadical::suggestPhase(uint32_t var, bool value)
{
  // No declareNewVariables() here, deliberately. Declaring can reach
  // CaDiCaL's declare_more_variables, which leaves the SATISFIED state and
  // resets the extension -- too much for an advisory hint to do. Nothing is
  // lost: every literal worth phasing has had a clause added and is
  // therefore already declared, and one that has not is guarded below.
  if (factor_enabled)
  {
    if (var >= ext_of_stp.size())
      return; // never declared: nothing to phase.
    var = (uint32_t)ext_of_stp[var];
  }
  s->phase(value ? (int)var : -(int)var);
}

// With factor enabled, external variables must be declared before use, and
// CaDiCaL chooses where each declared range lives so that it never overlaps
// the extension variables factor invents. Declaration is batched here
// (lazily, before clauses are added) rather than done in newVar because
// declare_more_variables destroys a satisfying assignment, and newVar can
// be called while the refinement loop is still reading the model. Callers
// check that a range is actually pending so the usual up-to-date clause path
// does not enter this comparatively large routine.
void Cadical::declareNewVariables()
{
#ifdef STP_CADICAL_HAS_FACTOR
  assert(factor_enabled);
  assert(ext_of_stp.size() <= next_variable);
  if (ext_of_stp.empty())
    ext_of_stp.push_back(0); // dummy: variables are 1-based
  while (ext_of_stp.size() <= next_variable)
  {
    const size_t gap = next_variable + 1 - ext_of_stp.size();
    const int newmax = s->declare_more_variables((int)gap);
    for (size_t i = gap; i >= 1; i--)
      ext_of_stp.push_back(newmax - (int)i + 1);
  }
#endif
}

bool Cadical::addClauseInternal(
    const vec_literals& ps) // Add a clause to the solver.
{
  if (factor_enabled && ext_of_stp.size() <= next_variable)
    declareNewVariables();
  for (int i=0; i < ps.size(); i++)
    {
      uint32_t var = ps[i].x >> 1;
      uint32_t polarity = ps[i].x & 1;
      if (factor_enabled)
        var = (uint32_t)ext_of_stp[var];
      s->add(polarity? -(int)var : (int)var);
    }
  s->add(0);
  return false;
}

uint8_t Cadical::modelValue(uint32_t x) const
{
  if (factor_enabled)
    x = (x < ext_of_stp.size()) ? (uint32_t)ext_of_stp[x] : 0;
  if (x != 0 && s->val(x) > 0)
    return true_literal();
  else
    return false_literal();
}


} //end namespace stp

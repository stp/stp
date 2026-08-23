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
#include <limits>
using std::vector;

namespace stp
{
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

// Incremental lazy backtracking: on a new solve whose assumptions extend a
// prefix of the previous call's, CaDiCaL backtracks only to the first
// difference and keeps the shared trail, instead of re-deciding and
// re-propagating everything from the root. Mode 1 restricts the kept
// trail to the assumption prefix; measured equal to mode 2 on the
// many-small-queries workloads this targets.
bool Cadical::enableTrailReuseInternal()
{
  // Like factor, "ilb" may only be set while the solver is still in its
  // configuration window; the driver's size gate therefore works by
  // rebuilding onto a fresh solver rather than by toggling.
  return s->set("ilb", 1);
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

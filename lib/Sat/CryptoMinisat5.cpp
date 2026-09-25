/********************************************************************
 * AUTHORS: Mate Soos, Andrew Teylu
 *
 * BEGIN DATE: November, 2013
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

#include "stp/Sat/CryptoMinisat5.h"
#include "cryptominisat5/cryptominisat.h"
#include <unordered_set>
#include <algorithm>
#include <cstdlib>
using std::vector;

namespace stp
{

std::string CryptoMiniSat5::version()
{
  return CMSat::SATSolver::get_version();
}

void CryptoMiniSat5::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  if (enable)
  {
    s->set_no_simplify_at_startup();
  }
}

#ifdef STP_CRYPTOMINISAT_HAS_UP
/* The IPASIR-UP side of SATSolver::TheoryPropagator. CryptoMiniSat speaks
 * its own Lit, STP speaks var*2+sign; this is the only place the two meet.
 *
 * Nothing here may throw: these are called from inside the solver's search,
 * across a boundary that is not prepared to unwind. The theory reports
 * failure through failed() instead, and once it has, this stops asking it
 * anything and lets the solve finish so the caller can see the failure. */
class CryptoMiniSat5::PropagatorBridge final : public CMSat::ExternalPropagator
{
public:
  explicit PropagatorBridge(SATSolver::TheoryPropagator& theory)
      : theory(theory)
  {
    // The theory judges partial assignments as well as complete ones.
    is_lazy = false;
    // A reason the theory gives for a propagated literal is a fact of the
    // theory, not of the trail; the solver may drop it once it is done with
    // it, like any other learned clause.
    are_reasons_forgettable = true;
  }

  void reserveNotificationBuffer(size_t count) { translated.reserve(count); }

  void notify_assignment(const std::vector<CMSat::Lit>& lits) override
  {
    if (theory.failed())
      return;
    translated.clear();
    for (CMSat::Lit lit : lits)
      translated.push_back(fromCms(lit));
    if (!translated.empty())
      theory.notifyAssigned(translated);
  }
  void notify_new_decision_level() override
  {
    if (!theory.failed())
      theory.notifyNewLevel();
  }
  void notify_backtrack(size_t new_level) override
  {
    pending.clear();
    pending_index = 0;
    pending_active = false;
    if (!theory.failed())
      theory.notifyBacktrack(new_level);
  }
  bool cb_check_found_model(const std::vector<CMSat::Lit>& model) override
  {
    (void)model;
    // A failed theory cannot vouch for anything; the caller checks failed()
    // and discards the verdict, and saying true is what lets the solve end.
    if (theory.failed())
      return true;
    return theory.checkFoundModel();
  }
  bool cb_has_external_clause(bool& is_forgettable) override
  {
    // Every clause the theory hands over is a Farkas no-good: entailed by
    // the theory, not by the trail, so it stays true for the rest of the
    // solve and must not be forgotten.
    is_forgettable = false;
    if (pending_active)
      return true;
    if (theory.failed())
      return false;
    pending.clear();
    pending_index = 0;
    if (!theory.takeClause(pending) || pending.empty())
      return false;
    pending_active = true;
    return true;
  }
  CMSat::Lit cb_add_external_clause_lit() override
  {
    if (!pending_active)
      return CMSat::lit_Undef;
    if (pending_index == pending.size())
    {
      pending.clear();
      pending_index = 0;
      pending_active = false;
      return CMSat::lit_Undef; // terminator
    }
    return toCms(pending[pending_index++]);
  }
  CMSat::Lit cb_propagate() override
  {
    if (theory.failed())
      return CMSat::lit_Undef;
    SATSolver::Lit literal;
    if (!theory.propagate(literal))
      return CMSat::lit_Undef;
    return toCms(literal);
  }
  CMSat::Lit cb_add_reason_clause_lit(CMSat::Lit propagated_lit) override
  {
    // One reason at a time, literal by literal, the propagated literal
    // among them; the theory keeps the reason for every literal it hands
    // out, so a lookup here fails only once the theory has.
    if (!reason_active || !(reason_for == propagated_lit))
    {
      reason.clear();
      reason_index = 0;
      reason_for = propagated_lit;
      reason_active = false;
      if (theory.failed() ||
          !theory.reasonFor(fromCms(propagated_lit), reason))
      {
        reason.clear();
        return CMSat::lit_Undef;
      }
      reason_active = true;
    }
    if (reason_index == reason.size())
    {
      reason.clear();
      reason_index = 0;
      reason_active = false;
      return CMSat::lit_Undef; // terminator
    }
    return toCms(reason[reason_index++]);
  }

private:
  static SATSolver::Lit fromCms(CMSat::Lit lit)
  {
    SATSolver::Lit literal;
    literal.x = (lit.var() << 1) | (lit.sign() ? 1u : 0u);
    return literal;
  }
  static CMSat::Lit toCms(SATSolver::Lit literal)
  {
    return CMSat::Lit(literal.x >> 1, (literal.x & 1u) != 0);
  }

  SATSolver::TheoryPropagator& theory;
  std::vector<SATSolver::Lit> pending;   // clause being handed over
  size_t pending_index = 0;
  bool pending_active = false;
  std::vector<SATSolver::Lit> reason;    // reason clause being handed over
  size_t reason_index = 0;
  bool reason_active = false;
  CMSat::Lit reason_for = CMSat::lit_Undef;
  // Reused across notifications: this runs on every assignment of an
  // observed variable, and must not allocate on that path.
  std::vector<SATSolver::Lit> translated;
};

bool CryptoMiniSat5::connectTheoryPropagator(
    SATSolver::TheoryPropagator* propagator,
    const std::vector<uint32_t>& observed)
{
  if (propagator == nullptr || propagator_bridge || num_threads != 1)
    return false;
  propagator_bridge.reset(new PropagatorBridge(*propagator));
  propagator_bridge->reserveNotificationBuffer(observed.size());
  s->connect_external_propagator(propagator_bridge.get());
  // Observing freezes the variable, so simplification will not eliminate
  // or replace an atom the theory is reasoning about.
  for (uint32_t var : observed)
    s->add_observed_var(var);
  return true;
}

void CryptoMiniSat5::disconnectTheoryPropagator()
{
  if (!propagator_bridge)
    return;
  s->disconnect_external_propagator(); // also un-observes every variable
  propagator_bridge.reset();
}

void CryptoMiniSat5::expectTheoryPropagator()
{
  // A variable replaced by an equivalent literal can no longer be observed,
  // and the propagator connects only after the first solve has simplified.
  s->set_no_equivalent_lit_replacement();
}
#endif

CryptoMiniSat5::CryptoMiniSat5(int num_threads)
#ifdef STP_CRYPTOMINISAT_HAS_UP
    : num_threads(num_threads)
#endif
{
  s = new CMSat::SATSolver;
  // s->log_to_file("stp.cnf");
  s->set_num_threads(num_threads);
  //s->set_default_polarity(false);
  //s->set_allow_otf_gauss();
  temp_cl = (void*)new vector<CMSat::Lit>;
}

CryptoMiniSat5::~CryptoMiniSat5()
{
#ifdef STP_CRYPTOMINISAT_HAS_UP
  disconnectTheoryPropagator();
#endif
  delete s;
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void CryptoMiniSat5::setMaxConflicts(int64_t _max_confl)
{
  assert(_max_confl >= 0);
  max_confl = _max_confl;

  // The budget belongs to the query being armed for, so measure it from
  // this point rather than from the solver's birth -- Minisat's
  // setConfBudget does exactly this (conflicts + x). It made no difference
  // while every query got a fresh solver; the incremental driver re-arms
  // per check-sat on one long-lived solver, where counting from birth made
  // each successive budget smaller until every solve gave up on arrival.
  confl_base = s->get_sum_conflicts();
}

bool CryptoMiniSat5::addClauseInternal(
    const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  real_temp_cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    real_temp_cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
  }

  return s->add_clause(real_temp_cl);
}

void CryptoMiniSat5::unsatAssumptions(const vec_literals& assumps,
                                      std::vector<int>& out)
{
  // As in MiniSat, get_conflict() is the final conflict clause expressed over
  // the assumptions, so it holds the NEGATION of each one the refutation
  // used. An assumption is in the core iff its negation appears there.
  const std::vector<CMSat::Lit>& conflict = s->get_conflict();

  out.clear();
  for (int i = 0; i < assumps.size(); i++)
  {
    const CMSat::Lit assumed(var(assumps[i]), sign(assumps[i]));
    if (std::find(conflict.begin(), conflict.end(), ~assumed) != conflict.end())
      out.push_back(assumps[i].x);
  }
}

bool CryptoMiniSat5::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

// Arm what is left of the query's conflict/time budgets before a solve call;
// FALSE means a budget is already spent and the caller should give up now.
bool CryptoMiniSat5::armBudgets(bool& timeout_expired)
{
  /*
   * The conflict budget is for the query, so what is handed over is what is
   * left of it. Once it is gone we give up here rather than passing a budget
   * of zero down and relying on how CryptoMiniSat reads it.
   */
  if (max_confl >= 0) {
     const int64_t spent =
         static_cast<int64_t>(s->get_sum_conflicts() - confl_base);
     const int64_t remaining = max_confl - spent;

     if (remaining <= 0) {
        timeout_expired = true;
        return false;
     }

     s->set_max_confl(static_cast<uint64_t>(remaining));
  }

  /*
   * The budget belongs to the query rather than to this call, so hand over
   * what is left of it rather than the original figure. SATSolver::solve()
   * has already turned away a query whose deadline is in the past, but the
   * clock moves on between that check and this one, and secondsRemaining()
   * clamps a negative remainder to zero: give up here rather than handing a
   * zero down and relying on how CryptoMiniSat reads it, exactly as the
   * conflict budget above does.
   */
  if (hasTimeLimit()) {
     const double remaining = secondsRemaining();

     if (remaining <= 0.0) {
        timeout_expired = true;
        return false;
     }

     s->set_max_time(remaining);
  }

  return true;
}

bool CryptoMiniSat5::solveInternal(bool& timeout_expired)
{
  if (!armBudgets(timeout_expired))
    return false;

  CMSat::lbool ret = s->solve();
  if (ret == CMSat::l_Undef)
  {
    timeout_expired = true;
  }
  return ret == CMSat::l_True;
}

bool CryptoMiniSat5::solveWithAssumptionsInternal(
    const stp::SATSolver::vec_literals& assumps, bool& timeout_expired)
{
  if (!armBudgets(timeout_expired))
    return false;

  // Cryptominisat uses its own vec and Lit classes, as in addClause.
  std::vector<CMSat::Lit> real_assumps;
  real_assumps.reserve(assumps.size());
  for (int i = 0; i < assumps.size(); i++)
    real_assumps.push_back(CMSat::Lit(var(assumps[i]), sign(assumps[i])));

  CMSat::lbool ret = s->solve(&real_assumps);
  if (ret == CMSat::l_Undef)
  {
    timeout_expired = true;
  }
  return ret == CMSat::l_True;
}

uint8_t CryptoMiniSat5::modelValue(uint32_t x) const
{
  // The three values SATSolver promises. This used to answer 0 or 1, which
  // made every false variable read as undef_literal() (also 0) to callers
  // that distinguish an unassigned variable from an assigned false value.
  const std::vector<CMSat::lbool>& model = s->get_model();
  if (x >= model.size())
    return undef_literal();
  if (model[x] == CMSat::l_True)
    return true_literal();
  if (model[x] == CMSat::l_False)
    return false_literal();
  return undef_literal();
}

uint32_t CryptoMiniSat5::newVar()
{
  s->new_var();
  return s->nVars() - 1;
}

bool CryptoMiniSat5::setSearchBiasInternal(SearchBias bias)
{
  // CryptoMiniSat has no named configurations, so what it offers has to be
  // picked out by hand. Turning off SLS is the piece that carries over: it is
  // the local-search phase, it looks for models, and it is wasted work when
  // there isn't one. On the QF_BV/20230221-oisc-gurtner family it came out
  // ahead on all 18 interleaved A/B pairs measured, by 12% of wall clock at
  // the median.
  //
  // Its other half-analogue was measured and rejected. CryptoMiniSat rotates
  // its polarity strategy over {best, stable, best_inv, saved} as the search
  // restarts, which looks like the stabilising mode that other solvers turn
  // off for unsatisfiable instances -- but pinning the rotation to plain
  // phase saving was *slower* on 8 of 9 of the same pairs, by 10-49%, so the
  // rotation is evidently earning its keep here whatever the answer turns out
  // to be. Its restart strategy is not reachable through the public API, so
  // the stabilising side of the bias is simply left alone.
  //
  // Nothing is done for SAT: the defaults are already the satisfiable-leaning
  // end of what is on offer, so say so rather than pretend to have applied
  // something.
  if (bias == SearchBias::NONE)
    return true;

  if (bias == SearchBias::SAT)
    return false;

  s->set_sls(0);
  return true;
}

void CryptoMiniSat5::setVerbosity(int v)
{
  s->set_verbosity(v);
}

uint32_t CryptoMiniSat5::nVars() const
{
  return s->nVars();
}

void CryptoMiniSat5::printStats() const
{
  // s->printStats();
}


// Count how many literals/bits get fixed subject to the assumptions. Sets
// `conflict` when unit propagation refutes them instead, in which case the
// return value carries no information.
uint32_t CryptoMiniSat5::getFixedCountWithAssumptions(const stp::SATSolver::vec_literals& assumps, const std::unordered_set<unsigned>& literals, bool& conflict )
{
  [[maybe_unused]] const uint64_t conf = s->get_sum_conflicts();
  assert(conf == 0);


  // Bounded variable elimination would remove variables this count is about
  // to look for, so a bit that is implied but whose variable was eliminated
  // reads as not deduced. The caller wants what unit propagation derives over
  // the encoding it asked for, not over whatever CMS rewrote it into.
  s->set_no_bve();

  bool bad = (CMSat::l_False == s->simplify());


  // Add the assumptions are clauses. add_clause() propagates a unit at level
  // zero as it adds it, so a false return is unit propagation deriving the
  // empty clause -- the conflict this is asked to report. Once that has
  // happened every later add_clause() returns false too, which is harmless.
  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  for (int i = 0; i < assumps.size(); i++)
  {
    real_temp_cl.clear();
    real_temp_cl.push_back(CMSat::Lit(var(assumps[i]), sign(assumps[i])));
    if (!s->add_clause(real_temp_cl))
      bad = true;
  }

  conflict = bad;
  if (bad)
    return 0; // nothing meaningful to count in an unsatisfiable solver


  //std::cerr << assumps.size() << " assumptions" << std::endl;

  uint32_t assigned = 0;
  std::vector<CMSat::Lit> zero = s->get_zero_assigned_lits();
  for (CMSat::Lit l : zero)
  {
      if (literals.find(l.var()) != literals.end())
        assigned++;
  }
 
 
       
  //std::cerr << assigned << " assignments at end" <<std::endl;

  // The assumptions are each single literals (corresponding to bits) that are true/false. 
  // so in the result they should be all be set
  assert(assigned >= static_cast<uint32_t>(assumps.size()));
  assert(s->get_sum_conflicts() == conf ); // no searching, so no conflicts.

  return assigned;
}



} //end namespace stp

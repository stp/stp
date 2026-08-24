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

CryptoMiniSat5::CryptoMiniSat5(int num_threads)
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
  return (s->get_model().at(x) == CMSat::l_True);
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

void CryptoMiniSat5::solveAndDump()
  {
     bool t;
     solve(t);
     s->open_file_and_dump_irred_clauses("clauses.txt");
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

/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew Teylu
 *
 * BEGIN DATE: Aug, 2010
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

#ifndef SATSOLVER_H_
#define SATSOLVER_H_

#include "SearchBias.h"
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

namespace stp
{
class SATSolver
{
private:
  SATSolver(const SATSolver&);      // no copy
  void operator=(const SATSolver&); // no assign.

public:
  SATSolver() {}

  virtual ~SATSolver() {}

  // A literal: a variable index and a sign, packed as variable*2 + sign
  // (sign set means negated). This is STP's own encoding; each backend
  // translates it into its solver's literal type in addClause.
  struct Lit
  {
    uint32_t x;
  };

  class vec_literals
  {
    std::vector<Lit> lits;

  public:
    int size() const { return static_cast<int>(lits.size()); }
    void push(Lit l) { lits.push_back(l); }
    // Drop the last literal. Retraction is why this exists: an assumption
    // installed for one solve and withdrawn for the next is pushed last, so
    // withdrawing it is a pop rather than a search.
    void pop() { lits.pop_back(); }
    void clear() { lits.clear(); }
    Lit operator[](int i) const { return lits[static_cast<size_t>(i)]; }
  };

  // Add a clause to the solver and count the submission at the common API
  // boundary. Backend-reported clause counts are not suitable for persistent
  // accounting: preprocessing may remove input clauses, and some backends do
  // not expose a count at all. This monotone counter instead records exactly
  // what STP has handed to the current backend instance, including a clause
  // whose submission discovers that the formula is already inconsistent.
  bool addClause(const SATSolver::vec_literals& ps)
  {
    submitted_clauses++;
    return addClauseInternal(ps);
  }

  uint64_t submittedClauses() const { return submitted_clauses; }

  // Whether this backend will still accept configuration. The window closes
  // at the first clause; a caller that must decide about a LIVE solver and
  // apply the choice to the fresh one a rebuild constructs can ask instead
  // of relying on knowing where it is in the sequence.
  bool configurationOpen() const { return submitted_clauses == 0; }

  virtual bool okay() const = 0; // FALSE means solver is in a conflicting state

  // Search without assumptions.
  //
  // Not virtual: this enforces the parts of the resource budget that do not
  // depend on the backend, then delegates to solveInternal(). Backends
  // override solveInternal(), not this.
  bool solve(bool& timeout_expired)
  {
    // The budget can already be spent before we ever reach the solver, either
    // because the caller asked for a zero budget or because an earlier
    // refinement iteration used it all up. Don't rely on the backend noticing:
    // a solver that cannot be interrupted mid-search would run to completion,
    // and even one that can only notices when it next polls.
    if (timeLimitExpired())
    {
      timeout_expired = true;
      return false;
    }

    return solveInternal(timeout_expired);
  }

  // Search under assumption literals: each is treated as a unit clause for
  // this call only, and leaves no trace afterwards. This is what makes the
  // solver reusable across (check-sat) calls -- retractable assertions are
  // assumed rather than added. Budget enforcement as in solve().
  //
  // Only meaningful when supportsAssumptions(); the incremental driver
  // selects a backend on that basis.
  bool solveWithAssumptions(const vec_literals& assumps, bool& timeout_expired)
  {
    if (timeLimitExpired())
    {
      timeout_expired = true;
      return false;
    }

    return solveWithAssumptionsInternal(assumps, timeout_expired);
  }

  virtual bool supportsAssumptions() const { return false; }

  typedef uint8_t lbool;

  static inline Lit mkLit(uint32_t var, bool sign)
  {
    Lit p;
    p.x = var + var + (uint32_t)sign;
    return p;
  }

  static inline uint32_t var(Lit p) { return p.x >> 1; }
  static inline bool sign(Lit p) { return (p.x & 1) != 0; }
  static inline int toInt(Lit p) { return (int)p.x; }

  // Ask the backend to tune its search towards satisfiable or unsatisfiable
  // instances. Only ever called before the first clause is added, because a
  // backend may only accept configuration while it is still empty.
  //
  // FALSE means this backend has nothing corresponding to the requested bias.
  // That isn't an error: the bias is a hint about the workload, and a backend
  // that ignores it is slower rather than wrong.
  bool setSearchBias(SearchBias bias)
  {
    assertConfigurable("setSearchBias");
    return setSearchBiasInternal(bias);
  }

  // Ask the backend to turn on bounded variable addition (BVA, CaDiCaL's
  // "factor"). Like setSearchBias this is only ever called before the first
  // clause is added, and FALSE means the backend has no such technique to
  // enable -- a performance hint declined, not an error.
  bool enableBVA()
  {
    assertConfigurable("enableBVA");
    return enableBVAInternal();
  }

  // Ask the backend to reuse the solver trail across incremental solve
  // calls when consecutive assumption sequences share a prefix, instead of
  // re-deciding and re-propagating from the root every call (CaDiCaL's
  // incremental lazy backtracking). Only correct to rely on when the
  // caller keeps its assumption order prefix-stable across calls, which
  // the incremental driver does: assumptions are emitted in assertion
  // stack order and push/pop only ever change the suffix. FALSE means the
  // backend has no such mechanism -- a performance hint declined, not an
  // error.
  bool enableTrailReuse()
  {
    assertConfigurable("enableTrailReuse");
    return enableTrailReuseInternal();
  }

  // Whether this backend can turn probe-based inprocessing off, and the
  // switch itself. disableInprobing() is only ever called before the
  // first clause is added (backends may only accept configuration while
  // empty); the capability query is free of that restriction, so a
  // caller can decide about a LIVE solver and apply the choice to the
  // fresh one a rebuild constructs. FALSE from the query means the
  // backend has no such technique to control -- a performance hint
  // declined, not an error.
  virtual bool supportsInprobingControl() const { return false; }
  bool disableInprobing()
  {
    assertConfigurable("disableInprobing");
    return disableInprobingInternal();
  }

  // The rest of the recurring-inprocessing retirement, applied alongside
  // disableInprobing under the same configuration-window rule: bounded
  // variable elimination re-eliminates restored variables every solve on
  // a persistent solver whose content churns (retractable encodings
  // mention eliminated variables and CaDiCaL restores them on contact),
  // and learned-clause shrinking taxes every conflict of a many-solve
  // session. Both measured as steady per-solve losses on the sessions
  // that retire inprobing, and their removal composes with it.
  bool disableEliminationAndShrinking()
  {
    assertConfigurable("disableEliminationAndShrinking");
    return disableEliminationAndShrinkingInternal();
  }

  // Turn off the backend's lucky-phase probing, which re-tries trivial
  // whole-assignment patterns over the entire clause database at every
  // solve call. Worth its price once per formula; on a persistent
  // many-solve solver it is a recurring tax. Configuration-window-only,
  // like the rest; FALSE means nothing to turn off.
  bool disableLuckyPhases()
  {
    assertConfigurable("disableLuckyPhases");
    return disableLuckyPhasesInternal();
  }

  // After solveWithAssumptions returned false: the subset of the assumed
  // literals that the refutation actually used, in the same 2*var+sign
  // encoding they were passed in. Any superset of a genuine core is a
  // correct answer -- the full assumption set always is one, and that is
  // the default for backends without the query. Only meaningful
  // immediately after an unsatisfiable assumption solve, before anything
  // else touches the solver.
  virtual void unsatAssumptions(const vec_literals& assumps,
                                std::vector<int>& out)
  {
    out.clear();
    for (int i = 0; i < assumps.size(); i++)
      out.push_back(assumps[i].x);
  }

  // Run whatever simplification the backend can do without being asked to
  // decide anything, so that what it derives at the root becomes visible to
  // rootFixed() below. A backend with nothing to offer leaves the formula
  // alone, which is always a correct answer to this.
  // Returns 20 when the backend settled the formula unsatisfiable while
  // simplifying, 10 when it settled it satisfiable, and 0 when it did not
  // settle it -- which is also what a backend with nothing to offer says.
  virtual int simplifyOnly() { return 0; }

  // What the backend has established about a variable at the root, after
  // simplifyOnly(): 1 if it is fixed true, -1 if fixed false, 0 if it is
  // not fixed or the backend cannot say. Zero is always a sound answer --
  // the caller may only use a non-zero one to learn something, never the
  // absence of one to conclude anything.
  virtual int rootFixed(unsigned /*var*/) { return 0; }

  // Suggest the value the decision heuristic should try first for a
  // variable. Pure search advice: it cannot change any verdict, only
  // which model is found first. The incremental driver uses it to steer
  // the search away from retracted content -- a popped level's
  // activation variable is unconstrained, and a backend whose default
  // phase is positive would otherwise keep dragging the dead level's
  // cone into the search. Backends without a cheap phase interface
  // ignore it.
  virtual void suggestPhase(uint32_t var, bool value)
  {
    (void)var;
    (void)value;
  }

  // Bring every variable created so far to the backend's attention.
  //
  // A backend may declare variables lazily -- CaDiCaL's factoring layer
  // declares on a clause, an assumption, or at the start of a solve -- which
  // leaves a variable that no clause mentions unknown to it, and an advisory
  // phase for such a variable is dropped. suggestPhase deliberately does not
  // declare, because declaring can reset a model extension and that is too
  // much for a hint to do; a caller that knows it is between construction and
  // the first solve can ask for it explicitly here instead.
  virtual void declarePendingVariables() {}

  // ---------------------------------------------------------------------
  // Resource budgets.
  //
  // STP spells "no limit" as -1, and that case is filtered out by the
  // caller, so these are only ever called with a value >= 0. A value of 0
  // therefore means what it says: a budget of zero, i.e. give up without
  // searching. It does not mean "unlimited".
  // ---------------------------------------------------------------------

  virtual void setMaxConflicts(int64_t /*max_confl*/)
  {
    std::cerr
        << "Warning: Max conflict setting is not supported by this SAT solver"
        << std::endl;
  }

  // The time budget belongs to the whole query, not to one solve() call.
  // STP calls solve() once per abstraction-refinement iteration, so a budget
  // re-armed per call would let a query run for an unbounded multiple of it.
  // The deadline is computed once, here, and every backend measures against
  // it; that also makes a budget of 0 fall out for free, as a deadline in the
  // past.
  //
  // Backends that can be interrupted mid-search should override
  // canInterruptSearch() and consult secondsRemaining() / timeLimitExpired().
  // For the rest, solve() still enforces the deadline between calls.
  virtual void setMaxTime(int64_t max_time) // seconds
  {
    assert(max_time >= 0);

    deadline = std::chrono::steady_clock::now() +
               std::chrono::seconds(max_time);
    deadline_set = true;

    if (!canInterruptSearch())
    {
      std::cerr << "Warning: this SAT solver cannot be interrupted during "
                   "search; the time limit is only enforced between solver "
                   "calls"
                << std::endl;
    }
  }

  bool hasTimeLimit() const { return deadline_set; }

  // TRUE once the query's time budget is gone. Always FALSE when no time
  // limit has been set.
  bool timeLimitExpired() const
  {
    return deadline_set && std::chrono::steady_clock::now() >= deadline;
  }

  // Time left on the query's budget, in seconds; never negative. Only
  // meaningful when hasTimeLimit(). Backends that take a duration rather
  // than a deadline should pass this on each solve, so that what remains
  // shrinks across refinement iterations instead of being re-armed.
  double secondsRemaining() const
  {
    assert(deadline_set);

    const std::chrono::duration<double> remaining =
        deadline - std::chrono::steady_clock::now();

    return remaining.count() > 0.0 ? remaining.count() : 0.0;
  }

  virtual uint8_t modelValue(uint32_t x) const = 0;

  virtual uint32_t newVar() = 0;

  virtual uint32_t nVars() const = 0;

  virtual void printStats() const = 0;

  virtual void setVerbosity(int v) = 0;

  virtual lbool true_literal() const = 0;
  virtual lbool false_literal() const = 0;
  virtual lbool undef_literal() const = 0;

  // The simplifying solvers shouldn't eliminate index / value variables.
  virtual void setFrozen(uint32_t /*var*/) {}

  virtual void enableRefinement(const bool /*enable*/) {}

  // TRUE when nClauses() is implemented, i.e. the backend can report how
  // many clauses it currently holds (after simplify(), the post-propagation
  // count). Callers with a fallback should ask this before calling it.
  virtual bool reportsClauseCount() const { return false; }

  virtual int nClauses()
  {
    std::cerr << "Not yet implemented.";
    exit(1);
  }

  virtual bool simplify()
  {
    std::cerr << "Not yet implemented.";
    exit(1);
  }

protected:
  // Backends may only accept configuration while they are still empty --
  // CaDiCaL closes its option window at the first clause and answers a late
  // setter by aborting the process. This header stated that rule in prose
  // beside five separate methods and checked it nowhere; a rebuild that
  // configured in the wrong order would have died inside a third-party
  // library with no STP frame to name the caller. submitted_clauses is
  // already exactly the latch -- it counts what STP handed THIS backend
  // instance, and a rebuild constructs a fresh one -- so the window needs no
  // state of its own, only asking.
  void assertConfigurable(const char* what) const
  {
    (void)what;
    assert(submitted_clauses == 0 &&
           "backend configured after its first clause: the configuration "
           "window closes there");
  }

  // Backend-specific configuration. Callers use the non-virtual facades
  // above, which check the window first. FALSE means the backend has no such
  // technique -- a performance hint declined, not an error.
  virtual bool setSearchBiasInternal(SearchBias /*bias*/) { return false; }
  virtual bool enableBVAInternal() { return false; }
  virtual bool enableTrailReuseInternal() { return false; }
  virtual bool disableInprobingInternal() { return false; }
  virtual bool disableEliminationAndShrinkingInternal() { return false; }
  virtual bool disableLuckyPhasesInternal() { return false; }

  // Backend-specific clause translation. Callers use addClause(), whose
  // non-virtual facade keeps submission accounting complete for every path,
  // including theory refinement code that only sees SATSolver&.
  virtual bool addClauseInternal(const vec_literals& ps) = 0;

  // Search without assumptions, having already been given a non-empty share
  // of whatever budget was configured. Implemented by each backend.
  virtual bool solveInternal(bool& timeout_expired) = 0;

  // Search under assumptions. Backends that return true from
  // supportsAssumptions() override this; the default must be unreachable.
  virtual bool solveWithAssumptionsInternal(const vec_literals& /*assumps*/,
                                            bool& /*timeout_expired*/)
  {
    std::cerr << "ERROR: this SAT backend does not support assumptions"
              << std::endl;
    exit(-1);
  }

  // TRUE if the backend can abandon a search that is already running, either
  // through a callback or through a limit of its own. Backends that cannot
  // get a time limit enforced only between solve() calls.
  virtual bool canInterruptSearch() const { return false; }

private:
  uint64_t submitted_clauses = 0;
  std::chrono::steady_clock::time_point deadline;
  bool deadline_set = false;
};
}
#endif

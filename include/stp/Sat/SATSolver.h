/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew V. Jones
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

#include "minisat/core/SolverTypes.h"
#include "minisat/mtl/Vec.h"
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>

// Don't let the defines escape outside.

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

  class vec_literals : public Minisat::vec<Minisat::Lit>
  {
  };

  virtual bool addClause(
      const SATSolver::vec_literals& ps) = 0; // Add a clause to the solver.

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

  typedef uint8_t lbool;

  static inline Minisat::Lit mkLit(uint32_t var, bool sign)
  {
    Minisat::Lit p;
    p.x = var + var + (int)sign;
    return p;
  }

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

  virtual unsigned long nVars() const = 0;

  virtual void printStats() const = 0;

  virtual void setVerbosity(int v) = 0;

  virtual lbool true_literal() const = 0;
  virtual lbool false_literal() const = 0;
  virtual lbool undef_literal() const = 0;

  // The simplifying solvers shouldn't eliminate index / value variables.
  virtual void setFrozen(uint32_t /*var*/) {}

  virtual void enableRefinement(const bool /*enable*/) {}

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
  // Search without assumptions, having already been given a non-empty share
  // of whatever budget was configured. Implemented by each backend.
  virtual bool solveInternal(bool& timeout_expired) = 0;

  // TRUE if the backend can abandon a search that is already running, either
  // through a callback or through a limit of its own. Backends that cannot
  // get a time limit enforced only between solve() calls.
  virtual bool canInterruptSearch() const { return false; }

private:
  std::chrono::steady_clock::time_point deadline;
  bool deadline_set = false;
};
}
#endif

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

/*
 * Wraps around Cadical
 */

#ifndef CADICAL_H_
#define CADICAL_H_

#include "SATSolver.h"
#include "src/cadical.hpp"
#include <chrono>

namespace stp
{
#if defined(__GNUC__) || defined(__clang__)
  class __attribute__((visibility("default"))) Cadical : public SATSolver
#else
  class Cadical : public SATSolver
#endif
{
  uint32_t next_variable = 0;
  CaDiCaL::Solver * s;

  // Cadical has no wall-clock limit of its own; it polls a Terminator
  // during search, so asking the base class whether the query's deadline
  // has passed is what gives us setMaxTime(). The deadline lives in
  // SATSolver and spans the whole query, so this is not re-armed per solve.
  class TimeLimit : public CaDiCaL::Terminator
  {
  public:
    TimeLimit(const SATSolver& owner) : owner(owner) {}
    bool terminate() override { return owner.timeLimitExpired(); }

  private:
    const SATSolver& owner;
  };
  TimeLimit time_limit;

  int64_t max_confl = -1;

public:
  Cadical();

  ~Cadical();

  bool addClause(const vec_literals& ps) override; // Add a clause to the solver.

  bool okay() const override; // FALSE means solver is in a conflicting state

  void setMaxConflicts(int64_t max_confl) override; // set max solver conflicts

  bool simplify() override; // Removes already satisfied clauses.

  uint8_t modelValue(uint32_t x) const override;

  uint32_t newVar() override;

  void setVerbosity(int v) override;

  unsigned long nVars() const override;

  void printStats() const override;

  lbool true_literal() const override { return ((uint8_t)1); }
  lbool false_literal() const override { return ((uint8_t)-1); }
  lbool undef_literal() const override { return ((uint8_t)2); }

protected:
  bool solveInternal(bool& timeout_expired) override;

  // Cadical polls the Terminator we connect during search.
  bool canInterruptSearch() const override { return true; }
};
}

#endif

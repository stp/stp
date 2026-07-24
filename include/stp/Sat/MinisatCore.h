/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
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
 * Wraps around CORE minisat.
 */

#ifndef MINISATCORE_H_
#define MINISATCORE_H_

#include "SATSolver.h"

namespace Minisat
{
class Solver;
}

namespace stp
{
#if defined(__GNUC__) || defined(__clang__)
  class __attribute__((visibility("default"))) MinisatCore : public SATSolver
#else
  class MinisatCore : public SATSolver
#endif


{
  Minisat::Solver* s;

public:
  MinisatCore();

  ~MinisatCore();

  bool addClause(const vec_literals& ps) override; // Add a clause to the solver.

  bool okay() const override; // FALSE means solver is in a conflicting state

  bool propagateWithAssumptions(const stp::SATSolver::vec_literals& assumps);

  void setMaxConflicts(int64_t max_confl) override;

  bool simplify() override; // Removes already satisfied clauses.

  uint8_t modelValue(uint32_t x) const override;

  uint8_t value(uint32_t x) const;

  uint32_t newVar() override;

  void setVerbosity(int v) override;

  unsigned long nVars() const override;

  void printStats() const override;

  lbool true_literal() const override { return ((uint8_t)0); }
  lbool false_literal() const override { return ((uint8_t)1); }
  lbool undef_literal() const override { return ((uint8_t)2); }

  int nClauses() override;

  //bool unitPropagate(const vec_literals& ps);

protected:
  bool solveInternal(bool& timeout_expired) override;
};
}

#endif

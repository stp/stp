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

#include <memory>

namespace Minisat
{
class Solver;
class Terminator;
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

  // Polled by MiniSat wherever its own budgets are, so that the deadline
  // SATSolver already owns can stop a search in progress. Held by pointer
  // because MiniSat's header is not included here.
  std::unique_ptr<Minisat::Terminator> deadline_terminator;

public:
  MinisatCore();

  ~MinisatCore();



  bool okay() const override; // FALSE means solver is in a conflicting state

  void unsatAssumptions(const vec_literals& assumps,
                        std::vector<int>& out) override;

  void setMaxConflicts(int64_t max_confl) override;

  bool simplify() override; // Removes already satisfied clauses.

  uint8_t modelValue(uint32_t x) const override;

  uint8_t value(uint32_t x) const;

  uint32_t newVar() override;

  void setVerbosity(int v) override;

  uint32_t nVars() const override;

  void printStats() const override;

  lbool true_literal() const override { return ((uint8_t)0); }
  lbool false_literal() const override { return ((uint8_t)1); }
  lbool undef_literal() const override { return ((uint8_t)2); }

  bool reportsClauseCount() const override { return true; }

  int nClauses() override;

  //bool unitPropagate(const vec_literals& ps);

  bool supportsAssumptions() const override { return true; }

protected:
  // MiniSat counts work, not time, so it cannot be handed a deadline the way
  // CryptoMiniSat can. It can be asked to stop, though, which is enough: the
  // terminator connected in the constructor reads the budget the base class is
  // already keeping, and MiniSat polls it on every conflict and every restart.
  bool canInterruptSearch() const override { return true; }

  bool addClauseInternal(const vec_literals& ps) override;
  bool solveInternal(bool& timeout_expired) override;
  bool solveWithAssumptionsInternal(const vec_literals& assumps,
                                    bool& timeout_expired) override;
};
}

#endif

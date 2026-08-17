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

/*
 * Wraps around Cryptominisat minisat.
 */
#ifndef CRYPTOMINISAT5_H_
#define CRYPTOMINISAT5_H_

#include "stp/Sat/SATSolver.h"
#include <unordered_set>

namespace CMSat
{
class SATSolver;
}

namespace stp
{
#if defined(__GNUC__) || defined(__clang__)
  class __attribute__((visibility("default"))) CryptoMiniSat5 : public SATSolver
#else
  class CryptoMiniSat5 : public SATSolver
#endif

{
  CMSat::SATSolver* s;

public:
  CryptoMiniSat5(int num_threads);

  ~CryptoMiniSat5();

  void setMaxConflicts(int64_t max_confl) override; // set max solver conflicts

  bool okay() const override; // FALSE means solver is in a conflicting state

  void unsatAssumptions(const vec_literals& assumps,
                        std::vector<int>& out) override;

  uint8_t modelValue(uint32_t x) const override;

  uint32_t newVar() override;

  bool setSearchBiasInternal(SearchBias bias) override;

  void setVerbosity(int v) override;

  uint32_t nVars() const override;

  void printStats() const override;

  void enableRefinement(const bool enable) override;

  // nb CryptoMiniSat has different literal values to the other minisats.
  lbool true_literal() const override { return ((uint8_t)1); }
  lbool false_literal() const override { return ((uint8_t)-1); }
  lbool undef_literal() const override { return ((uint8_t)0); }

  uint32_t getFixedCountWithAssumptions(const stp::SATSolver::vec_literals& assumps,  const std::unordered_set<unsigned>& literals, bool& conflict );


  void solveAndDump();

  bool supportsAssumptions() const override { return true; }

protected:
  bool addClauseInternal(const vec_literals& ps) override;
  bool solveInternal(bool& timeout_expired) override;
  bool solveWithAssumptionsInternal(const vec_literals& assumps,
                                    bool& timeout_expired) override;

  // CryptoMiniSat polls its own wall-clock limit during search.
  bool canInterruptSearch() const override { return true; }

private:
  bool armBudgets(bool& timeout_expired);

  void* temp_cl;
  // Negative means no budget was configured. This cannot default to 0,
  // which is now a budget of zero rather than the absence of one.
  int64_t max_confl = -1;
  // The solver's lifetime conflict count when the budget was last armed;
  // what the budget's query has spent is measured from here.
  uint64_t confl_base = 0;
};
}

#endif

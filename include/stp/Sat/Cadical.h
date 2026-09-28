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
#include "CadicalOptions.h"
#include <cadical/cadical.hpp>
#include <chrono>
#include <memory>
#include <vector>

// STP_CADICAL_HAS_FACTOR is decided by the configure, from the version of the
// CaDiCaL it located; the header that actually arrives here is decided by the
// include path. Those are two different answers to the same question, and they
// have disagreed: CryptoMiniSat >= 5.14 installs a bundled CaDiCaL's header
// under the same cadical/cadical.hpp, and once its prefix was on the search
// path ahead of STP's, the 2.1.3 header was compiled against a build that had
// read 3.0.1 off the checkout. lib/Sat/CMakeLists.txt keeps that from
// happening; this says so if it ever does again, rather than leaving it to
// surface as a missing member several hundred lines away -- or, for an API
// that happens to line up in both, not surfacing at all.
#if defined(STP_CADICAL_HAS_FACTOR) && \
    (!defined(CADICAL_MAJOR) || CADICAL_MAJOR < 3)
#error "cadical/cadical.hpp is older than the CaDiCaL this build configured \
against. Some other dependency's include directory is shadowing it -- see the \
CryptoMiniSat note in lib/Sat/CMakeLists.txt."
#endif

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
  const CadicalOptions options;
  void applyOptions();

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

  // Bounded variable addition (factor) invents extension variables in the
  // external index space, so once it is enabled STP's dense 1..n numbering
  // can no longer be used as CaDiCaL's directly: every variable has to be
  // declared, CaDiCaL picks where each declared range lives, and clause
  // literals and model lookups translate through this table. ext_of_stp[v]
  // is the CaDiCaL external index declared for STP variable v (1-based;
  // entry 0 unused). Empty and unused while factor is off, which keeps the
  // untranslated fast path bit-for-bit identical to pre-factor builds.
  std::vector<int> ext_of_stp;
  bool factor_enabled = false;

  // Probed once at construction (inside the configuration window):
  // whether this CaDiCaL build knows the "inprobing" option at all.
  bool inprobing_control = false;
  void declareNewVariables();

  // The external propagator that turns preferDecisions() into decisions;
  // see Cadical.cpp. Created on the first hint, so a solver that was never
  // hinted runs without one: while one is connected CaDiCaL forgoes its
  // lucky-phase probing and notifies the propagator of every assignment
  // of a variable it observes.
  class DecisionHints;
  std::unique_ptr<DecisionHints> hints;

  // Whether a search or a simplification has run. Hints are accepted only
  // before either: a variable may only be observed while inprocessing has
  // not touched it, and before the first search none has been.
  bool searched = false;

  // The IPASIR-UP side of SATSolver::TheoryPropagator. CaDiCaL speaks signed
  // external indices; STP speaks var*2+sign. This is the only place the two
  // meet, which is what keeps the theory itself free of any CaDiCaL type.
  //
  // Nothing here may throw: these are called from inside CaDiCaL's search,
  // across a C++ boundary that is not prepared to unwind. The theory reports
  // failure through failed() instead, and once it has, this stops asking it
  // anything and lets the solve finish so the caller can see the failure.
  class PropagatorBridge : public CaDiCaL::ExternalPropagator
#if defined(STP_CADICAL_HAS_DECISION_POLARITY)
                        , public CaDiCaL::DecisionPolarityAdvisor
#endif
  {
  public:
    PropagatorBridge(Cadical& owner, SATSolver::TheoryPropagator& theory)
        : owner(owner), theory(theory)
    {
      // The theory judges complete assignments as well as partial ones, so
      // this is not a lazy propagator.
      is_lazy = false;
      // A reason the theory gives for a propagated literal is a fact of the
      // theory, not of the trail; CaDiCaL may drop it once it is done with
      // it, like any other learned clause.
      are_reasons_forgettable = true;
    }

    void notify_assignment(const std::vector<int>& lits) override;
    void notify_new_decision_level() override;
    void notify_backtrack(size_t new_level) override;
    bool cb_check_found_model(const std::vector<int>& model) override;
    bool cb_has_external_clause(bool& is_forgettable) override;
    int cb_add_external_clause_lit() override;
    int cb_propagate() override;
    int cb_add_reason_clause_lit(int propagated_lit) override;
#if defined(STP_CADICAL_HAS_DECISION_POLARITY)
    int advise_decision_polarity(int default_literal) override;
#endif

    // Called once, before the search starts, so the notification path never
    // has to grow its buffer.
    void reserveNotificationBuffer(size_t count) { translated.reserve(count); }

  private:
    Cadical& owner;
    SATSolver::TheoryPropagator& theory;
    std::vector<SATSolver::Lit> pending;   // clause being handed over
    size_t pending_index = 0;
    bool pending_active = false;
    std::vector<SATSolver::Lit> reason;    // reason clause being handed over
    size_t reason_index = 0;
    int reason_for = 0;
    // Reused across notifications: this runs on every assignment of an
    // observed variable, and must not allocate on that path.
    std::vector<SATSolver::Lit> translated;
  };

  std::unique_ptr<PropagatorBridge> propagator_bridge;
  // CaDiCaL external index -> STP variable, populated only when factoring
  // has moved the numbering apart.
  std::vector<uint32_t> stp_of_ext;

  int externalOfStpVar(uint32_t var);
  bool stpVarOfExternal(int external, uint32_t& var) const;

public:
  Cadical();
  explicit Cadical(const CadicalOptions& options);

  bool supportsTheoryPropagator() const override { return true; }
  bool supportsDecisionPolarity() const override;
  bool connectTheoryPropagator(
      SATSolver::TheoryPropagator* propagator,
      const std::vector<uint32_t>& observed) override;
  void disconnectTheoryPropagator() override;

  ~Cadical();

  bool okay() const override; // FALSE means solver is in a conflicting state

  void setMaxConflicts(int64_t max_confl) override; // set max solver conflicts

  bool simplify() override; // Removes already satisfied clauses.

  uint8_t modelValue(uint32_t x) const override;

  uint32_t newVar() override;

  void setFrozen(uint32_t var) override;

  // Root-level facts CaDiCaL has derived; see SATSolver.
  int simplifyOnly() override;
  int rootFixed(unsigned var) override;
  bool reportsRootFixed() const override { return true; }

  bool setSearchBiasInternal(SearchBias bias) override;

  bool enableBVAInternal() override;

  bool supportsInprobingControl() const override;
  bool disableInprobingInternal() override;
  bool disableEliminationAndShrinkingInternal() override;
  bool disableLuckyPhasesInternal() override;

  bool enableTrailReuseInternal(TrailReuse scope) override;

  void suggestPhase(uint32_t var, bool value) override;
  void declarePendingVariables() override;
  bool supportsSearchReset() const override { return !factor_enabled; }
  bool resetSearch() override;
  bool preferDecisions(const std::vector<DecisionHint>& wanted) override;

  void unsatAssumptions(const vec_literals& assumps,
                        std::vector<int>& out) override;

  void setVerbosity(int v) override;

  uint32_t nVars() const override;
  bool validVariable(uint32_t x) const override
  {
    return x != 0 && x <= nVars();
  }

  bool reportsClauseCount() const override { return true; }

  int nClauses() override;

  void printStats() const override;

  lbool true_literal() const override { return ((uint8_t)1); }
  lbool false_literal() const override { return ((uint8_t)-1); }
  lbool undef_literal() const override { return ((uint8_t)2); }

public:
  bool supportsAssumptions() const override { return true; }

protected:
  bool addClauseInternal(const vec_literals& ps) override;
  bool solveInternal(bool& timeout_expired) override;
  bool solveWithAssumptionsInternal(const vec_literals& assumps,
                                    bool& timeout_expired) override;

  // Cadical polls the Terminator we connect during search.
  bool canInterruptSearch() const override { return true; }
};
}

#endif

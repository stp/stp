#ifndef STP_KISSAT_H
#define STP_KISSAT_H

#include "stp/Sat/SATSolver.h"
#include "stp/Util/Attributes.h"

#include <memory>

extern "C"
{
#include <kissat/kissat.h>
}

#ifndef KISSAT_HAS_INCREMENTAL
#error "STP requires Kissat with the incremental API"
#endif
#ifndef KISSAT_HAS_INCREMENTAL_GREEDY
#error "STP requires Kissat with bounded incremental greedy completion"
#endif

namespace stp
{
class DLL_PUBLIC Kissat : public SATSolver
{
  struct Allocations;
  struct LuckyProbe;
  std::unique_ptr<Allocations> allocations;
  std::unique_ptr<LuckyProbe> lucky_probe;
  kissat* solver;
  std::vector<int> external;
  std::vector<bool> frozen;
  int last_external = 0;
  int64_t max_conflicts = -1;
  bool trail_reuse_allowed;
  int trail_reuse_mode;
  int search_mode;
  int one_shot_search_mode = -1;
  uint64_t solve_calls = 0;
  bool one_shot = false;
  int import_order = 0;
  // Clause exchange (connectClauseExchange), through the exchange extension
  // of STP's Kissat fork.
  struct Exchange;
  std::unique_ptr<Exchange> exchange;
  // A connected TheoryPropagator (connectTheoryPropagator), through the
  // IPASIR-UP interface of STP's Kissat fork, and the STP variable of every
  // external variable STP allocated (external[v] + 1 maps back to v + 1).
  struct PropagatorBridge;
  std::unique_ptr<PropagatorBridge> propagator_bridge;
  std::vector<uint32_t> stp_of_external;
  // The propagator that turns preferDecisions() into decisions, through the
  // same interface; a theory takes its place when one connects.
  struct DecisionHints;
  std::unique_ptr<DecisionHints> hints;
  void connectHints();
  void disconnectHints();

  void requireHealthy() const;
  int literal(Lit lit) const;
  bool run(bool& timeout_expired);
  bool tryLuckyProbe(const vec_literals& assumptions, bool& timeout_expired);
  static int terminate(void* state);

public:
  explicit Kissat(bool trail_reuse_allowed = true, int search_mode = -1);
  Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed);
  Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed,
         int trail_reuse_mode);
  Kissat(bool trail_reuse_allowed, int search_mode, bool probing_allowed,
         int trail_reuse_mode, int elimination);
  ~Kissat() override;
  struct GreedyOptions
  {
    int mode = 0;
    int conflicts = 100;
    int decisions = 10000;
    int growth = 4;
    bool phase_cache = false;
  };
  void setGreedyOptions(const GreedyOptions& options);
  void setImportOrder(int order);
  void setOneShotSearchMode(int mode);
  bool okay() const override;
  bool supportsAssumptions() const override { return !one_shot; }
  bool configureOneShot() override;
  bool enableLuckyProbe() override;
  struct LuckyProbeStatistics
  {
    uint64_t attempts = 0;
    uint64_t successes = 0;
    uint64_t inconclusive = 0;
    uint64_t rejected_models = 0;
    uint64_t retained_literals = 0;
  };
  LuckyProbeStatistics luckyProbeStatistics() const;
  uint8_t modelValue(uint32_t var) const override;
  uint32_t newVar() override;
  uint32_t nVars() const override
  {
    return static_cast<uint32_t>(external.size());
  }
  void setFrozen(uint32_t var) override;
  void suggestPhase(uint32_t var, bool value) override;
  bool preferDecisions(const std::vector<DecisionHint>& wanted) override;
  int simplifyOnly() override;
  int rootFixed(unsigned var) override;
  bool reportsRootFixed() const override;
  void unsatAssumptions(const vec_literals& assumptions,
                        std::vector<int>& out) override;
  void setSeed(uint64_t seed) override;
  void setMaxConflicts(int64_t limit) override { max_conflicts = limit; }
  void clearMaxConflicts() override { max_conflicts = -1; }
  void printStats() const override;
  void setVerbosity(int verbosity) override;
  bool connectClauseExchange(ClauseExchange* exchange,
                             const ExchangeSettings& settings) override;
  ExchangeCounters exchangeCounters() const override;
  bool diversify(const Diversification& d) override;
  bool supportsTheoryPropagator() const override;
  bool supportsDecisionPolarity() const override;
  bool connectTheoryPropagator(TheoryPropagator* propagator,
                               const std::vector<uint32_t>& observed) override;
  void disconnectTheoryPropagator() override;
  lbool true_literal() const override { return 1; }
  lbool false_literal() const override { return 0; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals& clause) override;
  bool solveInternal(bool& timeout_expired) override;
  bool solveWithAssumptionsInternal(const vec_literals& assumptions,
                                    bool& timeout_expired) override;
  bool canInterruptSearch() const override { return true; }
  bool setSearchBiasInternal(SearchBias bias) override;
  bool setSearchOptionsInternal(const SatSearchOptions& options) override;
  bool enableBVAInternal() override;
  bool enableTrailReuseInternal(TrailReuse scope) override;
  bool disableLuckyPhasesInternal() override;
};
} // namespace stp

#endif

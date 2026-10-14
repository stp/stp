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

namespace stp
{
class DLL_PUBLIC Kissat : public SATSolver
{
  struct Allocations;
  std::unique_ptr<Allocations> allocations;
  kissat* solver;
  std::vector<int> external;
  std::vector<bool> frozen;
  int last_external = 0;
  int64_t max_conflicts = -1;
  bool trail_reuse_allowed;
  int search_mode;
  uint64_t solve_calls = 0;
  bool one_shot = false;

  void requireHealthy() const;
  int literal(Lit lit) const;
  bool run(bool& timeout_expired);
  static int terminate(void* state);

public:
  explicit Kissat(bool trail_reuse_allowed = true, int search_mode = -1);
  ~Kissat() override;
  bool okay() const override;
  bool supportsAssumptions() const override { return !one_shot; }
  bool configureOneShot() override;
  uint8_t modelValue(uint32_t var) const override;
  uint32_t newVar() override;
  uint32_t nVars() const override
  {
    return static_cast<uint32_t>(external.size());
  }
  void setFrozen(uint32_t var) override;
  void suggestPhase(uint32_t var, bool value) override;
  void unsatAssumptions(const vec_literals& assumptions,
                        std::vector<int>& out) override;
  void setSeed(uint64_t seed) override;
  void setMaxConflicts(int64_t limit) override { max_conflicts = limit; }
  void clearMaxConflicts() override { max_conflicts = -1; }
  void printStats() const override;
  void setVerbosity(int verbosity) override;
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

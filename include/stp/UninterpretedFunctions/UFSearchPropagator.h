#ifndef STP_UF_SEARCH_PROPAGATOR_H
#define STP_UF_SEARCH_PROPAGATOR_H

#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/UninterpretedFunctions/UFLowering.h"
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace stp
{

// A QF_UF search-time congruence checker. It observes the bit carriers of
// lowered applications, groups applications once their arguments are known,
// and sends CaDiCaL a theory-valid no-good when matching applications have
// opposing result bits. The batch UF checker remains the final certifier.
class UFSearchPropagator final : public SATSolver::TheoryPropagator
{
public:
  UFSearchPropagator() = default;
  ~UFSearchPropagator() override;

  UFSearchPropagator(const UFSearchPropagator&) = delete;
  UFSearchPropagator& operator=(const UFSearchPropagator&) = delete;

  // False means setup was unavailable; the ordinary UF refinement can run.
  bool connect(SATSolver& solver, const LoweredApplicationView& view,
               const ToSATBase::ASTNodeToSATVar& bindings);
  bool connected() const { return solver_ != nullptr; }
  const std::string& diagnostic() const { return diagnostic_; }
  uint64_t conflicts() const { return conflicts_; }
  uint64_t observedApplications() const { return applications_.size(); }

  void notifyAssigned(const std::vector<SATSolver::Lit>& literals) override;
  void notifyNewLevel() override;
  void notifyBacktrack(size_t level) override;
  bool checkFoundModel() override;
  bool takeClause(std::vector<SATSolver::Lit>& clause) override;
  bool failed() const override { return failed_; }

private:
  struct Bit
  {
    uint32_t variable = 0; // zero only for a constant
    bool constantValue = false;
  };
  using Key = std::pair<uint64_t, std::string>;
  struct Application
  {
    Key key;
    std::vector<Bit> arguments;
    std::vector<Bit> result;
    size_t remaining = 0;
    size_t position = 0;
    bool ready = false;
  };
  struct ResultUse
  {
    size_t application;
  };

  bool prepare(const LoweredApplicationView& view,
               const ToSATBase::ASTNodeToSATVar& bindings,
               SATSolver& solver, std::vector<uint32_t>& observed);
  bool addBits(const ASTNode& leaf, std::vector<Bit>& bits,
               const ToSATBase::ASTNodeToSATVar& bindings,
               SATSolver& solver);
  int value(const Bit& bit) const;
  Key keyFor(const Application& app) const;
  void insertReady(size_t id);
  void removeReady(size_t id);
  bool inspect(size_t id);
  bool conflict(size_t left, size_t right);
  void appendPremises(const Application& app,
                      std::vector<SATSolver::Lit>& clause) const;
  void fail(const char* reason);

  SATSolver* solver_ = nullptr;
  std::vector<Application> applications_;
  std::vector<std::vector<size_t>> argumentUses_;
  std::vector<std::vector<ResultUse>> resultUses_;
  std::map<Key, std::vector<size_t>> buckets_;
  std::vector<int8_t> assignments_;
  std::vector<uint32_t> trail_;
  std::vector<size_t> levelMarks_{0};
  std::vector<SATSolver::Lit> pending_;
  std::string diagnostic_;
  uint64_t conflicts_ = 0;
  bool failed_ = false;
  bool attempted_ = false;
};

} // namespace stp

#endif

#ifndef STP_LRA_RECONSTRUCTION_H
#define STP_LRA_RECONSTRUCTION_H
#include "RealModel.h"
#include <chrono>
#include <functional>

namespace stp::lra
{
class ReluProblem;
struct LraReconstruction
{
  /* The query as the caller wrote it, before presolve rewrote anything.
   * Always recorded, because the model commit checks its model against this
   * as well as against the formula it actually solved. */
  ASTNode original;
  /* Whether the caller permits model replay for this query. When it does
   * not, neither a replay nor dead-definition elimination is selected, and
   * HiGHS gets no storage for a model of its own; `original` is still
   * recorded and checked. */
  bool replay_allowed = true;
  /* Whether a model replay was selected for this query. A separate question
   * from `original`, which is recorded whether or not one was. */
  bool replay_selected = false;
  std::vector<RealModelDefinition> definitions;
  std::size_t replay_attempts = 0;
  std::size_t replay_screened = 0;
  double replay_seconds = 0;
  bool witness = false;
  // A query-local decision, separate from the HiGHS model-certificate context.
  bool eliminate_definitions = false;
};

ASTNode removeDeadRealDefinitions(STPMgr& manager, const ASTNode& input,
                                  LraReconstruction& reconstruction,
                                  const std::function<void()>& poll = {});
bool acceptsRealFormula(
    const ASTNode&, const std::function<bool(const ASTNode&)>&,
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max());
bool tryReluWitness(
    ReluProblem& problem, const std::vector<double>& proposal,
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max());
} // namespace stp::lra
#endif

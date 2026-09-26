#ifndef STP_LRA_RELU_H
#define STP_LRA_RELU_H

#include "LraFrontend.h"

#include <deque>
#include <memory>
#include <optional>
#include <unordered_map>

namespace stp
{
class SATSolver;
namespace lra
{
struct LraReconstruction;
struct ReluReplayPlan;

// Query-local, exact relaxation of asserted affine rows and direct-OR ReLUs.
// All members containing rationals live inside the caller's number scope.
// Bounds are closed overapproximations, including when the source is strict.
class ReluProblem final
{
public:
  using Var = std::size_t;
  struct Term
  {
    Var var;
    ExactRational coefficient;
  };
  struct Row
  {
    std::vector<Term> terms;
    ExactRational rhs;
    bool equality = false; // otherwise sum(terms) <= rhs
  };
  struct Box
  {
    std::optional<ExactRational> lower, upper;
  };
  struct Relu
  {
    Var pre, post;
    ASTNode source;
  };
  struct Definition
  {
    Var target;
    std::vector<Term> terms;
    ExactRational constant;
    ASTNode source;
  };

  ReluProblem(STPMgr& manager, const ASTNode& input);
  void propagate(std::uint64_t work_limit = 8000000);
  bool tighten(Var var, const ExactRational& value, bool lower);
  ASTNode formula();
  std::vector<Row> relaxation() const;
  std::optional<Row> linearRow(const ASTNode& atom);
  std::size_t fixed() const;

  STPMgr& manager;
  ASTVec conjuncts, symbols;
  ASTVec lemmas;
  std::vector<Box> bounds;
  std::vector<Row> rows;
  std::vector<Relu> relus;
  std::vector<Definition> definitions;
  bool infeasible = false;
  bool satisfied = false;
  LraReconstruction* reconstruction = nullptr;
  std::shared_ptr<ReluReplayPlan> replay_plan;
  bool limited = false;
  std::uint64_t updates = 0, work = 0;
  std::uint64_t boolean_bound_updates = 0;

private:
  void propagateBooleanBounds();
  Var variable(const ASTNode& node);
  void enqueue(Var var);
  Frontend frontend_;
  std::unordered_map<std::uint64_t, Var> ids_;
  std::vector<std::vector<std::size_t>> uses_;
  std::deque<std::size_t> pending_;
  std::vector<bool> queued_;
};

// Call within a NumberOperationScope. No state survives this query and no
// conditional assertion is used as an unconditional source of bounds.
ASTNode presolveRelus(STPMgr& manager, const ASTNode& input, bool& recognized,
                      SATSolver* solver, LraReconstruction* reconstruction);
void tightenReluRelaxation(ReluProblem& problem, SATSolver* solver,
                           bool automatic = false);
void pruneReluCases(ReluProblem& problem, SATSolver* solver);
void branchReluRelaxation(ReluProblem& problem, SATSolver* solver);

} // namespace lra
} // namespace stp
#endif

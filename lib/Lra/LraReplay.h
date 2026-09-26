#ifndef STP_LRA_REPLAY_H
#define STP_LRA_REPLAY_H
#include "LraRelu.h"
#include <unordered_set>

namespace stp::lra
{
// Immutable topology and approximate coefficients, shared by a query's branch
// nodes. No exact value or node-local bound is cached in this plan.
struct ReluReplayPlan
{
  struct Producer
  {
    bool relu;
    std::size_t index;
  };
  struct Term
  {
    std::size_t var;
    double coefficient;
  };
  struct Expression
  {
    std::vector<Term> terms;
    double constant = 0;
  };
  struct Predicate
  {
    Expression expression;
    Kind kind;
  };
  std::vector<std::size_t> parent, order;
  std::vector<std::optional<Producer>> producers;
  std::vector<Expression> definitions;
  std::unordered_set<std::uint64_t> implied;
  std::unordered_map<std::uint64_t, Predicate> predicates;
  bool valid = false;
  // In addition to a replayable topology, every source predicate is affine
  // and every remaining Boolean node can be checked without a SAT model.
  bool complete_formula = false;

  explicit ReluReplayPlan(ReluProblem& problem, const ASTNode& original);
  bool possible(ReluProblem& problem, const ASTNode& original,
                const std::vector<std::optional<ExactRational>>& inputs) const;
};
} // namespace stp::lra
#endif

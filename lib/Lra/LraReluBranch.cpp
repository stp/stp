#include "LraReconstruction.h"
#include "LraRelaxation.h"
#include "stp/STPManager/STPManager.h"

#include <chrono>
#include <cmath>
#include <iostream>
#include <unordered_set>

namespace stp::lra
{
void branchReluRelaxation(ReluProblem& problem, SATSolver* solver)
{
#ifndef STP_HAVE_HIGHS
  (void)problem;
  (void)solver;
  throw FrontendFailure(FrontendFailureKind::Unsupported,
                        "ReLU phase search requires ENABLE_HIGHS");
#else
  using Clock = std::chrono::steady_clock;
  const auto start = Clock::now();
  auto& manager = problem.manager;
  auto remaining = [&]()
  {
    const double local =
        manager.UserFlags.lra_relu_branch_seconds -
        std::chrono::duration<double>(Clock::now() - start).count();
    return std::min(local, solver && solver->hasTimeLimit()
                               ? solver->secondsRemaining()
                               : local);
  };
  struct Assumption
  {
    ReluProblem::Var pre;
    bool positive;
  };
  using Path = std::vector<Assumption>;
  struct Property
  {
    ASTNode guard;
    std::vector<ReluProblem::Row> rows;
  };
  std::vector<Property> properties;
  if (manager.UserFlags.lra_relu_property_branches)
  {
    std::unordered_set<std::uint64_t> relations;
    for (const auto& relu : problem.relus)
      relations.insert(relu.source.GetNodeNum());
    for (const auto& conjunct : problem.conjuncts)
    {
      if (conjunct.GetKind() != OR || conjunct.Degree() > 16 ||
          relations.count(conjunct.GetNodeNum()))
        continue;
      std::vector<Property> candidate;
      bool supported = true;
      for (const auto& arm : conjunct.GetChildren())
      {
        Property property{arm, {}};
        ASTVec atoms{arm};
        std::size_t visited = 0;
        while (!atoms.empty() && supported)
        {
          if (++visited > 64)
          {
            supported = false;
            break;
          }
          const auto atom = atoms.back();
          atoms.pop_back();
          if (atom.GetKind() == AND && atom.Degree() <= 8)
            for (const auto& child : atom.GetChildren())
              atoms.push_back(child);
          else if (const auto row = problem.linearRow(atom))
            property.rows.push_back(*row);
          else
            supported = false;
          if (atoms.size() + property.rows.size() > 8)
            supported = false;
        }
        if (!supported)
          break;
        candidate.push_back(std::move(property));
      }
      if (supported && candidate.size() >= 2)
      {
        properties = std::move(candidate);
        break;
      }
    }
  }
  struct Task
  {
    Path path;
    std::optional<std::size_t> property;
  };
  std::vector<Task> todo;
  if (properties.empty())
    todo.push_back({{}, std::nullopt});
  else
    // Every arm of this asserted OR is mandatory. A pending property arm
    // prevents refuting the query just like a pending phase child does.
    for (std::size_t i = properties.size(); i > 0; --i)
      todo.push_back({{}, i - 1});
  std::size_t nodes = 0, splits = 0, closed = 0, open = 0, maximum_depth = 0;
  const ExactRational nil;
  const auto zero = manager.CreateRealConst("0");
  while (!todo.empty() && remaining() > 0 &&
         manager.UserFlags.lra_relu_lp_call_seconds > 0 &&
         nodes < manager.UserFlags.lra_relu_branch_nodes)
  {
    Task task = std::move(todo.back());
    todo.pop_back();
    auto& path = task.path;
    ++nodes;
    maximum_depth = std::max(maximum_depth, path.size());
    // Each node starts from the same unconditional facts. Its tightened box,
    // fixed phases and queue are private and never overwrite the root state.
    ReluProblem node(problem);
    if (task.property)
      for (const auto& row : properties[*task.property].rows)
      {
        node.rows.push_back(row);
        if (row.terms.size() != 1 || row.terms[0].coefficient.isZero())
          continue;
        const auto& term = row.terms[0];
        const auto value = row.rhs / term.coefficient;
        if (row.equality || term.coefficient.sign() < 0)
          node.tighten(term.var, value, true);
        if (row.equality || term.coefficient.sign() > 0)
          node.tighten(term.var, value, false);
      }
    for (const auto& assumption : path)
      node.tighten(assumption.pre, nil, assumption.positive);
    node.propagate();
    RelaxationProbe probe;
    if (!node.infeasible)
      probe = probeRelaxation(
          node.relaxation(), node.bounds,
          std::min<double>(manager.UserFlags.lra_relu_lp_call_seconds,
                           remaining()),
          manager.UserFlags.lra_lp_partial);
    if (node.infeasible || probe.refuted)
    {
      ++closed;
      ASTVec literals;
      // Property rows are conditional too. Omitting this guard would let a
      // refuted output alternative discard models satisfying another one.
      if (task.property)
        literals.push_back(
            manager.CreateNode(NOT, properties[*task.property].guard));
      for (const auto& assumption : path)
      {
        // Negate precisely the closed bound used in this node. In
        // particular, NOT(pre >= 0) is pre < 0, not pre <= 0.
        const auto guard =
            manager.CreateNode(assumption.positive ? REAL_GE : REAL_LE,
                               problem.symbols[assumption.pre], zero);
        literals.push_back(manager.CreateNode(NOT, guard));
      }
      problem.lemmas.push_back(literals.empty() ? manager.ASTFalse
                               : literals.size() == 1
                                   ? literals[0]
                                   : manager.CreateNode(OR, literals));
      continue;
    }
    // Preserve SAT's own search when the relaxation supplies no useful
    // non-linear violation. Floating values are advice only, never a model.
    std::optional<ReluProblem::Var> chosen;
    double best = 1e-8;
    if (probe.values.size() == node.symbols.size())
      for (const auto& relu : node.relus)
      {
        const auto& box = node.bounds[relu.pre];
        if (!box.lower || !box.upper || box.lower->sign() >= 0 ||
            box.upper->sign() <= 0)
          continue;
        const double pre = probe.values[relu.pre],
                     post = probe.values[relu.post];
        if (!std::isfinite(pre) || !std::isfinite(post))
          continue;
        const double violation = std::abs(post - std::max(pre, 0.0));
        if (violation > best)
        {
          best = violation;
          chosen = relu.pre;
        }
      }
    if (!chosen)
    {
      if (tryReluWitness(node, probe.values))
      {
        problem.satisfied = true;
        break;
      }
      ++open;
      continue;
    }
    ++splits;
    // Both children are mandatory: pre <= 0 and pre >= 0 cover all reals,
    // including their shared zero boundary. A pending or abandoned child
    // prevents a whole-query refutation.
    Path positive = path;
    positive.push_back({*chosen, true});
    todo.push_back({std::move(positive), task.property});
    path.push_back({*chosen, false});
    todo.push_back({std::move(path), task.property});
  }
  open += todo.size();
  if (open == 0 && nodes != 0 && !problem.satisfied)
    problem.infeasible = true;
  if (manager.UserFlags.stats_flag)
    std::cerr << "LRA ReLU branch: nodes=" << nodes << ", splits=" << splits
              << ", closed=" << closed << ", open=" << open
              << ", depth=" << maximum_depth
              << ", clauses=" << problem.lemmas.size()
              << ", infeasible=" << problem.infeasible
              << ", property_roots=" << properties.size() << ", seconds="
              << std::chrono::duration<double>(Clock::now() - start).count()
              << '\n';
#endif
}
} // namespace stp::lra

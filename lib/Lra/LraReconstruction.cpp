#include "LraReconstruction.h"
#include "LraFrontend.h"
#include "LraRelaxation.h"
#include "LraReplay.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <deque>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <unordered_set>

namespace stp::lra
{
// Evaluate the complete source Boolean DAG over an exact Real model. Refuse
// Boolean/BV/UF leaves requiring a separate model; the ordinary coordinator
// handles those. No LP status or phase approximation participates in this test.
bool acceptsRealFormula(
    const ASTNode& root, const std::function<bool(const ASTNode&)>& predicate,
    std::chrono::steady_clock::time_point deadline)
{
  std::unordered_map<std::uint64_t, bool> values;
  std::vector<std::pair<ASTNode, bool>> todo{{root, false}};
  while (!todo.empty())
  {
    if (deadline != std::chrono::steady_clock::time_point::max() &&
        std::chrono::steady_clock::now() >= deadline)
      return false;
    const ASTNode node = todo.back().first;
    const bool visited = todo.back().second;
    todo.pop_back();
    if (values.count(node.GetNodeNum()))
      continue;
    const Kind kind = node.GetKind();
    if (kind == TRUE || kind == FALSE)
    {
      values.emplace(node.GetNodeNum(), kind == TRUE);
      continue;
    }
    if (node.Degree() == 2 && node[0].isRealTerm() && node[1].isRealTerm() &&
        (kind == EQ || kind == REAL_LT || kind == REAL_LE || kind == REAL_GT ||
         kind == REAL_GE))
    {
      values.emplace(node.GetNodeNum(), predicate(node));
      continue;
    }
    if (kind != AND && kind != OR && kind != NOT && kind != XOR &&
        kind != IFF && kind != IMPLIES && kind != ITE)
      return false;
    if (!visited)
    {
      todo.emplace_back(node, true);
      for (const auto& child : node.GetChildren())
        todo.emplace_back(child, false);
      continue;
    }
    auto child = [&](std::size_t i) { return values.at(node[i].GetNodeNum()); };
    bool value = false;
    switch (kind)
    {
      case AND:
        value = true;
        for (const auto& n : node.GetChildren())
          value = value && values.at(n.GetNodeNum());
        break;
      case OR:
        for (const auto& n : node.GetChildren())
          value = value || values.at(n.GetNodeNum());
        break;
      case NOT:
        if (node.Degree() != 1)
          return false;
        value = !child(0);
        break;
      case IFF:
        if (node.Degree() != 2)
          return false;
        value = child(0) == child(1);
        break;
      case IMPLIES:
        if (node.Degree() != 2)
          return false;
        value = !child(0) || child(1);
        break;
      case XOR:
        for (const auto& n : node.GetChildren())
          value = value != values.at(n.GetNodeNum());
        break;
      case ITE:
        if (node.Degree() != 3)
          return false;
        value = child(0) ? child(1) : child(2);
        break;
      default:
        return false;
    }
    values.emplace(node.GetNodeNum(), value);
  }
  return values.at(root.GetNodeNum());
}

bool tryReluWitness(ReluProblem& problem, const std::vector<double>& proposal,
                    std::chrono::steady_clock::time_point deadline)
{
  const auto expired = [&]() {
    return deadline != std::chrono::steady_clock::time_point::max() &&
           std::chrono::steady_clock::now() >= deadline;
  };
  auto* reconstruction = problem.reconstruction;
  if (!reconstruction || proposal.size() != problem.symbols.size() ||
      reconstruction->replay_attempts >= 32 || expired())
    return false;
  ++reconstruction->replay_attempts;
  struct Timer
  {
    LraReconstruction& reconstruction;
    std::chrono::steady_clock::time_point start =
        std::chrono::steady_clock::now();
    ~Timer()
    {
      reconstruction.replay_seconds +=
          std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                        start)
              .count();
    }
  } timer{*reconstruction};
  const std::size_t n = problem.symbols.size();
  if (!problem.replay_plan || problem.replay_plan->parent.size() != n)
    problem.replay_plan =
        std::make_shared<ReluReplayPlan>(problem, reconstruction->original);
  const auto& plan = *problem.replay_plan;
  if (!plan.valid || expired())
    return false;
  const auto& parent = plan.parent;
  const auto& producers = plan.producers;
  std::vector<std::optional<ExactRational>> values(n);
  for (const auto v : plan.order)
  {
    if (expired())
      return false;
    if (producers[v])
      continue;
    if (!std::isfinite(proposal[v]))
      return false;
    auto value = exactDyadic(proposal[v]);
    const auto& box = problem.bounds[v];
    if (box.lower && value < *box.lower)
      value = *box.lower;
    if (box.upper && value > *box.upper)
      value = *box.upper;
    values[v] = std::move(value);
  }
  if (problem.manager.UserFlags.lra_replay_screen &&
      !plan.possible(problem, reconstruction->original, values))
  {
    ++reconstruction->replay_screened;
    return false;
  }
  for (const auto v : plan.order)
  {
    if (expired())
      return false;
    if (!producers[v])
      continue;
    const auto p = *producers[v];
    if (p.relu)
      values[v] = std::max(ExactRational(),
                           *values[parent[problem.relus[p.index].pre]]);
    else
    {
      const auto& d = problem.definitions[p.index];
      auto value = d.constant;
      for (const auto& term : d.terms)
      {
        if (expired())
          return false;
        value += term.coefficient * *values[parent[term.var]];
      }
      values[v] = std::move(value);
    }
  }
  // Stay within the presolver's arithmetic budget. The published RealModel
  // has its own budget and is constructed only after this scope has ended.
  std::unordered_map<std::uint64_t, ExactRational> exact;
  for (std::size_t v = 0; v < n; ++v)
  {
    if (expired())
      return false;
    const auto& value = values[parent[v]];
    if (!value)
      return false;
    exact.emplace(problem.symbols[v].GetNodeNum(), *value);
  }
  auto termValue = [&](const ASTNode& input) -> const ExactRational&
  {
    std::vector<std::pair<ASTNode, bool>> pending{{input, false}};
    while (!pending.empty())
    {
      if (expired())
        throw std::runtime_error("exact replay deadline");
      const ASTNode term = pending.back().first;
      const bool visited = pending.back().second;
      pending.pop_back();
      if (exact.count(term.GetNodeNum()))
        continue;
      if (!term.isRealTerm())
        throw std::runtime_error("non-Real replay term");
      const Kind kind = term.GetKind();
      if (kind == REAL_CONST)
      {
        exact.emplace(term.GetNodeNum(),
                      ExactRational::fromCanonicalIntegers(
                          term.GetRealNumerator(), term.GetRealDenominator()));
        continue;
      }
      if (kind != REAL_ADD && kind != REAL_SUB && kind != REAL_NEG &&
          kind != REAL_MUL && kind != REAL_DIV)
        throw std::runtime_error("unsupported exact replay term");
      if (!visited)
      {
        pending.emplace_back(term, true);
        for (const auto& child : term.GetChildren())
          pending.emplace_back(child, false);
        continue;
      }
      const auto arg = [&](std::size_t i) -> const ExactRational&
      { return exact.at(term[i].GetNodeNum()); };
      if (term.Degree() == 0)
        throw std::runtime_error("empty replay term");
      auto value = arg(0);
      if (kind == REAL_NEG || (kind == REAL_SUB && term.Degree() == 1))
        value.negate();
      else if (kind == REAL_ADD || kind == REAL_SUB)
      {
        for (std::size_t i = 1; i < term.Degree(); ++i)
        {
          if (expired())
            throw std::runtime_error("exact replay deadline");
          if (kind == REAL_ADD)
            value += arg(i);
          else
            value -= arg(i);
        }
      }
      else if (term.Degree() != 2)
        throw std::runtime_error("malformed replay term");
      else if (kind == REAL_MUL)
        value *= arg(1);
      else
        value /= arg(1);
      exact.emplace(term.GetNodeNum(), std::move(value));
    }
    return exact.at(input.GetNodeNum());
  };
  try
  {
    if (!acceptsRealFormula(reconstruction->original,
                            [&](const ASTNode& atom)
                            {
                              // A subsequent term evaluation may rehash the map; references to its
                              // elements remain valid across rehashing.
                              const auto& left = termValue(atom[0]);
                              const auto& right = termValue(atom[1]);
                              const int comparison = left.compare(right);
                              switch (atom.GetKind())
                              {
                                case EQ:
                                  return comparison == 0;
                                case REAL_LT:
                                  return comparison < 0;
                                case REAL_LE:
                                  return comparison <= 0;
                                case REAL_GT:
                                  return comparison > 0;
                                case REAL_GE:
                                  return comparison >= 0;
                                default:
                                  return false;
                              }
                            }, deadline))
      return false;
  }
  catch (const std::exception&)
  {
    return false;
  }
  // The whole original formula holds, so freeze this exact witness. The
  // coordinator will independently evaluate that formula again before it
  // publishes SAT, using its ordinary model-publication protocol.
  std::vector<RealModelDefinition> definitions;
  for (std::size_t v = 0; v < n; ++v)
  {
    if (expired())
      return false;
    definitions.push_back(
        {problem.symbols[v], problem.manager.CreateRealConst(
                                 values[parent[v]]->canonicalFraction())});
  }
  if (expired())
    return false;
  reconstruction->definitions = std::move(definitions);
  reconstruction->witness = true;
  problem.satisfied = true;
  return true;
}

ASTNode removeDeadRealDefinitions(STPMgr& manager, const ASTNode& input,
                                  LraReconstruction& reconstruction,
                                  const std::function<void()>& poll)
{
  const auto visit = [&]() {
    if (poll)
      poll();
  };
  ASTVec conjuncts, todo{input};
  ASTNodeSet unique;
  while (!todo.empty())
  {
    visit();
    const auto node = todo.back();
    todo.pop_back();
    if (!unique.insert(node).second)
      continue;
    if (node.GetKind() == AND)
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    else if (node != manager.ASTTrue)
      conjuncts.push_back(node);
  }
  using Id = std::uint64_t;
  std::vector<std::vector<Id>> variables(conjuncts.size());
  std::unordered_map<Id, std::size_t> counts;
  std::unordered_map<Id, std::vector<std::size_t>> uses;
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    ASTVec stack{conjuncts[i]};
    ASTNodeSet seen;
    while (!stack.empty())
    {
      visit();
      const auto node = stack.back();
      stack.pop_back();
      if (!seen.insert(node).second)
        continue;
      if (node.GetKind() == SYMBOL && node.isRealTerm())
      {
        const auto id = node.GetNodeNum();
        variables[i].push_back(id);
        ++counts[id];
        uses[id].push_back(i);
      }
      for (const auto& child : node.GetChildren())
        stack.push_back(child);
    }
  }
  Frontend frontend(manager);
  std::deque<std::size_t> queue;
  std::vector<bool> queued(conjuncts.size(), true),
      removed(conjuncts.size(), false);
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
    queue.push_back(i);
  std::vector<RealModelDefinition> eliminated;
  while (!queue.empty())
  {
    visit();
    const auto index = queue.front();
    queue.pop_front();
    queued[index] = false;
    const auto& node = conjuncts[index];
    if (removed[index] || node.GetKind() != EQ || node.Degree() != 2)
      continue;
    for (std::size_t side = 0; side < 2; ++side)
    {
      const auto& target = node[side];
      if (target.GetKind() != SYMBOL || !target.isRealTerm() ||
          manager.FoundIntroducedSymbolSet(target) ||
          !node[1 - side].isRealTerm() || counts[target.GetNodeNum()] != 1)
        continue;
      bool cyclic = false;
      ASTVec stack{node[1 - side]};
      ASTNodeSet seen;
      while (!stack.empty())
      {
        visit();
        const auto term = stack.back();
        stack.pop_back();
        if (!seen.insert(term).second)
          continue;
        if (term == target)
        {
          cyclic = true;
          break;
        }
        for (const auto& child : term.GetChildren())
          stack.push_back(child);
      }
      if (cyclic)
        continue;
      // Removing an unused equation must not bypass validation of the input
      // fragment. Restrict reconstruction to supported affine expressions.
      try
      {
        (void)frontend.normalize(node[1 - side]);
      }
      catch (const FrontendFailure& e)
      {
        if (e.kind() != FrontendFailureKind::Unsupported)
          throw;
        continue;
      }
      eliminated.push_back({target, node[1 - side]});
      removed[index] = true;
      for (const auto id : variables[index])
      {
        visit();
        if (--counts[id] != 1)
          continue;
        for (const auto user : uses[id])
        {
          visit();
          if (!removed[user] && !queued[user])
          {
            queued[user] = true;
            queue.push_back(user);
          }
        }
      }
      break;
    }
  }
  // A removed variable was used only in its own equation. Removing that
  // equation may expose its dependencies, so reverse removal order evaluates
  // the reconstruction DAG. Cycles and live constraints remain with simplex.
  std::reverse(eliminated.begin(), eliminated.end());
  // Reported whether or not anything was eliminated: the line also carries
  // the witness and replay counts of whatever replay ran before this pass.
  const auto report = [&]()
  {
    if (manager.UserFlags.stats_flag)
      std::cerr << "LRA reconstruction: eliminated=" << eliminated.size()
                << ", witness=" << reconstruction.witness
                << ", replay_attempts=" << reconstruction.replay_attempts
                << '\n';
  };
  if (eliminated.empty())
  {
    report();
    return input;
  }
  ASTVec kept;
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    visit();
    if (!removed[i])
      kept.push_back(conjuncts[i]);
  }
  const auto result = kept.empty()       ? manager.ASTTrue
                      : kept.size() == 1 ? kept[0]
                                         : manager.CreateNode(AND, kept);
  visit();
  // Commit only after the formula is ready and the final cancellation check
  // succeeds. Later eliminations supply dependencies of earlier witnesses.
  reconstruction.definitions.insert(reconstruction.definitions.begin(),
                                    eliminated.begin(), eliminated.end());
  report();
  return result;
}
} // namespace stp::lra

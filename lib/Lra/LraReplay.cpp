#include "LraReplay.h"
#include "LraRelaxation.h"
#include <algorithm>
#include <cmath>
#include <limits>
#include <numeric>

namespace stp::lra
{
namespace
{
double fastApproximate(const ExactRational& q)
{
  if (const auto small = q.trySmall())
    return static_cast<double>(small->numerator) /
           static_cast<double>(small->denominator);
  return approximate(q);
}
} // namespace

ReluReplayPlan::ReluReplayPlan(ReluProblem& problem, const ASTNode& original)
{
  const auto n = problem.symbols.size();
  parent.resize(n);
  std::iota(parent.begin(), parent.end(), 0);
  auto root = [&](std::size_t v)
  {
    while (parent[v] != v)
    {
      parent[v] = parent[parent[v]];
      v = parent[v];
    }
    return v;
  };
  auto alias = [](const ReluProblem::Definition& d)
  {
    return d.constant.isZero() && d.terms.size() == 1 &&
           d.terms[0].coefficient.isOne();
  };
  for (const auto& d : problem.definitions)
    if (alias(d))
      parent[root(d.target)] = root(d.terms[0].var);
  for (std::size_t v = 0; v < n; ++v)
    parent[v] = root(v);
  producers.resize(n);
  definitions.resize(problem.definitions.size());
  for (std::size_t i = 0; i < problem.definitions.size(); ++i)
  {
    const auto& d = problem.definitions[i];
    implied.insert(d.source.GetNodeNum());
    if (!alias(d) && !producers[parent[d.target]])
      producers[parent[d.target]] = Producer{false, i};
    definitions[i].constant = fastApproximate(d.constant);
    for (const auto& term : d.terms)
      definitions[i].terms.push_back(
          {parent[term.var], fastApproximate(term.coefficient)});
  }
  for (std::size_t i = 0; i < problem.relus.size(); ++i)
  {
    const auto& r = problem.relus[i];
    implied.insert(r.source.GetNodeNum());
    if (!producers[parent[r.post]])
      producers[parent[r.post]] = Producer{true, i};
  }
  std::vector<std::vector<std::size_t>> users(n);
  std::vector<std::size_t> pending(n, 0);
  std::deque<std::size_t> ready;
  std::size_t groups = 0;
  for (std::size_t v = 0; v < n; ++v)
  {
    if (parent[v] != v)
      continue;
    ++groups;
    std::unordered_set<std::size_t> dependencies;
    if (producers[v])
    {
      const auto p = *producers[v];
      if (p.relu)
        dependencies.insert(parent[problem.relus[p.index].pre]);
      else
        for (const auto& term : definitions[p.index].terms)
          dependencies.insert(term.var);
    }
    pending[v] = dependencies.size();
    for (const auto dependency : dependencies)
      users[dependency].push_back(v);
    if (dependencies.empty())
      ready.push_back(v);
  }
  while (!ready.empty())
  {
    const auto v = ready.front();
    ready.pop_front();
    order.push_back(v);
    for (const auto user : users[v])
      if (--pending[user] == 0)
        ready.push_back(user);
  }
  if (order.size() != groups)
    return; // cyclic graph

  // Cache just the remaining property predicates. Defining equations and
  // ReLUs are checked again by the exact witness verifier, even when this
  // approximate screen treats them as implied by forward replay.
  ASTVec todo{original};
  ASTNodeSet seen;
  bool supported = true;
  while (!todo.empty())
  {
    const auto node = todo.back();
    todo.pop_back();
    if (!seen.insert(node).second || implied.count(node.GetNodeNum()))
      continue;
    if (const auto row = problem.linearRow(node))
    {
      Predicate predicate;
      predicate.kind = node.GetKind();
      predicate.expression.constant = -fastApproximate(row->rhs);
      for (const auto& term : row->terms)
        predicate.expression.terms.push_back(
            {term.var, fastApproximate(term.coefficient)});
      predicates.emplace(node.GetNodeNum(), std::move(predicate));
    }
    else
    {
      const auto kind = node.GetKind();
      if (kind != TRUE && kind != FALSE && kind != AND && kind != OR &&
          kind != NOT && kind != XOR && kind != IFF && kind != IMPLIES &&
          kind != ITE)
        supported = false;
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    }
  }
  valid = problem.symbols.size() == n;
  complete_formula = valid && supported;
}

bool ReluReplayPlan::possible(
    ReluProblem& problem, const ASTNode& original,
    const std::vector<std::optional<ExactRational>>& inputs) const
{
  std::vector<double> values(parent.size(),
                             std::numeric_limits<double>::quiet_NaN());
  for (const auto v : order)
  {
    if (!producers[v])
    {
      values[v] = fastApproximate(*inputs[v]);
      continue;
    }
    const auto p = *producers[v];
    if (p.relu)
      values[v] = std::max(0.0, values[parent[problem.relus[p.index].pre]]);
    else
    {
      const auto& d = definitions[p.index];
      double value = d.constant;
      for (const auto& term : d.terms)
        value += term.coefficient * values[term.var];
      values[v] = value;
    }
  }
  // A two-bit set of possible truth values. Near a boundary or on a
  // nonfinite/unsupported expression, retain both choices. In particular,
  // NOT and strict predicates cannot turn a rounded boundary into a rejection.
  constexpr unsigned no = 1, yes = 2, either = 3;
  std::unordered_map<std::uint64_t, unsigned> truth;
  std::vector<std::pair<ASTNode, bool>> todo{{original, false}};
  auto combine = [](unsigned a, unsigned b, auto operation)
  {
    unsigned result = 0;
    for (unsigned x = 0; x < 2; ++x)
      for (unsigned y = 0; y < 2; ++y)
        if ((a & (1U << x)) && (b & (1U << y)))
          result |= 1U << static_cast<unsigned>(operation(x != 0, y != 0));
    return result;
  };
  while (!todo.empty())
  {
    const ASTNode node = todo.back().first;
    const bool visited = todo.back().second;
    todo.pop_back();
    const auto id = node.GetNodeNum();
    if (truth.count(id))
      continue;
    const auto kind = node.GetKind();
    if (implied.count(id) || kind == TRUE)
    {
      truth[id] = yes;
      continue;
    }
    if (kind == FALSE)
    {
      truth[id] = no;
      continue;
    }
    const auto pred = predicates.find(id);
    if (pred != predicates.end())
    {
      const auto& expression = pred->second.expression;
      double delta = expression.constant, scale = 1.0 + std::abs(delta);
      for (const auto& term : expression.terms)
      {
        const double addend = term.coefficient * values[parent[term.var]];
        delta += addend;
        scale += std::abs(addend);
      }
      unsigned result = either;
      if (std::isfinite(delta) && std::isfinite(scale) &&
          std::abs(delta) > 1e-8 * scale)
      {
        // linearRow orients every inequality as lhs <= rhs, including >/>=.
        result = pred->second.kind == EQ ? no : delta < 0 ? yes : no;
      }
      truth[id] = result;
      continue;
    }
    if (kind != AND && kind != OR && kind != NOT && kind != XOR &&
        kind != IFF && kind != IMPLIES && kind != ITE)
    {
      truth[id] = either;
      continue;
    }
    if (!visited)
    {
      todo.emplace_back(node, true);
      for (const auto& child : node.GetChildren())
        todo.emplace_back(child, false);
      continue;
    }
    auto child = [&](std::size_t i) { return truth.at(node[i].GetNodeNum()); };
    unsigned result = either;
    if (kind == AND || kind == OR || kind == XOR)
    {
      result = kind == AND ? yes : no;
      for (const auto& c : node.GetChildren())
        result = combine(
            result, truth.at(c.GetNodeNum()), [&](bool a, bool b)
            { return kind == AND  ? a && b
                     : kind == OR ? a || b
                                  : a != b; });
    }
    else if (kind == NOT && node.Degree() == 1)
      result = ((child(0) & no) << 1U) | ((child(0) & yes) >> 1U);
    else if ((kind == IFF || kind == IMPLIES) && node.Degree() == 2)
      result = combine(child(0), child(1), [&](bool a, bool b)
                       { return kind == IFF ? a == b : !a || b; });
    else if (kind == ITE && node.Degree() == 3)
      result = ((child(0) & yes) ? child(1) : 0U) |
               ((child(0) & no) ? child(2) : 0U);
    truth[id] = result;
  }
  return (truth.at(original.GetNodeNum()) & yes) != 0;
}
} // namespace stp::lra

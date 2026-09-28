#include "LraRelu.h"
#include <algorithm>
#include <unordered_set>

namespace stp::lra
{
void ReluProblem::propagateBooleanBounds()
{
  using Map = std::unordered_map<Var, Box>;
  struct Domain
  {
    Map box;
    bool empty = false;
  };
  std::unordered_set<std::uint64_t> relations;
  for (const auto& relu : relus)
    relations.insert(relu.source.GetNodeNum());
  std::size_t budget = 1000000;
  // This is interval abstract interpretation of the asserted Boolean DAG,
  // not activation of individual disjuncts. Any unsupported connective has
  // the unconstrained domain; it cannot contribute a conditional fact.
  for (const auto& conjunct : conjuncts)
  {
    if (conjunct.GetKind() != OR || relations.count(conjunct.GetNodeNum()))
      continue;
    std::unordered_map<std::uint64_t, Domain> memo;
    std::vector<std::pair<ASTNode, bool>> todo{{conjunct, false}};
    bool exhausted = false;
    auto spend = [&]()
    {
      if (budget == 0)
      {
        exhausted = true;
        return false;
      }
      --budget;
      return true;
    };
    while (!todo.empty() && !exhausted)
    {
      const auto [node, visited] = todo.back();
      todo.pop_back();
      if (memo.count(node.GetNodeNum()))
        continue;
      if (!spend())
        break;
      const auto kind = node.GetKind();
      if ((kind == AND || kind == OR) && !visited)
      {
        todo.emplace_back(node, true);
        for (const auto& child : node.GetChildren())
          todo.emplace_back(child, false);
        continue;
      }
      Domain result;
      if (kind == AND)
      {
        for (const auto& child : node.GetChildren())
        {
          const auto& domain = memo.at(child.GetNodeNum());
          if (domain.empty)
          {
            result.empty = true;
            break;
          }
          for (const auto& [var, b] : domain.box)
          {
            if (!spend())
              break;
            auto& current = result.box[var];
            if (b.lower && (!current.lower || *b.lower > *current.lower))
              current.lower = b.lower;
            if (b.upper && (!current.upper || *b.upper < *current.upper))
              current.upper = b.upper;
            if (current.lower && current.upper &&
                *current.lower > *current.upper)
              result.empty = true;
          }
        }
      }
      else if (kind == OR)
      {
        result.empty = true;
        for (const auto& child : node.GetChildren())
        {
          const auto& domain = memo.at(child.GetNodeNum());
          if (domain.empty)
            continue;
          if (result.empty)
          {
            for (const auto& entry : domain.box)
            {
              if (!spend())
                break;
              result.box.insert(entry);
            }
            result.empty = false;
            continue;
          }
          for (auto it = result.box.begin(); it != result.box.end();)
          {
            if (!spend())
              break;
            const auto other = domain.box.find(it->first);
            if (other == domain.box.end())
            {
              it = result.box.erase(it);
              continue;
            }
            auto& b = it->second;
            const auto& c = other->second;
            if (!c.lower)
              b.lower.reset();
            else if (b.lower && *c.lower < *b.lower)
              b.lower = c.lower;
            if (!c.upper)
              b.upper.reset();
            else if (b.upper && *c.upper > *b.upper)
              b.upper = c.upper;
            if (!b.lower && !b.upper)
              it = result.box.erase(it);
            else
              ++it;
          }
        }
      }
      else if (kind == FALSE)
        result.empty = true;
      else if (const auto row = linearRow(node))
      {
        if (row->terms.empty())
          result.empty =
              row->rhs.sign() < 0 || (row->equality && !row->rhs.isZero());
        else if (row->terms.size() == 1)
        {
          const auto& term = row->terms[0];
          if (!term.coefficient.isZero())
          {
            const auto value = row->rhs / term.coefficient;
            auto& b = result.box[term.var];
            if (row->equality || term.coefficient.sign() < 0)
              b.lower = value;
            if (row->equality || term.coefficient.sign() > 0)
              b.upper = value;
          }
        }
      }
      memo.emplace(node.GetNodeNum(), std::move(result));
    }
    if (exhausted)
      return; // do not publish a partially processed disjunction
    const auto& result = memo.at(conjunct.GetNodeNum());
    if (result.empty)
    {
      infeasible = true;
      return;
    }
    for (const auto& [var, box] : result.box)
    {
      if (box.lower && tighten(var, *box.lower, true))
        ++boolean_bound_updates;
      if (box.upper && tighten(var, *box.upper, false))
        ++boolean_bound_updates;
    }
  }
}
} // namespace stp::lra

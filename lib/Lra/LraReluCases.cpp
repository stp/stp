#include "LraReplay.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <chrono>
#include <iostream>

namespace stp::lra
{
namespace
{
using Rational = ExactRational;
using Var = ReluProblem::Var;
using Box = ReluProblem::Box;

struct Affine
{
  std::vector<Rational> coefficients;
  Rational constant;
};

Box range(const Affine& expression, const std::vector<Box>& box)
{
  Box result{expression.constant, expression.constant};
  for (std::size_t i = 0; i < box.size(); ++i)
  {
    const auto& c = expression.coefficients[i];
    if (c.isZero())
      continue;
    *result.lower += c * *(c.sign() > 0 ? box[i].lower : box[i].upper);
    *result.upper += c * *(c.sign() > 0 ? box[i].upper : box[i].lower);
  }
  return result;
}

bool manageable(const Rational& q)
{
  return q.numeratorBits() <= 2048 && q.denominatorBits() <= 2048;
}
} // namespace

void pruneReluCases(ReluProblem& problem, SATSolver* solver)
{
  auto& manager = problem.manager;
  if (problem.fixed() == problem.relus.size() ||
      manager.UserFlags.lra_relu_cases_seconds == 0)
    return;
  using Clock = std::chrono::steady_clock;
  const auto start = Clock::now();
  std::uint64_t work = 0;
  std::size_t checked = 0, closed = 0, cache_hits = 0;
  const auto expired = [&]()
  {
    return work >= 100000000 || checked >= 512 ||
           (solver && solver->timeLimitExpired()) ||
           std::chrono::duration<double>(Clock::now() - start).count() >=
               manager.UserFlags.lra_relu_cases_seconds;
  };
  struct Group
  {
    std::size_t index;
    ASTVec arms;
  };
  std::vector<Group> groups;
  std::unordered_set<std::uint64_t> relations;
  for (const auto& relu : problem.relus)
    relations.insert(relu.source.GetNodeNum());
  for (std::size_t i = 0; i < problem.conjuncts.size(); ++i)
  {
    const auto& node = problem.conjuncts[i];
    if (node.GetKind() != OR || relations.count(node.GetNodeNum()))
      continue;
    Group group{i, {}};
    ASTVec todo{node};
    bool candidate = false;
    while (!todo.empty())
    {
      if (++work >= 100000)
        return;
      const auto child = todo.back();
      todo.pop_back();
      if (child.GetKind() == OR)
        for (std::size_t j = child.Degree(); j > 0; --j)
          todo.push_back(child[j - 1]);
      else
      {
        group.arms.push_back(child);
        candidate = candidate || child.GetKind() == AND;
      }
    }
    if (candidate)
      groups.push_back(std::move(group));
  }
  if (groups.empty() || expired())
    return;
  const auto original = problem.conjuncts.size() == 1
                            ? problem.conjuncts[0]
                            : manager.CreateNode(AND, problem.conjuncts);
  // Only the topology is reused. Every equation and ReLU selected by this
  // plan is asserted at the root. Other asserted equations may be omitted:
  // that weakens the domain checked below, so a refutation remains valid.
  ReluReplayPlan plan(problem, original);
  if (!plan.valid)
    return;
  std::vector<Var> inputs;
  for (const auto v : plan.order)
    if (!plan.producers[v] &&
        !(problem.bounds[v].lower && problem.bounds[v].upper &&
          *problem.bounds[v].lower == *problem.bounds[v].upper))
      inputs.push_back(v);
  // Expanding a network in hundreds of inputs would recreate the dense
  // substitution cost this presolver avoids. This pass targets small boxes.
  if (inputs.empty() || inputs.size() > 4)
    return;
  const auto dimensions = inputs.size();
  std::vector<int> input_index(problem.symbols.size(), -1);
  for (std::size_t i = 0; i < dimensions; ++i)
    input_index[inputs[i]] = static_cast<int>(i);
  struct Atom
  {
    ReluProblem::Row row;
    bool strict;
  };
  std::unordered_map<std::uint64_t, std::optional<ReluProblem::Row>> row_cache;
  std::vector<Box> cached_box;
  std::vector<std::optional<Affine>> values;
  for (const auto& group : groups)
  {
    ASTVec retained;
    for (const auto& arm : group.arms)
    {
      if (expired() || arm.GetKind() != AND)
      {
        retained.push_back(arm);
        continue;
      }
      std::vector<Box> box;
      for (const auto input : inputs)
        box.push_back(problem.bounds[input]);
      std::vector<Atom> atoms;
      ASTVec todo{arm};
      bool empty = false, narrowed = false;
      while (!todo.empty() && !expired())
      {
        ++work;
        const auto node = todo.back();
        todo.pop_back();
        if (node.GetKind() == AND)
        {
          for (const auto& child : node.GetChildren())
            todo.push_back(child);
          continue;
        }
        if (node.GetKind() == FALSE)
          empty = true;
        auto found = row_cache.find(node.GetNodeNum());
        if (found == row_cache.end())
          found = row_cache.emplace(node.GetNodeNum(), problem.linearRow(node))
                      .first;
        if (!found->second)
          continue; // unsupported conjuncts cannot help refute this arm
        const auto& row = *found->second;
        atoms.push_back(
            {row, node.GetKind() == REAL_LT || node.GetKind() == REAL_GT});
        if (row.terms.size() != 1)
          continue;
        const auto& term = row.terms[0];
        const auto index = input_index[plan.parent[term.var]];
        if (index < 0 || term.coefficient.isZero())
          continue;
        auto& b = box[static_cast<std::size_t>(index)];
        const auto value = row.rhs / term.coefficient;
        if ((row.equality || term.coefficient.sign() < 0) &&
            (!b.lower || value > *b.lower))
        {
          b.lower = value;
          narrowed = true;
        }
        if ((row.equality || term.coefficient.sign() > 0) &&
            (!b.upper || value < *b.upper))
        {
          b.upper = value;
          narrowed = true;
        }
      }
      if (expired())
      {
        retained.push_back(arm);
        continue;
      }
      for (const auto& b : box)
        empty = empty || (b.lower && b.upper && *b.lower > *b.upper);
      if (empty)
      {
        ++checked;
        ++closed;
        continue;
      }
      if (!narrowed || std::any_of(box.begin(), box.end(), [](const Box& b)
                                   { return !b.lower || !b.upper; }))
      {
        retained.push_back(arm);
        continue;
      }
      // All endpoints above are conditional on this arm. No endpoint or
      // affine expression below is ever installed in the unconditional box.
      // Cache only the graph calculation for an identical input box. Output
      // predicates are checked afresh, and unfinished calculations are never
      // cached. One entry keeps storage independent of the number of arms.
      const bool same_box =
          cached_box.size() == box.size() &&
          std::equal(box.begin(), box.end(), cached_box.begin(),
                     [](const Box& a, const Box& b)
                     { return a.lower == b.lower && a.upper == b.upper; });
      if (same_box)
        ++cache_hits;
      else
      {
        cached_box.clear();
        values.assign(problem.symbols.size(), std::nullopt);
        for (const auto v : plan.order)
        {
          if (expired())
            break;
          Affine value{std::vector<Rational>(dimensions), Rational()};
          if (!plan.producers[v])
          {
            const auto index = input_index[v];
            if (index >= 0)
              value.coefficients[static_cast<std::size_t>(index)] =
                  Rational(std::int64_t{1});
            else
              value.constant = *problem.bounds[v].lower;
          }
          else if (const auto p = *plan.producers[v]; p.relu)
          {
            const auto pre = plan.parent[problem.relus[p.index].pre];
            if (!values[pre])
              continue;
            const auto b = range(*values[pre], box);
            if (b.lower->sign() >= 0)
              value = *values[pre];
            else if (b.upper->sign() > 0)
              continue; // a phase is still ambiguous in this particular box
          }
          else
          {
            const auto& definition = problem.definitions[p.index];
            value.constant = definition.constant;
            bool known = true;
            for (const auto& term : definition.terms)
            {
              work += dimensions + 1;
              const auto& source = values[plan.parent[term.var]];
              if (!source)
              {
                known = false;
                break;
              }
              value.constant += term.coefficient * source->constant;
              for (std::size_t i = 0; i < dimensions; ++i)
                if (!source->coefficients[i].isZero())
                  value.coefficients[i] +=
                      term.coefficient * source->coefficients[i];
            }
            if (!known)
              continue;
          }
          if (manageable(value.constant) &&
              std::all_of(value.coefficients.begin(), value.coefficients.end(),
                          manageable))
            values[v] = std::move(value);
        }
        if (!expired())
          cached_box = box;
      }
      if (expired())
      {
        retained.push_back(arm);
        continue;
      }
      ++checked;
      bool refuted = false;
      for (const auto& atom : atoms)
      {
        Affine value{std::vector<Rational>(dimensions), Rational()};
        bool known = true;
        for (const auto& term : atom.row.terms)
        {
          const auto& source = values[plan.parent[term.var]];
          if (!source)
          {
            known = false;
            break;
          }
          value.constant += term.coefficient * source->constant;
          for (std::size_t i = 0; i < dimensions; ++i)
            value.coefficients[i] += term.coefficient * source->coefficients[i];
        }
        if (!known)
          continue;
        const auto b = range(value, box);
        if ((atom.strict ? *b.lower >= atom.row.rhs
                         : *b.lower > atom.row.rhs) ||
            (atom.row.equality && *b.upper < atom.row.rhs))
        {
          refuted = true;
          break;
        }
      }
      if (refuted)
        ++closed;
      else
        retained.push_back(arm);
    }
    if (retained.empty())
    {
      problem.infeasible = true;
      break;
    }
    if (retained.size() < group.arms.size())
      problem.conjuncts[group.index] =
          retained.size() == 1 ? retained[0] : manager.CreateNode(OR, retained);
  }
  if (manager.UserFlags.stats_flag)
    std::cerr << "LRA ReLU cases: checked=" << checked << ", closed=" << closed
              << ", variable_inputs=" << dimensions
              << ", cache_hits=" << cache_hits << ", work=" << work
              << ", limited=" << expired() << ", seconds="
              << std::chrono::duration<double>(Clock::now() - start).count()
              << '\n';
}
} // namespace stp::lra

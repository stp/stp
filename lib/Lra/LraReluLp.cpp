#include "LraReconstruction.h"
#include "LraRelaxation.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>
#include <unordered_set>

namespace stp::lra
{
#ifdef STP_HAVE_HIGHS
namespace
{
using Facts = std::unordered_map<std::uint64_t, ASTNode>;
ASTNode rewrite(STPMgr& manager, const ASTNode& root, Facts& memo)
{
  std::vector<std::pair<ASTNode, bool>> todo{{root, false}};
  while (!todo.empty())
  {
    const auto [node, visited] = todo.back();
    todo.pop_back();
    if (memo.count(node.GetNodeNum()))
      continue;
    if (!visited)
    {
      todo.emplace_back(node, true);
      for (const auto& child : node.GetChildren())
        if (!memo.count(child.GetNodeNum()))
          todo.emplace_back(child, false);
      continue;
    }
    ASTVec children;
    bool changed = false;
    for (const auto& child : node.GetChildren())
    {
      const auto& replacement = memo.at(child.GetNodeNum());
      children.push_back(replacement);
      changed = changed || replacement != child;
    }
    memo.emplace(node.GetNodeNum(),
                 !changed ? node
                 : node.isRealTerm()
                     ? manager.CreateRealTerm(node.GetKind(), children)
                     : manager.CreateNode(node.GetKind(), children));
  }
  return memo.at(root.GetNodeNum());
}

bool useful(const std::optional<ExactRational>& old, const ExactRational& value,
            bool lower)
{
  if (!old)
    return true;
  const auto gain = lower ? value - *old : *old - value;
  if (gain.sign() <= 0)
    return false;
  // Always take a phase change, even at an arbitrarily small zero boundary.
  if ((lower && old->sign() < 0 && value.sign() >= 0) ||
      (!lower && old->sign() > 0 && value.sign() <= 0))
    return true;
  const auto magnitude = old->sign() < 0 ? -*old : *old;
  return gain > (ExactRational(std::int64_t{1}) + magnitude) /
                    ExactRational(std::int64_t{10000000});
}
} // namespace
#endif

void tightenReluRelaxation(ReluProblem& problem, SATSolver* solver, bool automatic)
{
#ifndef STP_HAVE_HIGHS
  (void)problem;
  (void)solver;
  (void)automatic;
  throw FrontendFailure(FrontendFailureKind::Unsupported,
                        "ReLU LP optimization requires ENABLE_HIGHS");
#else
  using Clock = std::chrono::steady_clock;
  const auto start = Clock::now();
  auto& manager = problem.manager;
  const double seconds = automatic
      ? std::min(manager.UserFlags.lra_relu_auto_seconds,
                 manager.UserFlags.lra_relu_lp_seconds)
      : manager.UserFlags.lra_relu_lp_seconds;
  const unsigned call_limit = automatic ? 16 : 2048;
  const unsigned round_limit = automatic ? 0 : manager.UserFlags.lra_relu_lp_rounds;
  auto remaining = [&]()
  {
    const double local =
        seconds -
        std::chrono::duration<double>(Clock::now() - start).count();
    return std::min(local, solver && solver->hasTimeLimit()
                               ? solver->secondsRemaining()
                               : local);
  };
  auto call_seconds = [&]()
  {
    return std::min<double>(manager.UserFlags.lra_relu_lp_call_seconds,
                            remaining());
  };
  auto witness_deadline = [&]()
  {
    return automatic
        ? Clock::now() + std::chrono::duration_cast<Clock::duration>(
              std::chrono::duration<double>(std::max(0.0, remaining())))
        : Clock::time_point::max();
  };
  struct Target
  {
    ASTNode atom;
    RelaxationRow row;
  };
  std::vector<Target> targets;
  std::unordered_set<std::uint64_t> seen;
  for (const auto& r : problem.relus)
    seen.insert(r.source.GetNodeNum());
  ASTVec todo;
  for (const auto& conjunct : problem.conjuncts)
    if (!problem.linearRow(conjunct))
      todo.push_back(conjunct);
  while (!todo.empty())
  {
    const auto node = todo.back();
    todo.pop_back();
    if (!seen.insert(node.GetNodeNum()).second)
      continue;
    const auto row = problem.linearRow(node);
    if (row)
      targets.push_back({node, *row});
    else
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
  }
  Facts facts;
  std::size_t calls = 0, certificates = 0, tightened = 0, rounds = 0;
  std::size_t screened = 0, partial = 0;
  double search_seconds = 0, certificate_seconds = 0;
  const ExactRational one(std::int64_t{1});
  const ExactRational grid(std::uint64_t{1} << 40);
  for (unsigned round = 0; round <= round_limit;
       ++round)
  {
    if (call_seconds() <= 0 || calls >= call_limit || problem.infeasible ||
        problem.satisfied)
      break;
    // This snapshot remains valid throughout the round. Rebuild the hulls
    // only after useful certified bounds have changed, retaining a warm LP
    // basis across objectives within a round.
    const auto complete_rows = problem.relaxation();
    auto rows = complete_rows;
    // Keep output/property inequalities for the feasibility probe. Bounds
    // use the network relaxation, which is substantially cheaper to optimize
    // repeatedly. Dropping an asserted row only weakens a certified bound.
    rows.erase(
        std::remove_if(rows.begin(),
                       rows.begin() +
                           static_cast<std::ptrdiff_t>(problem.rows.size()),
                       [](const RelaxationRow& row) { return !row.equality; }),
        rows.begin() + static_cast<std::ptrdiff_t>(problem.rows.size()));
    const auto box = problem.bounds;
    RelaxationLp lp(rows, box,
                    {manager.UserFlags.lra_lp_partial, std::nullopt});
    auto minimize = [&](const std::vector<RelaxationTerm>& objective,
                        std::optional<double> goal = std::nullopt)
    {
      if (calls >= call_limit || call_seconds() <= 0)
        return std::optional<ExactRational>{};
      ++calls;
      const double old_search = lp.search_seconds,
                   old_check = lp.certificate_seconds;
      const auto old_screened = lp.screened,
                 old_partial = lp.partial_certificates;
      auto bound =
          lp.minimize(objective, call_seconds(),
                      manager.UserFlags.lra_lp_screen ? goal : std::nullopt);
      search_seconds += lp.search_seconds - old_search;
      certificate_seconds += lp.certificate_seconds - old_check;
      screened += lp.screened - old_screened;
      partial += lp.partial_certificates - old_partial;
      if (bound)
        ++certificates;
      return bound;
    };
    for (const auto& target : targets)
    {
      if (remaining() <= 0 || calls >= call_limit)
        break;
      if (facts.count(target.atom.GetNodeNum()))
        continue;
      const auto lo = minimize(target.row.terms, approximate(target.row.rhs));
      const bool strict =
          target.atom.GetKind() == REAL_LT || target.atom.GetKind() == REAL_GT;
      if (lo && (*lo > target.row.rhs || (strict && *lo == target.row.rhs)))
      {
        facts.emplace(target.atom.GetNodeNum(), manager.ASTFalse);
        continue;
      }
      // A property objective supplies promising inputs. Replay those inputs
      // through exact affine/ReLU definitions and verify the complete source
      // formula; the floating assignment itself is never accepted as a model.
      if (remaining() > 0 &&
          tryReluWitness(problem, lp.values(), witness_deadline()))
        break;
      auto negated = target.row.terms;
      for (auto& term : negated)
        term.coefficient.negate();
      const auto negative_hi = minimize(negated, -approximate(target.row.rhs));
      if (!negative_hi)
        continue;
      const auto hi = -*negative_hi;
      if (target.row.equality)
      {
        if (hi < target.row.rhs)
          facts.emplace(target.atom.GetNodeNum(), manager.ASTFalse);
        else if (lo && *lo == target.row.rhs && hi == target.row.rhs)
          facts.emplace(target.atom.GetNodeNum(), manager.ASTTrue);
      }
      else if (strict ? hi < target.row.rhs : hi <= target.row.rhs)
        facts.emplace(target.atom.GetNodeNum(), manager.ASTTrue);
    }
    if (problem.satisfied)
      break;
    Facts memo = facts;
    for (const auto& conjunct : problem.conjuncts)
      if (rewrite(manager, conjunct, memo) == manager.ASTFalse)
        problem.infeasible = true;
    if (problem.infeasible)
      break;
    if (calls < call_limit && remaining() > 0)
    {
      ++calls;
      const auto probe =
          probeRelaxation(complete_rows, box, call_seconds(),
                          manager.UserFlags.lra_lp_partial);
      if (probe.refuted)
      {
        ++certificates;
        problem.infeasible = true;
        break;
      }
    }
    if (round == round_limit)
      break;
    const auto before = tightened;
    std::unordered_set<ReluProblem::Var> selected;
    for (const auto& relu : problem.relus)
    {
      const auto& b = box[relu.pre];
      if (!b.lower || !b.upper || b.lower->sign() >= 0 ||
          b.upper->sign() <= 0 || !selected.insert(relu.pre).second)
        continue;
      for (bool lower : {true, false})
      {
        if (remaining() <= 0)
          break;
        const double old =
            lower ? approximate(*b.lower) : -approximate(*b.upper);
        double goal = old + 1e-7 * (1.0 + std::abs(old));
        if (old < 0 && goal > 0)
          goal = 0; // retain even a tiny phase change
        const auto bound = minimize({{relu.pre, lower ? one : -one}}, goal);
        if (!bound)
          continue;
        // Round outwards onto a dyadic grid. This keeps repeated exact dual
        // residual checks small without strengthening the certified bound.
        const auto rounded_lower = (*bound * grid).floor() / grid;
        const auto value = lower ? rounded_lower : -rounded_lower;
        if (useful(lower ? b.lower : b.upper, value, lower) &&
            problem.tighten(relu.pre, value, lower))
          ++tightened;
      }
      if (problem.infeasible)
        break;
    }
    ++rounds;
    problem.propagate();
    if (tightened == before)
      break;
  }
  if (!problem.infeasible)
  {
    Facts memo = facts;
    for (auto& conjunct : problem.conjuncts)
      conjunct = rewrite(manager, conjunct, memo);
  }
  if (manager.UserFlags.stats_flag)
    std::cerr << "LRA ReLU LP: rounds=" << rounds << ", calls=" << calls
              << ", certificates=" << certificates << ", screened=" << screened
              << ", partial=" << partial << ", tightened=" << tightened
              << ", facts=" << facts.size()
              << ", infeasible=" << problem.infeasible
              << ", witness=" << problem.satisfied
              << ", automatic=" << automatic << ", call_limit=" << call_limit
              << ", budget_seconds=" << seconds
              << ", search_seconds=" << search_seconds
              << ", certificate_seconds=" << certificate_seconds << ", seconds="
              << std::chrono::duration<double>(Clock::now() - start).count()
              << '\n';
#endif
}
} // namespace stp::lra

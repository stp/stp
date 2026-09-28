#include "LraRelu.h"
#include "LraReconstruction.h"
#include "LraReplay.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <iostream>

namespace stp
{
namespace lra
{
namespace
{
bool symbol(const ASTNode& node)
{
  return node.GetKind() == SYMBOL && node.isRealTerm();
}

bool zero(const ASTNode& node)
{
  return node.GetKind() == REAL_CONST && node.GetRealNumerator() == "0";
}

bool guard(const ASTNode& atom, const ASTNode& pre, bool positive)
{
  if (atom.Degree() != 2)
    return false;
  const Kind forward = positive ? REAL_GE : REAL_LE;
  const Kind backward = positive ? REAL_LE : REAL_GE;
  return (atom.GetKind() == forward && atom[0] == pre && zero(atom[1])) ||
         (atom.GetKind() == backward && atom[1] == pre && zero(atom[0]));
}

// Deliberately require both closed guards and exactly two atoms per branch.
// In particular, a superficially similar disjunction with extra restrictions
// or two strict guards is not equivalent to max(0, pre).
bool recognize(const ASTNode& node, ASTNode& pre, ASTNode& post)
{
  if (node.GetKind() != OR || node.Degree() != 2)
    return false;
  for (std::size_t off = 0; off < 2; ++off)
  {
    const auto& a = node[off];
    const auto& b = node[1 - off];
    if (a.GetKind() != AND || b.GetKind() != AND || a.Degree() != 2 ||
        b.Degree() != 2)
      continue;
    for (std::size_t eq = 0; eq < 2; ++eq)
    {
      const auto& e = a[eq];
      if (e.GetKind() != EQ || e.Degree() != 2)
        continue;
      for (std::size_t side = 0; side < 2; ++side)
      {
        if (!symbol(e[side]) || !zero(e[1 - side]))
          continue;
        post = e[side];
        for (std::size_t on = 0; on < 2; ++on)
        {
          const auto& f = b[on];
          if (f.GetKind() != EQ || f.Degree() != 2)
            continue;
          if (f[0] == post && symbol(f[1]))
            pre = f[1];
          else if (f[1] == post && symbol(f[0]))
            pre = f[0];
          else
            continue;
          if (pre != post && guard(a[1 - eq], pre, false) &&
              guard(b[1 - on], pre, true))
            return true;
        }
      }
    }
  }
  return false;
}

// Most LRA queries contain no ReLUs. Inspect asserted conjuncts without
// normalizing arithmetic or consuming symbol identities. A bounded scan may
// decline AUTO; explicit ON retains the original unrestricted recognition.
bool automaticBoundsCandidate(const ASTNode& input)
{
  ASTVec todo{input};
  ASTNodeSet seen;
  bool found = false;
  while (!todo.empty() && seen.size() < 100000)
  {
    const auto node = todo.back();
    todo.pop_back();
    if (!seen.insert(node).second)
      continue;
    if (node.GetKind() == AND)
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    else
    {
      ASTNode pre, post;
      if (recognize(node, pre, post))
      {
        found = true;
        break;
      }
    }
  }
  if (!found)
    return false;
  // Bound construction normalizes affine equations. Do not start that work
  // automatically on a source DAG of unbounded size.
  todo = {input};
  seen.clear();
  while (!todo.empty())
  {
    const auto node = todo.back();
    todo.pop_back();
    if (!seen.insert(node).second)
      continue;
    if (seen.size() > 200000)
      return false;
    for (const auto& child : node.GetChildren())
      todo.push_back(child);
  }
  return true;
}

#ifdef STP_HAVE_HIGHS
// A Real assignment cannot by itself check a named Boolean guard. Check the
// Boolean shape first; the replay plan subsequently checks affine predicates,
// symbol coverage and acyclicity. No guard is assumed true or discarded.
bool realWitnessShape(const ASTNode& input)
{
  ASTVec todo{input};
  ASTNodeSet seen;
  while (!todo.empty())
  {
    const auto node = todo.back();
    todo.pop_back();
    if (!seen.insert(node).second)
      continue;
    if (seen.size() > 100000)
      return false;
    const auto kind = node.GetKind();
    if (kind == TRUE || kind == FALSE)
      continue;
    if (node.Degree() == 2 && node[0].isRealTerm() && node[1].isRealTerm() &&
        (kind == EQ || kind == REAL_LT || kind == REAL_LE ||
         kind == REAL_GT || kind == REAL_GE))
      continue;
    if (kind != AND && kind != OR && kind != NOT && kind != XOR &&
        kind != IFF && kind != IMPLIES && kind != ITE)
      return false;
    for (const auto& child : node.GetChildren())
      todo.push_back(child);
  }
  return true;
}

bool automaticWitnessCandidate(ReluProblem& problem, const ASTNode& input)
{
  if (!realWitnessShape(input))
    return false;
  problem.replay_plan = std::make_shared<ReluReplayPlan>(problem, input);
  const auto& plan = *problem.replay_plan;
  if (!plan.complete_formula)
    return false;
  for (const auto v : plan.order)
    if (!plan.producers[v] &&
        (!problem.bounds[v].lower || !problem.bounds[v].upper))
      return false;
  return true;
}
#endif

ASTNode number(STPMgr& manager, const ExactRational& value)
{
  return manager.CreateRealConst(value.canonicalFraction());
}
} // namespace

ReluProblem::Var ReluProblem::variable(const ASTNode& node)
{
  const auto found = ids_.find(node.GetNodeNum());
  if (found != ids_.end())
    return found->second;
  const Var id = symbols.size();
  ids_.emplace(node.GetNodeNum(), id);
  symbols.push_back(node);
  bounds.emplace_back();
  uses_.emplace_back();
  return id;
}

std::optional<ReluProblem::Row> ReluProblem::linearRow(const ASTNode& atom)
{
  if (atom.Degree() != 2 || !atom[0].isRealTerm() || !atom[1].isRealTerm())
    return std::nullopt;
  const Kind kind = atom.GetKind();
  if (kind != EQ && kind != REAL_LE && kind != REAL_LT && kind != REAL_GE &&
      kind != REAL_GT)
    return std::nullopt;
  try
  {
    const auto normalized = frontend_.normalizePredicate(atom);
    const auto& polynomial = normalized.canonical.lhs_minus_rhs;
    // The frontend normalizes the sign as well as the coefficients.
    const auto relation = normalized.canonical.relation;
    const bool flip = relation == FrontendRelation::Greater ||
                      relation == FrontendRelation::GreaterEqual;
    Row row;
    row.equality = relation == FrontendRelation::Equal;
    row.rhs = flip ? polynomial.constant : -polynomial.constant;
    for (const auto& term : polynomial.terms)
      row.terms.push_back({variable(frontend_.symbolNode(term.symbol)),
                           flip ? -term.coefficient : term.coefficient});
    return row;
  }
  catch (const FrontendFailure& failure)
  {
    if (failure.kind() != FrontendFailureKind::Unsupported)
      throw;
    return std::nullopt;
  }
}

ReluProblem::ReluProblem(STPMgr& mgr, const ASTNode& input)
    : manager(mgr), frontend_(mgr)
{
  ASTVec todo{input};
  while (!todo.empty())
  {
    const auto node = todo.back();
    todo.pop_back();
    if (node.GetKind() == AND)
      for (std::size_t i = node.Degree(); i > 0; --i)
        todo.push_back(node[i - 1]);
    else
      conjuncts.push_back(node);
  }
  for (const auto& node : conjuncts)
  {
    ASTNode pre, post;
    if (recognize(node, pre, post))
      relus.push_back({variable(pre), variable(post), node});
  }
  if (relus.empty())
    return;
  for (const auto& node : conjuncts)
  {
    const auto row = linearRow(node);
    if (!row)
      continue;
    rows.push_back(*row);
    if (row->terms.empty())
    {
      if (row->rhs.sign() < 0 || (row->equality && !row->rhs.isZero()))
        infeasible = true;
    }
    else if (row->terms.size() == 1)
    {
      const auto& term = row->terms[0];
      const auto value = row->rhs / term.coefficient;
      tighten(term.var, value, term.coefficient.sign() < 0);
      if (row->equality)
        tighten(term.var, value, term.coefficient.sign() > 0);
    }
    if (!row->equality)
      continue;
    for (std::size_t side = 0; side < 2; ++side)
    {
      if (!symbol(node[side]))
        continue;
      const Var target = variable(node[side]);
      // A syntactic definition must not mention its target on the RHS.
      const auto rhs = frontend_.normalize(node[1 - side]);
      Definition definition{target, {}, rhs.constant, node};
      bool cyclic = false;
      for (const auto& term : rhs.terms)
      {
        const Var id = variable(frontend_.symbolNode(term.symbol));
        cyclic = cyclic || id == target;
        definition.terms.push_back({id, term.coefficient});
      }
      if (!cyclic)
        definitions.push_back(std::move(definition));
      // Equality factories can reorder two symbols. Propagate aliases both
      // ways, so x = input works regardless of that canonical operand order.
      if (!symbol(node[1 - side]))
        break;
    }
  }
  if (manager.UserFlags.lra_boolean_bounds)
    propagateBooleanBounds();
  const std::size_t count = definitions.size() + relus.size();
  queued_.assign(count, true);
  for (std::size_t i = 0; i < count; ++i)
    pending_.push_back(i);
  for (std::size_t i = 0; i < definitions.size(); ++i)
    for (const auto& term : definitions[i].terms)
      uses_[term.var].push_back(i);
  for (std::size_t i = 0; i < relus.size(); ++i)
  {
    uses_[relus[i].pre].push_back(definitions.size() + i);
    uses_[relus[i].post].push_back(definitions.size() + i);
  }
}

void ReluProblem::enqueue(Var var)
{
  for (const auto id : uses_[var])
    if (!queued_[id])
    {
      queued_[id] = true;
      pending_.push_back(id);
    }
}

bool ReluProblem::tighten(Var var, const ExactRational& value, bool lower)
{
  if (value.numeratorBits() > 2048 || value.denominatorBits() > 2048)
  {
    limited = true;
    return false;
  }
  auto& box = bounds[var];
  auto& old = lower ? box.lower : box.upper;
  if (old && (lower ? value <= *old : value >= *old))
    return false;
  old = value;
  ++updates;
  if (box.lower && box.upper && *box.lower > *box.upper)
    infeasible = true;
  enqueue(var);
  return true;
}

void ReluProblem::propagate(std::uint64_t budget)
{
  const ExactRational nil;
  // Cyclic definitions can improve forever. Retain the facts proved so far
  // and leave the remaining work to ordinary solving when this budget ends.
  while (!pending_.empty() && !infeasible && work < budget)
  {
    const auto id = pending_.front();
    pending_.pop_front();
    queued_[id] = false;
    ++work;
    if (id < definitions.size())
    {
      const auto& definition = definitions[id];
      std::optional<ExactRational> lo = definition.constant, hi = lo;
      for (const auto& term : definition.terms)
      {
        ++work;
        const auto& b = bounds[term.var];
        const auto& a = term.coefficient.sign() > 0 ? b.lower : b.upper;
        const auto& z = term.coefficient.sign() > 0 ? b.upper : b.lower;
        if (lo && a)
          *lo += term.coefficient * *a;
        else
          lo.reset();
        if (hi && z)
          *hi += term.coefficient * *z;
        else
          hi.reset();
      }
      if (lo)
        tighten(definition.target, *lo, true);
      if (hi)
        tighten(definition.target, *hi, false);
    }
    else
    {
      const auto& relu = relus[id - definitions.size()];
      // Copy: tightening can change either endpoint referenced below.
      const Box pre = bounds[relu.pre], post = bounds[relu.post];
      tighten(relu.post, pre.lower ? std::max(nil, *pre.lower) : nil, true);
      if (pre.upper)
        tighten(relu.post, std::max(nil, *pre.upper), false);
      if (post.upper)
        tighten(relu.pre, *post.upper, false);
      if (post.lower && post.lower->sign() > 0)
        tighten(relu.pre, *post.lower, true);
    }
  }
  limited = limited || (!pending_.empty() && !infeasible);
}

std::size_t ReluProblem::fixed() const
{
  return static_cast<std::size_t>(
      std::count_if(relus.begin(), relus.end(),
                    [&](const Relu& r)
                    {
                      const auto& b = bounds[r.pre];
                      return (b.upper && b.upper->sign() <= 0) ||
                             (b.lower && b.lower->sign() >= 0);
                    }));
}

std::vector<ReluProblem::Row> ReluProblem::relaxation() const
{
  std::vector<Row> result = rows;
  const ExactRational one(std::int64_t{1}), nil;
  for (const auto& r : relus)
  {
    const auto& b = bounds[r.pre];
    if (b.upper && b.upper->sign() <= 0)
      result.push_back({{{r.post, one}}, nil, true});
    else if (b.lower && b.lower->sign() >= 0)
      result.push_back({{{r.post, one}, {r.pre, -one}}, nil, true});
    else
    {
      result.push_back({{{r.post, -one}}, nil, false});
      result.push_back({{{r.pre, one}, {r.post, -one}}, nil, false});
      if (b.lower && b.upper)
      {
        // Multiply the triangle by its positive width. Forming a rational
        // slope introduces one unrelated denominator per ReLU; summing dual
        // rows then builds a huge least common multiple in the exact checker.
        // This equivalent row retains the input endpoints' denominators.
        const auto width = *b.upper - *b.lower;
        result.push_back({{{r.post, width}, {r.pre, -*b.upper}},
                          -*b.upper * *b.lower,
                          false});
      }
    }
  }
  return result;
}

ASTNode ReluProblem::formula()
{
  if (satisfied)
    return manager.ASTTrue;
  if (infeasible)
    return manager.ASTFalse;
  if (relus.empty())
    return manager.CreateNode(AND, conjuncts);
  ASTVec result;
  std::unordered_map<std::uint64_t, ASTNode> replacements;
  const auto nil = manager.CreateRealConst("0");
  for (const auto& r : relus)
  {
    const auto& b = bounds[r.pre];
    if (b.upper && b.upper->sign() <= 0)
      replacements.emplace(r.source.GetNodeNum(),
                           manager.CreateNode(EQ, symbols[r.post], nil));
    else if (b.lower && b.lower->sign() >= 0)
      replacements.emplace(
          r.source.GetNodeNum(),
          manager.CreateNode(EQ, symbols[r.post], symbols[r.pre]));
  }
  for (const auto& node : conjuncts)
  {
    const auto found = replacements.find(node.GetNodeNum());
    result.push_back(found == replacements.end() ? node : found->second);
  }
  for (Var v = 0; v < symbols.size(); ++v)
  {
    const auto& b = bounds[v];
    if (b.lower)
      result.push_back(
          manager.CreateNode(REAL_GE, symbols[v], number(manager, *b.lower)));
    if (b.upper)
      result.push_back(
          manager.CreateNode(REAL_LE, symbols[v], number(manager, *b.upper)));
  }
  // Keep affine antecedents conjoined. All added rows therefore have their
  // explanations in the submitted query, including after push/pop or UF
  // refinement. No branch-local reasoning is published here.
  auto relaxed = relaxation();
  for (std::size_t i = rows.size(); i < relaxed.size(); ++i)
  {
    const auto& row = relaxed[i];
    if (row.equality)
      continue; // the corresponding phase was replaced above
    ASTVec terms;
    for (const auto& term : row.terms)
      terms.push_back(manager.CreateRealTerm(
          REAL_MUL,
          ASTVec{number(manager, term.coefficient), symbols[term.var]}));
    const auto lhs =
        terms.size() == 1 ? terms[0] : manager.CreateRealTerm(REAL_ADD, terms);
    result.push_back(
        manager.CreateNode(REAL_LE, lhs, number(manager, row.rhs)));
  }
  result.insert(result.end(), lemmas.begin(), lemmas.end());
  return manager.CreateNode(AND, result);
}

ASTNode presolveRelus(STPMgr& manager, const ASTNode& input, bool& recognized,
                      SATSolver* solver, LraReconstruction* reconstruction)
{
  using Mode = UserDefinedFlags::OptionMode;
  const auto& flags = manager.UserFlags;
  // Explicit later stages still imply their prerequisite bounds, as before.
  // bounds=off vetoes automatic LP selection, not an explicit lp/cases/branch.
  const bool forced = flags.lra_relu_bounds == Mode::ON ||
                      flags.lra_relu_lp == Mode::ON ||
                      flags.lra_relu_cases || flags.lra_relu_branch;
  if (!forced && (flags.lra_relu_bounds == Mode::OFF ||
                  !automaticBoundsCandidate(input)))
    return input;
  ReluProblem problem(manager, input);
  if (problem.relus.empty())
    return input;
  problem.propagate(forced ? 8000000 : 200000);
  if (!forced && problem.limited)
  {
    if (flags.stats_flag)
      std::cerr << "LRA ReLU auto: bounds_limit=1, lp=0, reconstruction=0\n";
    return input; // retain ordinary substitution when AUTO did not finish
  }
  recognized = true;
  bool automatic_lp = false;
  bool auto_reconstruction = false;
#ifdef STP_HAVE_HIGHS
  const bool lp_budget = flags.lra_relu_lp_seconds != 0 &&
                         flags.lra_relu_lp_call_seconds != 0;
  const bool proposal_requested =
      (lp_budget && (flags.lra_relu_lp == Mode::ON ||
                    (flags.lra_relu_lp == Mode::AUTO &&
                     flags.lra_relu_auto_seconds != 0))) ||
      flags.lra_relu_branch;
  const ASTNode& witness_source =
      reconstruction && reconstruction->replay_selected
          ? reconstruction->original : input;
  if (reconstruction && reconstruction->replay_allowed &&
      flags.lra_model_reconstruction != Mode::OFF &&
      proposal_requested && !problem.infeasible && !problem.limited &&
      automaticWitnessCandidate(problem, witness_source))
  {
    automatic_lp = flags.lra_relu_lp == Mode::AUTO && lp_budget &&
                   flags.lra_relu_auto_seconds != 0;
    auto_reconstruction = flags.lra_model_reconstruction == Mode::AUTO;
    if (auto_reconstruction)
    {
      if (reconstruction->original.IsNull())
        reconstruction->original = input;
      reconstruction->replay_selected = true;
      reconstruction->eliminate_definitions = true;
    }
  }
#endif
  if (reconstruction && flags.lra_model_reconstruction != Mode::OFF &&
      reconstruction->replay_selected)
    problem.reconstruction = reconstruction;
  const bool lp = flags.lra_relu_lp == Mode::ON || automatic_lp;
  if (flags.stats_flag)
    std::cerr << "LRA ReLU policy: lp=" << lp
              << ", automatic_lp=" << automatic_lp
              << ", reconstruction=" << (problem.reconstruction != nullptr)
              << ", automatic_reconstruction=" << auto_reconstruction << '\n';
  if (manager.UserFlags.lra_relu_cases && !problem.infeasible)
    pruneReluCases(problem, solver);
  if (lp && !problem.infeasible)
    tightenReluRelaxation(problem, solver, automatic_lp);
  if (manager.UserFlags.lra_relu_branch && !problem.infeasible &&
      !problem.satisfied)
    branchReluRelaxation(problem, solver);
  if (manager.UserFlags.stats_flag)
    std::cerr << "LRA ReLU: relations=" << problem.relus.size()
              << ", fixed=" << problem.fixed()
              << ", updates=" << problem.updates << ", work=" << problem.work
              << ", limited=" << problem.limited
              << ", boolean_bounds=" << problem.boolean_bound_updates
              << ", infeasible=" << problem.infeasible << ", replay_attempts="
              << (reconstruction ? reconstruction->replay_attempts : 0)
              << ", replay_screened="
              << (reconstruction ? reconstruction->replay_screened : 0)
              << ", replay_seconds="
              << (reconstruction ? reconstruction->replay_seconds : 0) << '\n';
  return problem.formula();
}
} // namespace lra
} // namespace stp

#include "stp/UninterpretedFunctions/UFSearchPropagator.h"
#include <algorithm>

namespace stp
{

UFSearchPropagator::~UFSearchPropagator()
{
  if (solver_ != nullptr)
    solver_->disconnectTheoryPropagator();
}

bool UFSearchPropagator::addBits(
    const ASTNode& leaf, std::vector<Bit>& bits,
    const ToSATBase::ASTNodeToSATVar& bindings, SATSolver& solver)
{
  const unsigned width = std::max(1u, leaf.GetValueWidth());
  if (leaf.isConstant())
  {
    if (leaf.GetKind() != TRUE && leaf.GetKind() != FALSE &&
        leaf.GetKind() != BVCONST)
      return false;
    for (unsigned bit = 0; bit < width; ++bit)
    {
      Bit item;
      item.constantValue = leaf.GetKind() == TRUE ||
                           (leaf.GetKind() == BVCONST &&
                            CONSTANTBV::BitVector_bit_test(leaf.GetBVConst(),
                                                           bit) != 0);
      bits.push_back(item);
    }
    return true;
  }
  if (leaf.GetKind() != SYMBOL)
    return false;
  const auto found = bindings.find(leaf);
  if (found == bindings.end() || found->second.size() != width)
    return false;
  for (uint32_t variable : found->second)
  {
    if (!solver.validVariable(variable))
      return false;
    Bit item;
    item.variable = variable;
    bits.push_back(item);
  }
  return true;
}

bool UFSearchPropagator::prepare(
    const LoweredApplicationView& view,
    const ToSATBase::ASTNodeToSATVar& bindings, SATSolver& solver,
    std::vector<uint32_t>& observed)
{
  argumentUses_.resize(static_cast<size_t>(solver.nVars()) + 1);
  resultUses_.resize(argumentUses_.size());
  assignments_.resize(argumentUses_.size(), 0);

  for (const LoweredApplicationRecord& record : view.applications)
  {
    if (!record.observableArguments)
      continue;
    if (record.declaration == nullptr ||
        record.namedActuals.size() !=
            record.declaration->signature().arity() ||
        record.resultSymbol.GetKind() != SYMBOL)
      return false;

    Application app;
    app.key.first = record.declaration->id();
    for (const ASTNode& actual : record.namedActuals)
      if (!addBits(actual, app.arguments, bindings, solver))
        return false;
    if (!addBits(record.resultSymbol, app.result, bindings, solver))
      return false;
    if (app.result.empty())
      return false;

    const size_t id = applications_.size();
    for (const Bit& bit : app.arguments)
      if (bit.variable != 0)
      {
        argumentUses_[bit.variable].push_back(id);
        ++app.remaining;
      }
    for (const Bit& bit : app.result)
      if (bit.variable != 0)
        resultUses_[bit.variable].push_back({id});
    applications_.push_back(std::move(app));
  }

  for (size_t id = 0; id < applications_.size(); ++id)
    if (applications_[id].remaining == 0)
      insertReady(id);
  for (uint32_t variable = 1; variable < assignments_.size(); ++variable)
    if (!argumentUses_[variable].empty() || !resultUses_[variable].empty())
      observed.push_back(variable);
  return !applications_.empty() && !observed.empty();
}

bool UFSearchPropagator::connect(
    SATSolver& solver, const LoweredApplicationView& view,
    const ToSATBase::ASTNodeToSATVar& bindings)
{
  if (solver_ != nullptr)
    return solver_ == &solver;
  if (attempted_)
    return false;
  attempted_ = true;
  if (!solver.supportsTheoryPropagator())
    return false;
  try
  {
    std::vector<uint32_t> observed;
    if (!prepare(view, bindings, solver, observed))
    {
      diagnostic_ = "UF search setup could not bind every application";
      return false;
    }
    if (!solver.connectTheoryPropagator(this, observed))
    {
      diagnostic_ = "SAT backend declined the UF search propagator";
      return false;
    }
    solver_ = &solver;
    return true;
  }
  catch (...)
  {
    diagnostic_ = "unexpected failure setting up UF search propagation";
    return false;
  }
}

int UFSearchPropagator::value(const Bit& bit) const
{
  if (bit.variable == 0)
    return bit.constantValue ? 1 : -1;
  return assignments_[bit.variable];
}

UFSearchPropagator::Key
UFSearchPropagator::keyFor(const Application& app) const
{
  Key key;
  key.first = app.key.first;
  key.second.reserve(app.arguments.size());
  for (const Bit& bit : app.arguments)
    key.second.push_back(value(bit) > 0 ? '1' : '0');
  return key;
}

void UFSearchPropagator::insertReady(size_t id)
{
  Application& app = applications_[id];
  app.key = keyFor(app);
  auto& bucket = buckets_[app.key];
  app.position = bucket.size();
  bucket.push_back(id);
  app.ready = true;
}

void UFSearchPropagator::removeReady(size_t id)
{
  Application& app = applications_[id];
  auto found = buckets_.find(app.key);
  if (found == buckets_.end())
  {
    fail("UF search bucket disappeared during backtrack");
    return;
  }
  auto& bucket = found->second;
  const size_t moved = bucket.back();
  bucket[app.position] = moved;
  applications_[moved].position = app.position;
  bucket.pop_back();
  if (bucket.empty())
    buckets_.erase(found);
  app.ready = false;
}

void UFSearchPropagator::appendPremises(
    const Application& app, std::vector<SATSolver::Lit>& clause) const
{
  for (const Bit& bit : app.arguments)
    if (bit.variable != 0)
      clause.push_back(SATSolver::mkLit(bit.variable,
                                       assignments_[bit.variable] > 0));
}

bool UFSearchPropagator::conflict(size_t left, size_t right)
{
  const Application& a = applications_[left];
  const Application& b = applications_[right];
  if (a.result.size() != b.result.size())
  {
    fail("UF search result widths disagree within a declaration");
    return false;
  }
  for (size_t bit = 0; bit < a.result.size(); ++bit)
  {
    const int av = value(a.result[bit]);
    const int bv = value(b.result[bit]);
    if (av == 0 || bv == 0 || av == bv)
      continue;

    // The argument tuples are fully assigned and equal in this bucket.
    // Falsifying every literal below would make those tuples equal again
    // while fixing opposite values for one result bit, which congruence
    // forbids. The clause remains valid after this trail backtracks.
    std::vector<SATSolver::Lit> clause;
    clause.reserve(a.arguments.size() + b.arguments.size() + 2);
    appendPremises(a, clause);
    appendPremises(b, clause);
    clause.push_back(SATSolver::mkLit(a.result[bit].variable, av > 0));
    clause.push_back(SATSolver::mkLit(b.result[bit].variable, bv > 0));
    std::sort(clause.begin(), clause.end(),
              [](SATSolver::Lit x, SATSolver::Lit y) { return x.x < y.x; });
    clause.erase(std::unique(clause.begin(), clause.end(),
                             [](SATSolver::Lit x, SATSolver::Lit y) {
                               return x.x == y.x;
                             }),
                 clause.end());
    pending_ = std::move(clause);
    ++conflicts_;
    return true;
  }
  return false;
}

bool UFSearchPropagator::inspect(size_t id)
{
  const Application& app = applications_[id];
  if (!app.ready)
    return false;
  const auto found = buckets_.find(app.key);
  if (found == buckets_.end())
  {
    fail("UF search ready application has no bucket");
    return false;
  }
  for (size_t other : found->second)
    if (other != id && conflict(id, other))
      return true;
  return false;
}

void UFSearchPropagator::fail(const char* reason)
{
  failed_ = true;
  diagnostic_ = reason;
  pending_.clear();
}

void UFSearchPropagator::notifyAssigned(
    const std::vector<SATSolver::Lit>& literals)
{
  if (failed_)
    return;
  try
  {
    std::vector<size_t> touched;
    for (SATSolver::Lit literal : literals)
    {
      const uint32_t variable = SATSolver::var(literal);
      if (variable >= assignments_.size())
        continue; // a retained decision hint observed before connection
      const int8_t assigned = SATSolver::sign(literal) ? -1 : 1;
      if (assignments_[variable] == assigned)
        continue;
      if (assignments_[variable] != 0)
      {
        fail("UF search saw contradictory SAT assignments");
        return;
      }
      assignments_[variable] = assigned;
      trail_.push_back(variable);
      for (size_t id : argumentUses_[variable])
      {
        Application& app = applications_[id];
        if (app.remaining == 0)
        {
          fail("UF search argument count underflowed");
          return;
        }
        if (--app.remaining == 0)
        {
          insertReady(id);
          touched.push_back(id);
        }
      }
      for (const ResultUse& use : resultUses_[variable])
        if (applications_[use.application].ready)
          touched.push_back(use.application);
    }
    if (pending_.empty())
      for (size_t id : touched)
        if (inspect(id) || failed_)
          break;
  }
  catch (...)
  {
    fail("unexpected failure tracking UF search assignments");
  }
}

void UFSearchPropagator::notifyNewLevel()
{
  if (failed_)
    return;
  try
  {
    levelMarks_.push_back(trail_.size());
  }
  catch (...)
  {
    fail("unexpected failure opening a UF search level");
  }
}

void UFSearchPropagator::notifyBacktrack(size_t level)
{
  if (failed_)
    return;
  try
  {
    pending_.clear();
    while (levelMarks_.size() > level + 1)
    {
      const size_t mark = levelMarks_.back();
      levelMarks_.pop_back();
      while (trail_.size() > mark)
      {
        const uint32_t variable = trail_.back();
        trail_.pop_back();
        for (size_t id : argumentUses_[variable])
        {
          Application& app = applications_[id];
          if (app.remaining == 0)
            removeReady(id);
          ++app.remaining;
        }
        assignments_[variable] = 0;
      }
    }
  }
  catch (...)
  {
    fail("unexpected failure backtracking UF search assignments");
  }
}

bool UFSearchPropagator::checkFoundModel()
{
  if (failed_)
    return true;
  try
  {
    if (!pending_.empty())
      return false;
    for (size_t id = 0; id < applications_.size(); ++id)
      if (inspect(id))
        return false;
    return true;
  }
  catch (...)
  {
    fail("unexpected failure checking a UF search model");
    return true;
  }
}

bool UFSearchPropagator::takeClause(std::vector<SATSolver::Lit>& clause)
{
  if (failed_ || pending_.empty())
    return false;
  clause.swap(pending_);
  return true;
}

} // namespace stp

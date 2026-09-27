/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

// Model.cpp -- the detached model snapshot, the evaluator over it, and the
// Model / ArrayValue / FunctionValue value types.

#include "Internal.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/literal_fp.h"
#include "stp/Globals/Globals.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/UninterpretedFunctions/UFChecker.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"

#include <algorithm>
#include <ostream>
#include <set>
#include <sstream>

namespace stp
{
namespace api
{
namespace detail
{

ASTNode rebuild_node(ManagerImpl* m, NodeFactory* f, const ASTNode& n, const ASTVec& kids);

ModelSnapshot::~ModelSnapshot()
{
  scalars.clear();
  arrays.clear();
  functions.clear();
  core.clear();
  if (mgr != nullptr)
    mgr->release();
}

// A function over Reals, in its codomain or an argument: its values are not
// bit-carried, so the certified seed cannot table it.
bool involves_real(const UFSignature& sig)
{
  if (sig.codomain().kind() == SourceSort::Kind::Real)
    return true;
  for (const SourceSort& d : sig.domain())
    if (d.kind() == SourceSort::Kind::Real)
      return true;
  return false;
}

bool index_before(const ASTNode& a, const ASTNode& b)
{
  return CONSTANTBV::BitVector_Lexicompare(a.GetBVConst(), b.GetBVConst()) < 0;
}

// The fill value of an array's unobserved cells under the model's fill rule.
ASTNode fill_value(ManagerImpl* m, std::uint32_t array_sort, bool ones, const char* fn)
{
  const SortRec& r = m->rec(array_sort);
  const SortRec& e = m->rec(r.element);
  if (ones && e.kind == SortKind::BV)
    return m->bm->CreateMaxConst(e.a);
  return m->default_value(r.element, fn);
}

ASTNode lift(ManagerImpl* m, const ASTNode& carrier, const SourceSort& sort)
{
  if (carrier.IsNull() || !carrier.isConstant())
    return carrier;
  if (sort.kind() == SourceSort::Kind::FloatingPoint || sort.kind() == SourceSort::Kind::RoundingMode)
  {
    if (carrier.GetKind() == BVCONST && carrier.GetValueWidth() == sort.packedWidth())
      return m->bm->LiftSourceValue(carrier, sort);
  }
  if (sort.kind() == SourceSort::Kind::Uninterpreted && carrier.GetKind() == BVCONST &&
      carrier.GetValueWidth() == sort.packedWidth() &&
      carrier.GetSourceSort().kind() != SourceSort::Kind::Uninterpreted)
    return m->bm->CreateUninterpretedConst(carrier, sort);
  return carrier;
}

std::shared_ptr<const ModelSnapshot> SolverImpl::take_snapshot(Verdict v)
{
  auto snap = std::make_shared<ModelSnapshot>();
  snap->mgr = mgr;
  mgr->retain();
  snap->verdict = v;
  snap->fill_ones = fill_ones;
  STPMgr* bm = mgr->bm;
  GlobalParserBM = bm;
  if (stp->hasIncrementalSolver())
    stp->getIncrementalSolver()->materializePendingModel();
  AbsRefine_CounterExample* ce = stp->Ctr_Example;
  const ASTNodeMap raw = ce->GetCompleteCounterExample();
  const char* fn = "Solver::model";

  std::set<ASTNode> arrays_seen;
  for (const auto& entry : raw)
  {
    const ASTNode& key = entry.first;
    if (key.GetKind() == READ)
    {
      if (key[0].GetKind() == SYMBOL && !bm->FoundIntroducedSymbolSet(key[0]) &&
          key[1].isConstant())
        arrays_seen.insert(key[0]);
      continue;
    }
    if (key.GetKind() != SYMBOL || bm->FoundIntroducedSymbolSet(key))
      continue;
    if (mgr->is_const_array(key) || mgr->decl_of(key) != nullptr)
      continue;
    const SourceSort ss = key.GetSourceSort();
    if (!ss.isKnown() || ss.kind() == SourceSort::Kind::Real)
      continue;
    if (ss.kind() == SourceSort::Kind::Array)
    {
      arrays_seen.insert(key);
      continue;
    }
    if (ss.kind() == SourceSort::Kind::Unknown)
      continue;
    const ASTNode value = lift(mgr, ce->GetCounterExample(key), ss);
    if (!value.IsNull() && value.isConstant())
    {
      snap->scalars[key] = value;
      snap->core.push_back(key);
    }
  }

  // A declared array the solve equated with a constant array (directly or
  // through a store chain, an ite, or a chain of equalities) may have no
  // observed cell at all; its completion is still that constant's default,
  // and the snapshot has to say so.
  for (const std::string& name : mgr->symbol_order)
  {
    auto sit = mgr->symbols.find(name);
    if (sit == mgr->symbols.end() || sit->second.is_function)
      continue;
    const ASTNode& node = sit->second.node;
    ASTNode completion;
    if (node.GetType() == ARRAY_TYPE && !mgr->is_const_array(node) &&
        ce->arrayCompletion(node, completion))
      arrays_seen.insert(node);
  }

  for (const ASTNode& array : arrays_seen)
  {
    ArrayCells cells;
    cells.array = array;
    cells.sort = mgr->sort_of_node(array, fn);
    const SourceSort as = array.GetSourceSort();
    const std::vector<std::pair<ASTNode, ASTNode>> entries =
        ce->GetCounterExampleArray(ce->CounterExampleSize() != 0, array);
    for (const auto& e : entries)
    {
      if (!e.first.isConstant() || !e.second.isConstant())
        continue;
      cells.entries.emplace_back(lift(mgr, e.first, as.index()), lift(mgr, e.second, as.element()));
    }
    std::sort(cells.entries.begin(), cells.entries.end(),
              [](const std::pair<ASTNode, ASTNode>& x, const std::pair<ASTNode, ASTNode>& y) {
                return index_before(x.first, y.first);
              });
    // The unobserved cells: the default of the constant array the checker
    // connected this array to, else the option's fill.
    ASTNode completion;
    if (ce->arrayCompletion(array, completion))
      cells.fill = lift(mgr, completion, as.element());
    else
      cells.fill = fill_value(mgr, cells.sort, fill_ones, fn);
    snap->arrays[array] = cells;
    snap->core.push_back(array);
  }

  // uninterpreted functions: the certified seed, else the vacuous one
  const UFTheoryAdapter* adapter = ce->getUFTheoryAdapter();
  const UFFunctionModelSeedSet* seed = nullptr;
  UFFunctionModelSeedSet fallback;
  if (adapter != nullptr && adapter->hasCertifiedModel())
    seed = adapter->certifiedModelSeed();
  else if (UFContext* ctx = bm->getUFContextIfAny())
  {
    // the vacuous seed of each function whose values are bit-carried; one
    // over Reals gets its table from the exact model below (a Real has no
    // bit-level default to seed it with)
    std::vector<const UFDecl*> seeded;
    for (const UFDecl* d : ctx->activeDeclarations())
      if (d != nullptr && !involves_real(d->signature()))
        seeded.push_back(d);
    fallback = UFModel::defaultSeed(seeded);
    seed = &fallback;
  }
  if (seed != nullptr)
  {
    for (const UFFunctionModelSeed& f : seed->functions)
    {
      if (f.declaration == nullptr)
        continue;
      const UFSignature& sig = f.declaration->signature();
      if (involves_real(sig))
        continue; // tabled from the exact model below
      FunctionCases fc;
      fc.identity = f.declaration->identityNode();
      fc.sort = mgr->sort_of_node(fc.identity, fn);
      for (const UFModelCase& c : f.cases)
      {
        std::vector<ASTNode> args;
        for (std::size_t i = 0; i < c.arguments.size() && i < sig.domain().size(); ++i)
          args.push_back(UFModel::concreteValue(bm, c.arguments[i], sig.domain()[i]));
        fc.cases.emplace_back(std::move(args), UFModel::concreteValue(bm, c.result, sig.codomain()));
      }
      fc.else_value = UFModel::concreteValue(bm, f.defaultValue, sig.codomain());
      snap->functions[fc.identity] = fc;
      // The core is what the solver assigned: a function it never saw has
      // only the vacuous seed, and completion gives the same answer.
      if (!fc.cases.empty())
        snap->core.push_back(fc.identity);
    }
  }

  // The partial floating-point operations (fp.min/fp.max on the two zeros,
  // fp.to_ubv/fp.to_sbv on NaN, infinities and out-of-range values) take the
  // choice the solve's encoding made; a later evaluation cannot know it, so
  // the value of every such node in the checked formula is recorded now.
  {
    std::vector<ASTNode> roots = bm->GetAsserts();
    roots.insert(roots.end(), last_assumptions.begin(), last_assumptions.end());
    ASTNodeSet seen;
    std::vector<ASTNode> stack(roots.begin(), roots.end());
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (n.IsNull() || !seen.insert(n).second)
        continue;
      const Kind_t k = n.GetKind();
      if (k == FP_MIN || k == FP_MAX || k == FP_TO_UBV || k == FP_TO_SBV)
      {
        const ASTNode value = ce->GetCounterExample(n);
        if (!value.IsNull() && value.isConstant())
          snap->scalars[n] = lift(mgr, value, n.GetSourceSort());
      }
      // fp.to_real's constant for NaN or an infinity: the solve's choice,
      // which the exact model holds (never in the core: no one declared it)
      if (k == SYMBOL && bm->IsFpToRealSpecial(n))
      {
        ASTNode value;
        if (bm->HasRealModelValue(n) && bm->RealModelValueNode(n, value) && !value.IsNull())
          snap->scalars[n] = value;
      }
      for (const ASTNode& c : n.GetChildren())
        stack.push_back(c);
    }
  }

  // Reals: the exact model (its symbols, and the Real-sorted applications it
  // valued as a whole; only the symbols are the core)
  for (const ASTNode& sym : bm->AllRealSymbols())
  {
    // The solver's own symbols (a lowered application's result, say) and a
    // function's identity are not entries of the model.
    if (sym.GetKind() == SYMBOL &&
        (bm->FoundIntroducedSymbolSet(sym) || mgr->decl_of(sym) != nullptr ||
         STPMgr::isReservedSymbolName(sym.GetName())))
      continue;
    ASTNode value;
    if (bm->HasRealModelValue(sym) && bm->RealModelValueNode(sym, value) && !value.IsNull())
    {
      snap->scalars[sym] = value;
      if (sym.GetKind() == SYMBOL)
        snap->core.push_back(sym);
    }
  }

  // Functions over Reals. The certified seed above carries bit-level values
  // only, so a function with a Real codomain or a Real argument is tabled
  // from its applications in the checked formula: each one's value (the
  // exact model's, for a Real result) is recorded as a value of the
  // application itself, and then, keyed by its arguments' values, as a case
  // of the function, which is how an application built later is answered;
  // any other application completes to the codomain's default.
  {
    std::map<ASTNode, std::vector<ASTNode>> applications; // identity -> applications
    std::vector<ASTNode> roots = bm->GetAsserts();
    roots.insert(roots.end(), last_assumptions.begin(), last_assumptions.end());
    ASTNodeSet seen;
    std::vector<ASTNode> stack(roots.begin(), roots.end());
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (n.IsNull() || !seen.insert(n).second)
        continue;
      if (n.GetKind() == UF_APPLY)
        if (const UFDecl* d = mgr->decl_of(n[0]))
          if (involves_real(d->signature()))
            applications[n[0]].push_back(n);
      for (const ASTNode& c : n.GetChildren())
        stack.push_back(c);
    }
    std::vector<ASTNode> valued;
    for (const auto& entry : applications)
      for (const ASTNode& app : entry.second)
      {
        const SourceSort codomain = mgr->decl_of(entry.first)->signature().codomain();
        ASTNode value;
        if (codomain.kind() == SourceSort::Kind::Real)
        {
          if (!bm->HasRealModelValue(app) || !bm->RealModelValueNode(app, value))
            value = ASTNode();
        }
        else
          value = lift(mgr, ce->GetCounterExample(app), codomain);
        if (!value.IsNull() && value.isConstant())
        {
          snap->scalars[app] = value;
          valued.push_back(app);
        }
      }
    if (!applications.empty())
    {
      // arguments through the snapshot as it now stands, where a nested
      // application already has its value
      Evaluator ev(*snap, fn, /*complete=*/true);
      for (const auto& entry : applications)
      {
        FunctionCases fc;
        fc.identity = entry.first;
        fc.sort = mgr->sort_of_node(fc.identity, fn);
        const std::uint32_t codomain = mgr->rec(fc.sort).codomain;
        fc.else_value = mgr->default_value(codomain, fn);
        for (const ASTNode& app : entry.second)
        {
          auto vit = snap->scalars.find(app);
          if (vit == snap->scalars.end())
            continue;
          std::vector<ASTNode> args;
          for (std::size_t i = 1; i < app.Degree(); ++i)
            args.push_back(ev.evaluate(app[i]));
          bool known = false;
          for (const auto& c : fc.cases)
            known = known || c.first == args;
          if (!known)
            fc.cases.emplace_back(std::move(args), vit->second);
        }
        if (!fc.cases.empty())
          snap->core.push_back(fc.identity);
        snap->functions[fc.identity] = std::move(fc);
      }
    }
  }

  std::sort(snap->core.begin(), snap->core.end(), [mgr = mgr](const ASTNode& a, const ASTNode& b) {
    auto na = mgr->names_by_node.find(a);
    auto nb = mgr->names_by_node.find(b);
    const std::string sa = na != mgr->names_by_node.end() ? na->second : std::string(a.GetName());
    const std::string sb = nb != mgr->names_by_node.end() ? nb->second : std::string(b.GetName());
    return sa < sb;
  });
  return snap;
}

// ------------------------------------------------------------ the evaluator

Evaluator::Evaluator(const ModelSnapshot& s, const char* fn, bool complete)
    : s_(s), m_(s.mgr), fn_(fn), complete_(complete)
{
}

ASTNode Evaluator::evaluate(const ASTNode& n)
{
  return engine_call(m_, fn_, [&] { return eval(n); });
}

ASTNode Evaluator::read(const ASTNode& array, const ASTNode& index)
{
  return engine_call(m_, fn_, [&] { return eval_read(array, index); });
}

ASTNode Evaluator::eval(const ASTNode& n)
{
  auto it = memo_.find(n);
  if (it != memo_.end())
    return it->second;
  // A term the solver assigned directly: a symbol, or a Real-sorted
  // application the exact model valued as a whole.
  auto assigned = s_.scalars.find(n);
  if (assigned != s_.scalars.end())
  {
    memo_.emplace(n, assigned->second);
    return assigned->second;
  }
  // A conversion to a Real: its operand's value, converted. A finite value
  // converts exactly; NaN and the infinities select their format's constant,
  // which is the solve's choice when the solve saw it and a completion
  // otherwise.
  if (n.GetKind() == ITE)
  {
    const ASTNode operand = m_->bm->FpToRealOperand(n);
    if (!operand.IsNull())
    {
      const SourceSort ss = operand.GetSourceSort();
      const ASTNode value = eval(operand);
      if (value.GetKind() != BVCONST)
        fail_internal(fn_, "a floating-point operand did not evaluate to a value");
      ASTNode out = m_->bm->FpToRealOfValue(value, ss.exponentWidth(), ss.significandWidth());
      if (out.GetKind() == SYMBOL)
      {
        auto special = s_.scalars.find(out);
        if (special != s_.scalars.end())
          out = special->second;
        else
        {
          if (!complete_)
            incomplete_ = true;
          out = m_->bm->CreateRealConst("0");
        }
      }
      memo_.emplace(n, out);
      return out;
    }
  }
  ASTNode out;
  switch (n.GetKind())
  {
    case TRUE:
    case FALSE:
    case BVCONST:
    case REAL_CONST:
      out = n;
      break;
    case SYMBOL:
    {
      if (n.GetType() == ARRAY_TYPE || m_->is_const_array(n) ||
          m_->decl_of(n) != nullptr)
      {
        // arrays and functions stay symbolic; reads and applications resolve
        // them -- but one the model never assigned is a completion
        if (!complete_ && !m_->is_const_array(n) &&
            s_.arrays.count(n) == 0 && s_.functions.count(n) == 0)
          incomplete_ = true;
        out = n;
        break;
      }
      auto sit = s_.scalars.find(n);
      if (sit != s_.scalars.end())
        out = sit->second;
      else
      {
        if (!complete_)
          incomplete_ = true;
        out = m_->default_value(m_->sort_of_node(n, fn_), fn_);
      }
      break;
    }
    case READ:
      out = eval_read(n[0], eval(n[1]));
      break;
    case WRITE:
      out = n;
      break;
    case UF_APPLY:
      out = eval_apply(n);
      break;
    case ARRAY_EQ:
      out = arrays_equal(n[0], n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
      break;
    case ITE:
    {
      const ASTNode c = eval(n[0]);
      if (c == m_->bm->ASTTrue)
        out = n.GetType() == ARRAY_TYPE ? n[1] : eval(n[1]);
      else if (c == m_->bm->ASTFalse)
        out = n.GetType() == ARRAY_TYPE ? n[2] : eval(n[2]);
      else
        fail_internal(fn_, "an if-then-else condition did not evaluate to a truth value");
      break;
    }
    case DISTINCT:
    {
      // Pairwise on the evaluated operands; values intern by value, so two
      // equal values are one node (arrays compare by their cells).
      ASTVec kids;
      for (const ASTNode& c : n.GetChildren())
        kids.push_back(n.GetChildren()[0].GetType() == ARRAY_TYPE ? c : eval(c));
      bool distinct = true;
      for (std::size_t i = 0; i < kids.size() && distinct; ++i)
        for (std::size_t j = i + 1; j < kids.size() && distinct; ++j)
          distinct = kids[i].GetType() == ARRAY_TYPE ? !arrays_equal(kids[i], kids[j])
                                                     : !(kids[i] == kids[j]);
      out = distinct ? m_->bm->ASTTrue : m_->bm->ASTFalse;
      break;
    }
    case EQ:
      if (n[0].GetType() == ARRAY_TYPE)
      {
        out = arrays_equal(n[0], n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
        break;
      }
      if (n[0].GetSourceSort().kind() == SourceSort::Kind::Uninterpreted)
      {
        // elements of a declared sort: one value, one node
        out = eval(n[0]) == eval(n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
        break;
      }
      // fall through
    default:
    {
      ASTVec kids;
      kids.reserve(n.Degree());
      for (const ASTNode& c : n.GetChildren())
        kids.push_back(eval(c));
      out = fold(n, kids);
      break;
    }
  }
  memo_.emplace(n, out);
  return out;
}

ASTNode Evaluator::eval_read(const ASTNode& array, const ASTNode& index)
{
  switch (array.GetKind())
  {
    case SYMBOL:
    {
      if (m_->is_const_array(array))
        return eval(m_->const_array_default(array));
      auto it = s_.arrays.find(array);
      if (it != s_.arrays.end())
      {
        for (const auto& e : it->second.entries)
          if (e.first == index)
            return e.second;
        if (!complete_)
          incomplete_ = true;
        return it->second.fill;
      }
      if (!complete_)
        incomplete_ = true;
      return fill_value(m_, m_->sort_of_node(array, fn_), s_.fill_ones, fn_);
    }
    case WRITE:
    {
      if (eval(array[1]) == index)
        return eval(array[2]);
      return eval_read(array[0], index);
    }
    case ITE:
    {
      const ASTNode c = eval(array[0]);
      return eval_read(c == m_->bm->ASTTrue ? array[1] : array[2], index);
    }
    default:
      break;
  }
  fail_internal(fn_, "a read over an array term that is not a symbol, store or ite");
}

ASTNode Evaluator::eval_apply(const ASTNode& n)
{
  const ASTNode identity = n[0];
  std::vector<ASTNode> args;
  for (std::size_t i = 1; i < n.Degree(); ++i)
    args.push_back(eval(n[i]));
  auto it = s_.functions.find(identity);
  if (it == s_.functions.end())
  {
    if (!complete_)
      incomplete_ = true;
    return m_->default_value(m_->sort_of_node(n, fn_), fn_);
  }
  for (const auto& c : it->second.cases)
  {
    if (c.first.size() != args.size())
      continue;
    bool same = true;
    for (std::size_t i = 0; i < args.size() && same; ++i)
      same = c.first[i] == args[i];
    if (same)
      return c.second;
  }
  // the default branch completes an unobserved application
  if (!complete_)
    incomplete_ = true;
  return it->second.else_value;
}

void collect_indices(Evaluator& ev, const ModelSnapshot& s, ManagerImpl* m, const ASTNode& array,
                     std::set<ASTNode>& indices, ASTNode& base)
{
  ASTNode n = array;
  for (;;)
  {
    switch (n.GetKind())
    {
      case WRITE:
        indices.insert(ev.evaluate(n[1]));
        n = n[0];
        continue;
      case ITE:
      {
        const ASTNode c = ev.evaluate(n[0]);
        n = (c == m->bm->ASTTrue) ? n[1] : n[2];
        continue;
      }
      default:
        break;
    }
    break;
  }
  base = n;
  auto it = s.arrays.find(n);
  if (it != s.arrays.end())
    for (const auto& e : it->second.entries)
      indices.insert(e.first);
}

bool Evaluator::arrays_equal(const ASTNode& a, const ASTNode& b)
{
  std::set<ASTNode> indices;
  ASTNode base_a, base_b;
  collect_indices(*this, s_, m_, a, indices, base_a);
  collect_indices(*this, s_, m_, b, indices, base_b);
  for (const ASTNode& i : indices)
    if (!(eval_read(a, i) == eval_read(b, i)))
      return false;
  // the unobserved cells: equal fills, or the same base
  if (base_a == base_b)
    return true;
  auto fa = s_.arrays.find(base_a);
  auto fb = s_.arrays.find(base_b);
  const ASTNode fill_a = fa != s_.arrays.end() ? fa->second.fill
                         : m_->is_const_array(base_a) ? eval(m_->const_array_default(base_a))
                                                                  : fill_value(m_, m_->sort_of_node(base_a, fn_), s_.fill_ones, fn_);
  const ASTNode fill_b = fb != s_.arrays.end() ? fb->second.fill
                         : m_->is_const_array(base_b) ? eval(m_->const_array_default(base_b))
                                                                  : fill_value(m_, m_->sort_of_node(base_b, fn_), s_.fill_ones, fn_);
  return fill_a == fill_b;
}

namespace
{
// Decimal big-integer helpers for comparing two Real values exactly: the
// engine folds Real arithmetic at construction but not the orderings, and
// its exact rationals need a number-budget scope this evaluator has not got.
std::string mul_dec(const std::string& a, const std::string& b)
{
  std::vector<int> out(a.size() + b.size(), 0);
  for (std::size_t i = a.size(); i-- > 0;)
    for (std::size_t j = b.size(); j-- > 0;)
    {
      int v = out[i + j + 1] + (a[i] - '0') * (b[j] - '0');
      out[i + j + 1] = v % 10;
      out[i + j] += v / 10;
    }
  std::string s;
  for (int d : out)
    if (!(s.empty() && d == 0))
      s.push_back(static_cast<char>('0' + d));
  return s.empty() ? "0" : s;
}

// -1, 0, 1 for the magnitudes a, b (no sign, no leading zeros)
int cmp_dec(const std::string& a, const std::string& b)
{
  if (a.size() != b.size())
    return a.size() < b.size() ? -1 : 1;
  const int c = a.compare(b);
  return c < 0 ? -1 : (c > 0 ? 1 : 0);
}

// -1, 0, 1 for x <=> y
int compare_rationals(const RationalValue& x, const RationalValue& y)
{
  auto split = [](const std::string& s, bool& negative) {
    negative = !s.empty() && s[0] == '-';
    std::string m = negative ? s.substr(1) : s;
    const std::size_t first = m.find_first_not_of('0');
    m = first == std::string::npos ? "0" : m.substr(first);
    if (m == "0")
      negative = false;
    return m;
  };
  bool xneg, yneg;
  const std::string xn = split(x.numerator, xneg), yn = split(y.numerator, yneg);
  if (xneg != yneg)
    return xneg ? -1 : 1;
  // same sign: compare |xn| * yd with |yn| * xd
  const int c = cmp_dec(mul_dec(xn, y.denominator), mul_dec(yn, x.denominator));
  return xneg ? -c : c;
}
} // namespace

ASTNode Evaluator::fold(const ASTNode& n, const ASTVec& kids)
{
  for (const ASTNode& k : kids)
    if (!k.isConstant())
      fail_internal(fn_, "an operand did not evaluate to a value");
  // the Real orderings, and equality, over two Real values
  {
    const Kind_t rk = n.GetKind();
    if (kids.size() == 2 && kids[0].GetKind() == REAL_CONST && kids[1].GetKind() == REAL_CONST &&
        (rk == REAL_LT || rk == REAL_LE || rk == REAL_GT || rk == REAL_GE || rk == EQ))
    {
      const int c = compare_rationals(rational_of(kids[0]), rational_of(kids[1]));
      const bool holds = rk == REAL_LT ? c < 0
                         : rk == REAL_LE ? c <= 0
                         : rk == REAL_GT ? c > 0
                         : rk == REAL_GE ? c >= 0
                                         : c == 0;
      return holds ? m_->bm->ASTTrue : m_->bm->ASTFalse;
    }
  }
  // The partial floating-point operations reach the blaster only in the
  // total form FpTotalise gives them at solve time: one extra child that
  // carries the unspecified choice (which zero fp.min/fp.max return for
  // (+0, -0); the result of fp.to_ubv/fp.to_sbv on NaN, an infinity or an
  // out-of-range value). Evaluation supplies a constant zero choice, so the
  // engine's own folding answers every specified case and the unspecified
  // ones evaluate to that choice instead of aborting in the blaster.
  ASTVec total = kids;
  const Kind_t nk = n.GetKind();
  if ((nk == FP_MIN || nk == FP_MAX) && kids.size() == 2)
    total.push_back(m_->bm->CreateZeroConst(1));
  else if ((nk == FP_TO_UBV || nk == FP_TO_SBV) && kids.size() == 3)
    total.push_back(m_->bm->CreateZeroConst(n.GetValueWidth()));
  ASTNode out = rebuild_node(m_, m_->folding_factory(), n, total);
  if (out.isConstant())
    return out;
  if (out.GetExpWidth() != 0 || n.GetType() == BOOLEAN_TYPE)
  {
    const ASTNode folded = literal_fp::tryEvaluateFpConstant(m_->bm, out);
    if (!folded.IsNull() && folded.isConstant())
      return folded;
  }
  if (out.isRealTerm())
    fail_internal(fn_, "a Real term did not fold to a value");
  const ASTNode evaluated = NonMemberBVConstEvaluator(m_->bm, out);
  if (evaluated.isConstant())
    return lift(m_, evaluated, n.GetSourceSort());
  fail_internal(fn_, "cannot evaluate a term of kind " + std::to_string(static_cast<int>(n.GetKind())));
}

} // namespace detail

using detail::ManagerImpl;
using detail::ModelSnapshot;

// ============================================================ Model

Model::Model(std::shared_ptr<const ModelSnapshot> s) noexcept : snap_(std::move(s)) {}
Model::Model(const Model&) noexcept = default;
Model& Model::operator=(const Model&) noexcept = default;
Model::~Model() = default;

namespace
{
const ModelSnapshot& snap_of(const Model& m, const char* fn)
{
  const ModelSnapshot* s = m.impl();
  if (s == nullptr)
    detail::fail(ErrorCode::STATE, fn, "the model handle is empty");
  s->mgr->check_alive(fn);
  return *s;
}

ASTNode own_node(const ModelSnapshot& s, const Term& t, const char* fn)
{
  if (t.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the term is null", 0);
  if (t.impl_manager() != s.mgr)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager", 0, {t});
  return detail::node_of(t);
}

Term eval_term(const ModelSnapshot& s, const Term& t, const char* fn)
{
  detail::Evaluator ev(s, fn, true);
  return detail::make_term(s.mgr, ev.evaluate(own_node(s, t, fn)));
}
} // namespace

TermManager Model::manager() const
{
  return TermManager(snap_of(*this, "Model::manager").mgr);
}

Term Model::value(const Term& t) const
{
  return eval_term(snap_of(*this, "Model::value"), t, "Model::value");
}

std::optional<Term> Model::try_value(const Term& t) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::try_value");
  detail::Evaluator ev(s, "Model::try_value", false);
  const ASTNode v = ev.evaluate(own_node(s, t, "Model::try_value"));
  if (ev.incomplete())
    return std::nullopt;
  return detail::make_term(s.mgr, v);
}

std::vector<Term> Model::values(const std::vector<Term>& ts) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::values");
  detail::Evaluator ev(s, "Model::values", true);
  std::vector<Term> out;
  out.reserve(ts.size());
  for (const Term& t : ts)
    out.push_back(detail::make_term(s.mgr, ev.evaluate(own_node(s, t, "Model::values"))));
  return out;
}

bool Model::bool_value(const Term& t) const { return value(t).to_bool(); }
std::uint64_t Model::uint64_value(const Term& t) const { return value(t).to_uint64(); }
std::int64_t Model::int64_value(const Term& t) const { return value(t).to_int64(); }
std::string Model::bv_string(const Term& t, int base, bool pad) const { return value(t).to_bv_string(base, pad); }
std::vector<std::uint64_t> Model::bv_limbs(const Term& t) const { return value(t).to_bv_limbs(); }
std::vector<std::uint8_t> Model::bv_bytes(const Term& t, bool little_endian) const { return value(t).to_bv_bytes(little_endian); }
FloatValue Model::fp_value(const Term& t) const { return value(t).to_fp(); }
RoundingMode Model::rm_value(const Term& t) const { return value(t).to_rm(); }
RationalValue Model::real_value(const Term& t) const { return value(t).to_rational(); }
std::uint64_t Model::uninterpreted_index(const Term& t) const { return value(t).to_uninterpreted_index(); }

ArrayValue Model::array_value(const Term& t) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::array_value");
  const ASTNode n = own_node(s, t, "Model::array_value");
  if (n.GetSourceSort().kind() != SourceSort::Kind::Array)
    detail::fail(ErrorCode::SORT_MISMATCH, "Model::array_value", "expected an array term", 0, {t},
                 {t.sort()});
  auto impl = std::make_shared<detail::ValueImpl>();
  impl->snap = snap_;
  impl->key = n;
  impl->is_array = true;
  detail::Evaluator ev(s, "Model::array_value", true);
  std::set<ASTNode> indices;
  ASTNode base;
  detail::collect_indices(ev, s, s.mgr, n, indices, base);
  impl->cells.array = n;
  impl->cells.sort = s.mgr->sort_of_node(n, "Model::array_value");
  for (const ASTNode& i : indices)
    impl->cells.entries.emplace_back(i, ev.read(n, i));
  std::sort(impl->cells.entries.begin(), impl->cells.entries.end(),
            [](const std::pair<ASTNode, ASTNode>& x, const std::pair<ASTNode, ASTNode>& y) {
              return detail::index_before(x.first, y.first);
            });
  auto fit = s.arrays.find(base);
  if (fit != s.arrays.end())
    impl->cells.fill = fit->second.fill;
  else if (s.mgr->is_const_array(base))
    impl->cells.fill = ev.evaluate(s.mgr->const_array_default(base));
  else
    impl->cells.fill = detail::fill_value(s.mgr, impl->cells.sort, s.fill_ones, "Model::array_value");
  return ArrayValue(impl);
}

FunctionValue Model::function_value(const Term& t) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::function_value");
  const ASTNode n = own_node(s, t, "Model::function_value");
  if (s.mgr->decl_of(n) == nullptr)
    detail::fail(ErrorCode::SORT_MISMATCH, "Model::function_value", "expected a function symbol", 0,
                 {t}, {t.sort()});
  auto impl = std::make_shared<detail::ValueImpl>();
  impl->snap = snap_;
  impl->key = n;
  auto it = s.functions.find(n);
  if (it != s.functions.end())
    impl->cases = it->second;
  else
  {
    impl->cases.identity = n;
    impl->cases.sort = s.mgr->sort_of_node(n, "Model::function_value");
    impl->cases.else_value =
        s.mgr->default_value(s.mgr->rec(impl->cases.sort).codomain, "Model::function_value");
  }
  return FunctionValue(impl);
}

void Model::array_bytes(const Term& array, std::uint64_t first, std::size_t count,
                        std::uint8_t* out) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::array_bytes");
  const ASTNode n = own_node(s, array, "Model::array_bytes");
  const std::uint32_t sort = s.mgr->sort_of_node(n, "Model::array_bytes");
  const detail::SortRec& r = s.mgr->rec(sort);
  if (r.kind != SortKind::ARRAY)
    detail::fail(ErrorCode::SORT_MISMATCH, "Model::array_bytes", "expected an array term", 0, {array});
  const detail::SortRec& ir = s.mgr->rec(r.index);
  const detail::SortRec& er = s.mgr->rec(r.element);
  if (ir.kind != SortKind::BV || er.kind != SortKind::BV || er.a % 8 != 0)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Model::array_bytes",
                 "array_bytes needs a bit-vector-indexed array of byte-multiple elements", 0,
                 {array});
  if (count == 0)
    return;
  if (ir.a < 64 && (first + count - 1) >> ir.a != 0)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Model::array_bytes",
                 "first_index + count - 1 does not fit the index width", 1);
  if (out == nullptr)
    detail::fail(ErrorCode::NULL_HANDLE, "Model::array_bytes", "the output buffer is null", 3);
  detail::Evaluator ev(s, "Model::array_bytes", true);
  const std::size_t bytes_per = er.a / 8;
  for (std::size_t i = 0; i < count; ++i)
  {
    const ASTNode index = s.mgr->bv_const(ir.a, first + i);
    const ASTNode v = ev.read(n, index);
    const std::string bits = detail::bv_bits_of(v);
    for (std::size_t b = 0; b < bytes_per; ++b)
    {
      std::uint8_t byte = 0;
      for (unsigned k = 0; k < 8; ++k)
        if (bits[bits.size() - 1 - (b * 8 + k)] == '1')
          byte |= static_cast<std::uint8_t>(1u << k);
      out[i * bytes_per + b] = byte;
    }
  }
}

std::vector<Term> Model::symbols() const
{
  const ModelSnapshot& s = snap_of(*this, "Model::symbols");
  std::vector<Term> out;
  for (const ASTNode& n : s.core)
    out.push_back(detail::make_term(s.mgr, n));
  return out;
}

bool Model::in_core(const Term& t) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::in_core");
  const ASTNode n = own_node(s, t, "Model::in_core");
  return std::find(s.core.begin(), s.core.end(), n) != s.core.end();
}

std::string Model::to_smt2() const
{
  const ModelSnapshot& s = snap_of(*this, "Model::to_smt2");
  ManagerImpl* m = s.mgr;
  std::ostringstream os;
  os << "(\n";
  for (const ASTNode& n : s.core)
  {
    std::string name;
    auto nit = m->names_by_node.find(n);
    if (nit != m->names_by_node.end())
      name = nit->second;
    else if (const UFDecl* d = m->decl_of(n))
      name = d->name();
    else
      name = n.GetName();
    const std::uint32_t sort = m->sort_of_node(n, "Model::to_smt2");
    const detail::SortRec& r = m->rec(sort);
    auto sit = s.scalars.find(n);
    if (sit != s.scalars.end())
    {
      os << "  (define-fun " << detail::quote_symbol(name) << " () " << m->sort_text(sort) << " "
         << detail::print_term(m, sit->second, Format::SMTLIB2, false) << ")\n";
      continue;
    }
    auto ait = s.arrays.find(n);
    if (ait != s.arrays.end())
    {
      const detail::ArrayCells& cells = ait->second;
      std::string body = "((as const " + m->sort_text(sort) + ") " +
                         detail::print_term(m, cells.fill, Format::SMTLIB2, false) + ")";
      for (const auto& e : cells.entries)
        body = "(store " + body + " " + detail::print_term(m, e.first, Format::SMTLIB2, false) + " " +
               detail::print_term(m, e.second, Format::SMTLIB2, false) + ")";
      os << "  (define-fun " << detail::quote_symbol(name) << " () " << m->sort_text(sort) << " "
         << body << ")\n";
      continue;
    }
    auto fit = s.functions.find(n);
    if (fit != s.functions.end() && r.kind == SortKind::FUN)
    {
      const detail::FunctionCases& fc = fit->second;
      os << "  (define-fun " << detail::quote_symbol(name) << " (";
      for (std::size_t i = 0; i < r.domain.size(); ++i)
        os << (i ? " " : "") << "(x!" << i << " " << m->sort_text(r.domain[i]) << ")";
      os << ") " << m->sort_text(r.codomain) << " ";
      std::string body = detail::print_term(m, fc.else_value, Format::SMTLIB2, false);
      for (std::size_t c = fc.cases.size(); c-- > 0;)
      {
        std::string cond;
        for (std::size_t i = 0; i < fc.cases[c].first.size(); ++i)
          cond += " (= x!" + std::to_string(i) + " " +
                  detail::print_term(m, fc.cases[c].first[i], Format::SMTLIB2, false) + ")";
        const std::string guard = fc.cases[c].first.size() == 1 ? cond.substr(1) : "(and" + cond + ")";
        body = "(ite " + guard + " " + detail::print_term(m, fc.cases[c].second, Format::SMTLIB2, false) +
               " " + body + ")";
      }
      os << body << ")\n";
    }
  }
  os << ")\n";
  return os.str();
}

std::ostream& operator<<(std::ostream& os, const Model& m)
{
  return os << m.to_smt2();
}

// ============================================================ ArrayValue

ArrayValue::ArrayValue(std::shared_ptr<const detail::ValueImpl> i) noexcept : impl_(std::move(i)) {}
ArrayValue::ArrayValue(const ArrayValue&) noexcept = default;
ArrayValue& ArrayValue::operator=(const ArrayValue&) noexcept = default;
ArrayValue::~ArrayValue() = default;

Sort ArrayValue::sort() const { return Sort(impl_->snap->mgr, impl_->cells.sort); }
Term ArrayValue::default_value() const { return detail::make_term(impl_->snap->mgr, impl_->cells.fill); }
std::size_t ArrayValue::size() const { return impl_->cells.entries.size(); }
ArrayValue::Entry ArrayValue::entry(std::size_t i) const
{
  if (i >= impl_->cells.entries.size())
    detail::fail(ErrorCode::INDEX_OUT_OF_RANGE, "ArrayValue::entry",
                 "index " + std::to_string(i) + " out of range [0, " +
                     std::to_string(impl_->cells.entries.size()) + ")",
                 0);
  ManagerImpl* m = impl_->snap->mgr;
  return Entry{detail::make_term(m, impl_->cells.entries[i].first),
               detail::make_term(m, impl_->cells.entries[i].second), true};
}
std::vector<ArrayValue::Entry> ArrayValue::entries() const
{
  std::vector<Entry> out;
  for (std::size_t i = 0; i < size(); ++i)
    out.push_back(entry(i));
  return out;
}
Term ArrayValue::at(const Term& index) const
{
  ManagerImpl* m = impl_->snap->mgr;
  if (index.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, "ArrayValue::at", "the index is null", 0);
  const ASTNode i = detail::node_of(index);
  if (!i.isConstant())
    detail::fail(ErrorCode::NOT_A_VALUE, "ArrayValue::at", "the index must be a value", 0, {index});
  for (const auto& e : impl_->cells.entries)
    if (e.first == i)
      return detail::make_term(m, e.second);
  return detail::make_term(m, impl_->cells.fill);
}
Term ArrayValue::as_term() const
{
  ManagerImpl* m = impl_->snap->mgr;
  TermManager tm(m);
  Term out = tm.mk_const_array(sort(), default_value());
  for (const auto& e : impl_->cells.entries)
    out = store(out, detail::make_term(m, e.first), detail::make_term(m, e.second));
  return out;
}

// ============================================================ FunctionValue

FunctionValue::FunctionValue(std::shared_ptr<const detail::ValueImpl> i) noexcept : impl_(std::move(i)) {}
FunctionValue::FunctionValue(const FunctionValue&) noexcept = default;
FunctionValue& FunctionValue::operator=(const FunctionValue&) noexcept = default;
FunctionValue::~FunctionValue() = default;

Sort FunctionValue::sort() const { return Sort(impl_->snap->mgr, impl_->cases.sort); }
std::size_t FunctionValue::size() const { return impl_->cases.cases.size(); }
FunctionValue::Entry FunctionValue::entry(std::size_t i) const
{
  if (i >= impl_->cases.cases.size())
    detail::fail(ErrorCode::INDEX_OUT_OF_RANGE, "FunctionValue::entry",
                 "index " + std::to_string(i) + " out of range [0, " +
                     std::to_string(impl_->cases.cases.size()) + ")",
                 0);
  ManagerImpl* m = impl_->snap->mgr;
  Entry e;
  for (const ASTNode& a : impl_->cases.cases[i].first)
    e.args.push_back(detail::make_term(m, a));
  e.value = detail::make_term(m, impl_->cases.cases[i].second);
  e.observed = true;
  return e;
}
std::vector<FunctionValue::Entry> FunctionValue::entries() const
{
  std::vector<Entry> out;
  for (std::size_t i = 0; i < size(); ++i)
    out.push_back(entry(i));
  return out;
}
Term FunctionValue::else_value() const { return detail::make_term(impl_->snap->mgr, impl_->cases.else_value); }
Term FunctionValue::apply(const std::vector<Term>& args) const
{
  ManagerImpl* m = impl_->snap->mgr;
  std::vector<ASTNode> nodes;
  for (std::size_t i = 0; i < args.size(); ++i)
  {
    if (args[i].is_null())
      detail::fail(ErrorCode::NULL_HANDLE, "FunctionValue::apply", "an argument is null", static_cast<int>(i));
    nodes.push_back(detail::node_of(args[i]));
    if (!nodes.back().isConstant())
      detail::fail(ErrorCode::NOT_A_VALUE, "FunctionValue::apply", "the arguments must be values",
                   static_cast<int>(i), {args[i]});
  }
  for (const auto& c : impl_->cases.cases)
  {
    if (c.first.size() != nodes.size())
      continue;
    bool same = true;
    for (std::size_t i = 0; i < nodes.size() && same; ++i)
      same = c.first[i] == nodes[i];
    if (same)
      return detail::make_term(m, c.second);
  }
  return else_value();
}
Term FunctionValue::as_ite_term(const std::vector<Term>& formals) const
{
  ManagerImpl* m = impl_->snap->mgr;
  const detail::SortRec& r = m->rec(impl_->cases.sort);
  if (formals.size() != r.domain.size())
    detail::fail(ErrorCode::ARITY, "FunctionValue::as_ite_term",
                 "the function takes " + std::to_string(r.domain.size()) + " formals");
  Term body = else_value();
  for (std::size_t c = impl_->cases.cases.size(); c-- > 0;)
  {
    const auto& entry = impl_->cases.cases[c];
    std::vector<Term> conj;
    for (std::size_t i = 0; i < entry.first.size(); ++i)
      conj.push_back(eq(formals[i], detail::make_term(m, entry.first[i])));
    const Term guard = conj.size() == 1 ? conj[0] : and_(conj);
    body = ite(guard, detail::make_term(m, entry.second), body);
  }
  return body;
}

} // namespace api
} // namespace stp

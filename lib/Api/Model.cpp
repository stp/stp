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
#include <limits>
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

// Every member that holds engine nodes is emptied before the manager is
// released: the release may be the last one and free the nodes' manager, and
// a node outliving it would be let go into freed memory.
ModelSnapshot::~ModelSnapshot()
{
  scalars.clear();
  arrays.clear();
  functions.clear();
  core.clear();
  partial_choices.clear();
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

// The key of a partial floating-point operation `n` whose operands have the
// values `kids` (PartialChoiceKey).
PartialChoiceKey partial_choice_key(const ASTNode& n, const ASTVec& kids)
{
  PartialChoiceKey key;
  key.kind = n.GetKind();
  for (std::size_t i = 0; i < kids.size(); ++i)
  {
    const SourceSort ss = n[i].GetSourceSort();
    if (ss.kind() != SourceSort::Kind::FloatingPoint)
    {
      key.operands.push_back(kids[i]);
      continue;
    }
    key.formats.push_back(ss.exponentWidth());
    key.formats.push_back(ss.significandWidth());
    const bool nan = fp_value_of(kids[i], ss.exponentWidth(), ss.significandWidth()).cls ==
                     FloatValue::Class::NOT_A_NUMBER;
    key.operands.push_back(nan ? ASTNode() : kids[i]);
  }
  return key;
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

  // every array's cells from one walk over the counterexample
  const std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> recorded =
      ce->GetCounterExampleArrays(ce->CounterExampleSize() != 0,
                                  std::vector<ASTNode>(arrays_seen.begin(), arrays_seen.end()));
  for (const ASTNode& array : arrays_seen)
  {
    ArrayCells cells;
    cells.array = array;
    cells.sort = mgr->sort_of_node(array, fn);
    const SourceSort as = array.GetSourceSort();
    const auto rit = recorded.find(array);
    if (rit != recorded.end())
      for (const auto& e : rit->second)
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
      // concreteValue hands an element of a declared sort back as its
      // carrier's bits; the snapshot holds every other value of that sort as
      // the element itself, so it is lifted here like the rest.
      FunctionCases fc;
      fc.identity = f.declaration->identityNode();
      fc.sort = mgr->sort_of_node(fc.identity, fn);
      for (const UFModelCase& c : f.cases)
      {
        std::vector<ASTNode> args;
        for (std::size_t i = 0; i < c.arguments.size() && i < sig.domain().size(); ++i)
          args.push_back(lift(mgr, UFModel::concreteValue(bm, c.arguments[i], sig.domain()[i]),
                              sig.domain()[i]));
        fc.cases.emplace_back(std::move(args),
                              lift(mgr, UFModel::concreteValue(bm, c.result, sig.codomain()),
                                   sig.codomain()));
      }
      fc.else_value = lift(mgr, UFModel::concreteValue(bm, f.defaultValue, sig.codomain()),
                           sig.codomain());
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
  std::vector<ASTNode> partials;
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
        {
          snap->scalars[n] = lift(mgr, value, n.GetSourceSort());
          partials.push_back(n);
        }
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
    // A symbol no arithmetic mentioned has the model's zero, which is the
    // completion's value too: it is not in the core, as a bit-vector symbol
    // the solve never saw is not.
    if (sym.GetKind() == SYMBOL && !bm->RealModelSolveValued(sym))
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

  // Each partial operation's choice again, keyed by its operands' values
  // through the snapshot as it now stands: these operations are functions, so
  // an application the check never saw, over values one it did see had,
  // takes that one's choice rather than a completion.
  if (!partials.empty())
  {
    Evaluator ev(*snap, fn, /*complete=*/true);
    for (const ASTNode& n : partials)
    {
      ASTVec kids;
      for (const ASTNode& c : n.GetChildren())
        kids.push_back(ev.evaluate(c));
      snap->partial_choices.emplace(partial_choice_key(n, kids), snap->scalars[n]);
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

// An explicit stack: a term is valued once everything its value reads is in
// the memo, so a deep term costs heap rather than the C++ stack. A step that
// finds inputs without a value names them and is taken again once they have
// one; a read keeps its place in the chain of writes it walks, and an ite
// values only the branch its condition picks (the other may need a
// completion the value does not).
ASTNode Evaluator::eval(const ASTNode& root)
{
  if (const auto it = memo_.find(root); it != memo_.end())
    return it->second;
  std::vector<Frame> stack;
  stack.push_back(Frame{root, ASTNode(), ASTNode(), false});
  std::vector<ASTNode> needs;
  while (!stack.empty())
  {
    if (memo_.count(stack.back().n) != 0)
    {
      stack.pop_back();
      continue;
    }
    needs.clear();
    ASTNode out;
    step(stack.back(), needs, out);
    if (!needs.empty())
    {
      for (const ASTNode& need : needs)
        stack.push_back(Frame{need, ASTNode(), ASTNode(), false});
      continue;
    }
    memo_.emplace(stack.back().n, out);
    stack.pop_back();
  }
  return memo_.at(root);
}

const ASTNode* Evaluator::valued(const ASTNode& n) const
{
  const auto it = memo_.find(n);
  return it == memo_.end() ? nullptr : &it->second;
}

void Evaluator::step(Frame& f, std::vector<ASTNode>& needs, ASTNode& out)
{
  const ASTNode n = f.n;
  // every one of `kids` valued, or the missing ones named
  const auto all_valued = [&](const auto& kids, std::size_t from) {
    for (std::size_t i = from; i < kids.size(); ++i)
      if (valued(kids[i]) == nullptr)
        needs.push_back(kids[i]);
    return needs.empty();
  };
  // A term the solver assigned directly: a symbol, or a Real-sorted
  // application the exact model valued as a whole.
  if (const auto assigned = s_.scalars.find(n); assigned != s_.scalars.end())
  {
    out = assigned->second;
    return;
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
      const ASTNode* value = valued(operand);
      if (value == nullptr)
      {
        needs.push_back(operand);
        return;
      }
      if (value->GetKind() != BVCONST)
        fail_internal(fn_, "a floating-point operand did not evaluate to a value");
      const SourceSort ss = operand.GetSourceSort();
      out = m_->bm->FpToRealOfValue(*value, ss.exponentWidth(), ss.significandWidth());
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
      return;
    }
  }
  switch (n.GetKind())
  {
    case TRUE:
    case FALSE:
    case BVCONST:
    case REAL_CONST:
      out = n;
      return;
    case SYMBOL:
    {
      if (n.GetType() == ARRAY_TYPE || m_->is_const_array(n) || m_->decl_of(n) != nullptr)
      {
        // arrays and functions stay symbolic; reads and applications resolve
        // them -- but one the model never assigned is a completion
        if (!complete_ && !m_->is_const_array(n) && s_.arrays.count(n) == 0 &&
            s_.functions.count(n) == 0)
          incomplete_ = true;
        out = n;
        return;
      }
      if (!complete_)
        incomplete_ = true;
      out = m_->default_value(m_->sort_of_node(n, fn_), fn_);
      return;
    }
    case READ:
    {
      if (!f.started)
      {
        const ASTNode* index = valued(n[1]);
        if (index == nullptr)
        {
          needs.push_back(n[1]);
          return;
        }
        f.index = *index;
        f.cursor = n[0];
        f.started = true;
      }
      // down the chain from where the last step stopped
      for (;;)
      {
        const ASTNode array = f.cursor;
        switch (array.GetKind())
        {
          case SYMBOL:
          {
            if (m_->is_const_array(array))
            {
              const ASTNode fill = m_->const_array_default(array);
              if (const ASTNode* v = valued(fill))
                out = *v;
              else
                needs.push_back(fill);
              return;
            }
            out = read_symbol(array, f.index);
            return;
          }
          case WRITE:
          {
            const ASTNode* at = valued(array[1]);
            if (at == nullptr)
            {
              needs.push_back(array[1]);
              return;
            }
            if (!(*at == f.index))
            {
              f.cursor = array[0];
              continue;
            }
            if (const ASTNode* v = valued(array[2]))
              out = *v;
            else
              needs.push_back(array[2]);
            return;
          }
          case ITE:
          {
            const ASTNode* c = valued(array[0]);
            if (c == nullptr)
            {
              needs.push_back(array[0]);
              return;
            }
            f.cursor = *c == m_->bm->ASTTrue ? array[1] : array[2];
            continue;
          }
          default:
            fail_internal(fn_, "a read over an array term that is not a symbol, store or ite");
        }
      }
    }
    case WRITE:
      out = n;
      return;
    case UF_APPLY:
    {
      if (!all_valued(n.GetChildren(), 1))
        return;
      out = apply_values(n);
      return;
    }
    case ARRAY_EQ:
      out = arrays_equal(n[0], n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
      return;
    case ITE:
    {
      const ASTNode* c = valued(n[0]);
      if (c == nullptr)
      {
        needs.push_back(n[0]);
        return;
      }
      if (!(*c == m_->bm->ASTTrue) && !(*c == m_->bm->ASTFalse))
        fail_internal(fn_, "an if-then-else condition did not evaluate to a truth value");
      const ASTNode& branch = *c == m_->bm->ASTTrue ? n[1] : n[2];
      if (n.GetType() == ARRAY_TYPE)
      {
        out = branch;
        return;
      }
      if (const ASTNode* v = valued(branch))
        out = *v;
      else
        needs.push_back(branch);
      return;
    }
    case DISTINCT:
    {
      // Pairwise on the evaluated operands; values intern by value, so two
      // equal values are one node (arrays compare by their cells).
      const bool arrays = n.GetChildren()[0].GetType() == ARRAY_TYPE;
      if (!arrays && !all_valued(n.GetChildren(), 0))
        return;
      ASTVec kids;
      for (const ASTNode& c : n.GetChildren())
        kids.push_back(arrays ? c : *valued(c));
      bool distinct = true;
      for (std::size_t i = 0; i < kids.size() && distinct; ++i)
        for (std::size_t j = i + 1; j < kids.size() && distinct; ++j)
          distinct = arrays ? !arrays_equal(kids[i], kids[j]) : !(kids[i] == kids[j]);
      out = distinct ? m_->bm->ASTTrue : m_->bm->ASTFalse;
      return;
    }
    case EQ:
      if (n[0].GetType() == ARRAY_TYPE)
      {
        out = arrays_equal(n[0], n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
        return;
      }
      if (n[0].GetSourceSort().kind() == SourceSort::Kind::Uninterpreted)
      {
        // elements of a declared sort: one value, one node
        if (!all_valued(n.GetChildren(), 0))
          return;
        out = *valued(n[0]) == *valued(n[1]) ? m_->bm->ASTTrue : m_->bm->ASTFalse;
        return;
      }
      // fall through
    default:
    {
      if (!all_valued(n.GetChildren(), 0))
        return;
      ASTVec kids;
      kids.reserve(n.Degree());
      for (const ASTNode& c : n.GetChildren())
        kids.push_back(*valued(c));
      out = fold(n, kids);
      return;
    }
  }
}

// The cell of array symbol `array` at value `index`: an observed cell, else
// the fill (a completion), else -- an array the model never assigned -- the
// option's fill (a completion too).
ASTNode Evaluator::read_symbol(const ASTNode& array, const ASTNode& index)
{
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

// A read at a value, down the chain of writes: each write's index and value,
// and each ite's condition, valued as the walk reaches them (by eval, whose
// own stack is explicit).
ASTNode Evaluator::eval_read(const ASTNode& from, const ASTNode& index)
{
  ASTNode array = from;
  for (;;)
  {
    switch (array.GetKind())
    {
      case SYMBOL:
        if (m_->is_const_array(array))
          return eval(m_->const_array_default(array));
        return read_symbol(array, index);
      case WRITE:
        if (eval(array[1]) == index)
          return eval(array[2]);
        array = array[0];
        continue;
      case ITE:
        array = eval(array[0]) == m_->bm->ASTTrue ? array[1] : array[2];
        continue;
      default:
        fail_internal(fn_, "a read over an array term that is not a symbol, store or ite");
    }
  }
}

// An application whose arguments are valued: the case the model lists for
// those values, else the else branch (a completion), else -- a function the
// model never assigned -- the codomain's default (a completion too).
ASTNode Evaluator::apply_values(const ASTNode& n)
{
  const ASTNode identity = n[0];
  std::vector<ASTNode> args;
  for (std::size_t i = 1; i < n.Degree(); ++i)
    args.push_back(*valued(n[i]));
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

// The cells a chain of writes gives array term `array`, walked once from the
// top: the topmost write to an index is its cell, in the order first met
// (ites follow the branch their condition picks). `base` is where the chain
// ends. Linear in the chain; reading each written index from the top again
// was quadratic.
void chain_cells(Evaluator& ev, ManagerImpl* m, const ASTNode& array,
                 std::vector<std::pair<ASTNode, ASTNode>>& cells, ASTNode& base)
{
  std::unordered_set<ASTNode, ASTNode::ASTNodeHasher> written;
  ASTNode n = array;
  for (;;)
  {
    if (n.GetKind() == WRITE)
    {
      const ASTNode index = ev.evaluate(n[1]);
      if (written.insert(index).second)
        cells.emplace_back(index, ev.evaluate(n[2]));
      n = n[0];
    }
    else if (n.GetKind() == ITE)
      n = ev.evaluate(n[0]) == m->bm->ASTTrue ? n[1] : n[2];
    else
      break;
  }
  base = n;
}

// Whether `count` distinct indexes are every value of the array sort's index
// sort, leaving no cell for a fill to decide. Values are interned canonically
// (a float format's NaNs are one node, its two zeros are two), so distinct
// nodes are distinct values; a declared sort has an element per pattern of its
// carrier.
bool covers_index_sort(ManagerImpl* m, std::uint32_t array_sort, std::size_t count)
{
  const SortRec& i = m->rec(m->rec(array_sort).index);
  constexpr unsigned digits = std::numeric_limits<std::size_t>::digits;
  switch (i.kind)
  {
    case SortKind::BV:
      return i.a < digits && count == (std::size_t{1} << i.a);
    case SortKind::UNINTERPRETED:
      return i.b < digits && count == (std::size_t{1} << i.b);
    case SortKind::RM:
      return count == 5;
    case SortKind::FP:
      // every pattern but the 2^sb - 2 NaNs, and the one NaN
      return i.a + i.b < digits &&
             count == (std::size_t{1} << (i.a + i.b)) - (std::size_t{1} << i.b) + 3;
    default:
      return false;
  }
}

bool Evaluator::arrays_equal(const ASTNode& a, const ASTNode& b)
{
  std::vector<std::pair<ASTNode, ASTNode>> cells_a, cells_b;
  ASTNode base_a, base_b;
  chain_cells(*this, m_, a, cells_a, base_a);
  chain_cells(*this, m_, b, cells_b, base_b);
  const std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> at_a(cells_a.begin(),
                                                                          cells_a.end());
  const std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> at_b(cells_b.begin(),
                                                                          cells_b.end());
  // every index either side writes, or its base has a cell at, read on both
  std::set<ASTNode> indices;
  for (const auto& c : cells_a)
    indices.insert(c.first);
  for (const auto& c : cells_b)
    indices.insert(c.first);
  for (const ASTNode& base : {base_a, base_b})
    if (const auto it = s_.arrays.find(base); it != s_.arrays.end())
      for (const auto& e : it->second.entries)
        indices.insert(e.first);
  const auto cell = [&](const std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher>& at,
                        const ASTNode& base, const ASTNode& i) {
    const auto it = at.find(i);
    return it != at.end() ? it->second : eval_read(base, i);
  };
  for (const ASTNode& i : indices)
    if (!(cell(at_a, base_a, i) == cell(at_b, base_b, i)))
      return false;
  // the unobserved cells, if the writes leave any: equal fills, or the same
  // base
  if (base_a == base_b || covers_index_sort(m_, m_->sort_of_node(a, fn_), indices.size()))
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
  const auto fold_total = [&](const ASTVec& total) -> ASTNode {
    const ASTNode out = rebuild_node(m_, m_->folding_factory(), n, total);
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
  };
  // The partial floating-point operations reach the blaster only in the
  // total form FpTotalise gives them at solve time: one extra child that
  // carries the unspecified choice (which zero fp.min/fp.max return for
  // (+0, -0); the result of fp.to_ubv/fp.to_sbv on NaN, an infinity or an
  // out-of-range value). Folded under two different choices, a specified
  // case answers the same both times, and the engine's own folding is its
  // value; an unspecified one gives back each choice.
  const Kind_t nk = n.GetKind();
  const bool min_max = (nk == FP_MIN || nk == FP_MAX) && kids.size() == 2;
  const bool to_bv = (nk == FP_TO_UBV || nk == FP_TO_SBV) && kids.size() == 3;
  if (!min_max && !to_bv)
    return fold_total(kids);
  const unsigned width = min_max ? 1 : n.GetValueWidth();
  ASTVec with_zero = kids, with_ones = kids;
  with_zero.push_back(m_->bm->CreateZeroConst(width));
  with_ones.push_back(m_->bm->CreateMaxConst(width));
  const ASTNode zero_choice = fold_total(with_zero);
  if (zero_choice == fold_total(with_ones))
    return zero_choice;
  // Unspecified: the solve's choice for these operand values, if the check met
  // them. Otherwise any value is a model's to choose, and the zero choice is
  // this evaluation's -- a completion, so not one simplify() or try_value()
  // may make.
  const auto chosen = s_.partial_choices.find(partial_choice_key(n, kids));
  if (chosen != s_.partial_choices.end())
    return chosen->second;
  if (!complete_)
    incomplete_ = true;
  return zero_choice;
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
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager", 0);
  return detail::node_of(t);
}

// The value of array term `n`: its cells and its default. `determined`, when
// given, says whether the value needs no completion: every symbol it reads is
// in the core, and its base is an array the model assigned (default included)
// or a constant array.
std::shared_ptr<detail::ValueImpl> array_value_of(const std::shared_ptr<const ModelSnapshot>& snap,
                                                  const ASTNode& n, const char* fn, bool complete,
                                                  bool* determined)
{
  const ModelSnapshot& s = *snap;
  auto impl = std::make_shared<detail::ValueImpl>();
  impl->snap = snap;
  impl->key = n;
  impl->is_array = true;
  detail::Evaluator ev(s, fn, complete);
  ASTNode base;
  detail::chain_cells(ev, s.mgr, n, impl->cells.entries, base);
  // the base's own cells, under the writes
  if (const auto it = s.arrays.find(base); it != s.arrays.end())
  {
    std::unordered_set<ASTNode, ASTNode::ASTNodeHasher> written;
    for (const auto& c : impl->cells.entries)
      written.insert(c.first);
    for (const auto& e : it->second.entries)
      if (written.count(e.first) == 0)
        impl->cells.entries.push_back(e);
  }
  impl->cells.array = n;
  impl->cells.sort = s.mgr->sort_of_node(n, fn);
  std::sort(impl->cells.entries.begin(), impl->cells.entries.end(),
            [](const std::pair<ASTNode, ASTNode>& x, const std::pair<ASTNode, ASTNode>& y) {
              return detail::index_before(x.first, y.first);
            });
  bool assigned = true;
  auto fit = s.arrays.find(base);
  if (fit != s.arrays.end())
    impl->cells.fill = fit->second.fill;
  else if (s.mgr->is_const_array(base))
    impl->cells.fill = ev.evaluate(s.mgr->const_array_default(base));
  else
  {
    impl->cells.fill = detail::fill_value(s.mgr, impl->cells.sort, s.fill_ones, fn);
    assigned = false;
  }
  if (determined != nullptr)
    *determined = assigned && !ev.incomplete();
  return impl;
}

// A function has no value term: its value is a table (function_value).
void refuse_function(const ModelSnapshot& s, const ASTNode& n, const Term& t, const char* fn)
{
  if (s.mgr->rec(s.mgr->sort_of_node(n, fn)).kind == SortKind::FUN)
    detail::fail(ErrorCode::SORT_MISMATCH, fn,
                 "a function has no value term; read its table with Model::function_value", 0,
                 {t}, {t.sort()});
}

Term value_term(const std::shared_ptr<const ModelSnapshot>& snap, detail::Evaluator& ev,
                const Term& t, const char* fn)
{
  const ModelSnapshot& s = *snap;
  const ASTNode n = own_node(s, t, fn);
  refuse_function(s, n, t, fn);
  // An array's value is a constant array under a chain of stores; the
  // evaluator hands an array term back as it stands.
  if (n.GetSourceSort().kind() == SourceSort::Kind::Array)
    return ArrayValue(array_value_of(snap, n, fn, true, nullptr)).as_term();
  return detail::make_term(s.mgr, ev.evaluate(n));
}
} // namespace

TermManager Model::manager() const
{
  return TermManager(snap_of(*this, "Model::manager").mgr);
}

Term Model::value(const Term& t) const
{
  const ModelSnapshot& s = snap_of(*this, "Model::value");
  detail::Evaluator ev(s, "Model::value", true);
  return value_term(snap_, ev, t, "Model::value");
}

std::optional<Term> Model::try_value(const Term& t) const
{
  const char* fn = "Model::try_value";
  const ModelSnapshot& s = snap_of(*this, fn);
  const ASTNode n = own_node(s, t, fn);
  refuse_function(s, n, t, fn);
  if (n.GetSourceSort().kind() == SourceSort::Kind::Array)
  {
    bool determined = false;
    const ArrayValue av(array_value_of(snap_, n, fn, false, &determined));
    if (!determined)
      return std::nullopt;
    return av.as_term();
  }
  detail::Evaluator ev(s, fn, false);
  const ASTNode v = ev.evaluate(n);
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
    out.push_back(value_term(snap_, ev, t, "Model::values"));
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
  return ArrayValue(array_value_of(snap_, n, "Model::array_value", true, nullptr));
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
  // [first, first + count) has to lie in the index sort, which the sum cannot
  // be trusted to say: it wraps at 2^64. Past 64 bits every such interval fits,
  // and an index beyond 2^64 - 1 carries into bit 64.
  const std::uint64_t last = count - 1; // past first
  const bool fits = ir.a > 64 || (ir.a == 64 ? last <= UINT64_MAX - first
                                             : first >> ir.a == 0 &&
                                                   last <= ((std::uint64_t(1) << ir.a) - 1) - first);
  if (!fits)
    detail::fail(ErrorCode::INVALID_ARGUMENT, "Model::array_bytes",
                 "first_index + count - 1 does not fit the index width", 1);
  if (out == nullptr)
    detail::fail(ErrorCode::NULL_HANDLE, "Model::array_bytes", "the output buffer is null", 3);
  detail::Evaluator ev(s, "Model::array_bytes", true);
  const std::size_t bytes_per = er.a / 8;
  for (std::size_t i = 0; i < count; ++i)
  {
    const std::uint64_t low = first + i;
    ASTNode index;
    if (low >= first)
      index = s.mgr->bv_const(ir.a, low);
    else
    {
      // 2^64 + low, most significant bit first
      std::string bits(ir.a, '0');
      bits[ir.a - 65] = '1';
      for (unsigned k = 0; k < 64; ++k)
        if ((low >> k) & 1)
          bits[ir.a - 1 - k] = '1';
      index = s.mgr->bv_const_bits(ir.a, bits);
    }
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
Term ArrayValue::default_value() const
{
  impl_->snap->mgr->check_alive("ArrayValue::default_value");
  return detail::make_term(impl_->snap->mgr, impl_->cells.fill);
}
std::size_t ArrayValue::size() const { return impl_->cells.entries.size(); }
ArrayValue::Entry ArrayValue::entry(std::size_t i) const
{
  if (i >= impl_->cells.entries.size())
    detail::fail(ErrorCode::INDEX_OUT_OF_RANGE, "ArrayValue::entry",
                 "index " + std::to_string(i) + " out of range [0, " +
                     std::to_string(impl_->cells.entries.size()) + ")",
                 0);
  ManagerImpl* m = impl_->snap->mgr;
  m->check_alive("ArrayValue::entry");
  return Entry{detail::make_term(m, impl_->cells.entries[i].first),
               detail::make_term(m, impl_->cells.entries[i].second)};
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
  const char* fn = "ArrayValue::at";
  ManagerImpl* m = impl_->snap->mgr;
  m->check_alive(fn);
  if (index.is_null())
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the index is null", 0);
  if (index.impl_manager() != m)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the index belongs to another term manager", 0);
  const ASTNode i = detail::node_of(index);
  if (!i.isConstant())
    detail::fail(ErrorCode::NOT_A_VALUE, fn, "the index must be a value", 0, {index});
  // an index of another sort names no cell: refused, where it answered the default
  const std::uint32_t expected = m->rec(impl_->cells.sort).index;
  if (m->sort_of_node(i, fn) != expected)
    detail::fail(ErrorCode::SORT_MISMATCH, fn, "the index is not of the array's index sort", 0,
                 {index}, {index.sort(), Sort(m, expected)});
  for (const auto& e : impl_->cells.entries)
    if (e.first == i)
      return detail::make_term(m, e.second);
  return detail::make_term(m, impl_->cells.fill);
}
Term ArrayValue::as_term() const
{
  ManagerImpl* m = impl_->snap->mgr;
  m->check_alive("ArrayValue::as_term");
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
  m->check_alive("FunctionValue::entry");
  Entry e;
  for (const ASTNode& a : impl_->cases.cases[i].first)
    e.args.push_back(detail::make_term(m, a));
  e.value = detail::make_term(m, impl_->cases.cases[i].second);
  return e;
}
std::vector<FunctionValue::Entry> FunctionValue::entries() const
{
  std::vector<Entry> out;
  for (std::size_t i = 0; i < size(); ++i)
    out.push_back(entry(i));
  return out;
}
Term FunctionValue::else_value() const
{
  impl_->snap->mgr->check_alive("FunctionValue::else_value");
  return detail::make_term(impl_->snap->mgr, impl_->cases.else_value);
}
Term FunctionValue::apply(const std::vector<Term>& args) const
{
  const char* fn = "FunctionValue::apply";
  ManagerImpl* m = impl_->snap->mgr;
  m->check_alive(fn);
  // the function's own arity and domain: arguments that fit no case of it
  // used to answer the else value
  const detail::SortRec& r = m->rec(impl_->cases.sort);
  if (args.size() != r.domain.size())
    detail::fail(ErrorCode::ARITY, fn,
                 "the function takes " + std::to_string(r.domain.size()) + " arguments");
  std::vector<ASTNode> nodes;
  for (std::size_t i = 0; i < args.size(); ++i)
  {
    if (args[i].is_null())
      detail::fail(ErrorCode::NULL_HANDLE, fn, "an argument is null", static_cast<int>(i));
    if (args[i].impl_manager() != m)
      detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the argument belongs to another term manager",
                   static_cast<int>(i));
    nodes.push_back(detail::node_of(args[i]));
    if (!nodes.back().isConstant())
      detail::fail(ErrorCode::NOT_A_VALUE, fn, "the arguments must be values",
                   static_cast<int>(i), {args[i]});
    if (m->sort_of_node(nodes.back(), fn) != r.domain[i])
      detail::fail(ErrorCode::SORT_MISMATCH, fn, "the argument is not of the function's domain sort",
                   static_cast<int>(i), {args[i]}, {args[i].sort(), Sort(m, r.domain[i])});
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
  m->check_alive("FunctionValue::as_ite_term");
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

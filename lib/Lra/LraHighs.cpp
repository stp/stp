#include "LraHighs.h"
#include "ExactLraCore.h"
#include "LraFrontend.h"
#include "LraHighsCuts.h"
#include "LraReconstruction.h"
#include "LraRelaxation.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>
#include <map>
#include <unordered_map>
#include <unordered_set>
#ifdef STP_HAVE_HIGHS
#include <interfaces/highs_c_api.h>
#endif

namespace stp::lra
{
#ifdef STP_HAVE_HIGHS
namespace
{
using Clock = std::chrono::steady_clock;
struct Budget final : ExactLraResourceObserver
{
  SATSolver* solver;
  Clock::time_point deadline;
  Budget(SATSolver* s, unsigned seconds)
      : solver(s), deadline(Clock::now() + std::chrono::seconds(seconds))
  {
  }
  double remaining() const
  {
    const double own = std::max(
        0.0, std::chrono::duration<double>(deadline - Clock::now()).count());
    return solver && solver->hasTimeLimit()
               ? std::min(own, solver->secondsRemaining())
               : own;
  }
  StopReason pollBeforePivot() noexcept override
  {
    return remaining() > 0 ? StopReason::Continue : StopReason::ResourceLimit;
  }
  void accountPivot(bool) noexcept override {}
};
struct Engine
{
  void* ptr = Highs_create();
  ~Engine()
  {
    if (ptr)
      Highs_destroy(ptr);
  }
  Engine(const Engine&) = delete;
  Engine& operator=(const Engine&) = delete;
  Engine() = default;
};
using Row = HighsProofRow;
struct Endpoint
{
  ExactRational value;
  std::size_t row;
  bool negate;
};
struct ColumnBounds
{
  std::optional<Endpoint> lower, upper;
};
struct Equation
{
  std::map<std::size_t, ExactRational> terms;
  ExactRational value, delta;
};

class Proposal
{
public:
  STPMgr& manager;
  Frontend frontend;
  Budget budget;
  NumberBudget& numbers;
  std::vector<ASTNode> symbols;
  std::unordered_map<std::uint64_t, std::size_t> columns;
  std::vector<Row> rows;
  std::vector<std::size_t> binaries;
  std::size_t mip_calls = 0, mip_models = 0;
  bool constant_conflict = false;
  std::vector<std::vector<std::pair<std::size_t, double>>> cut_recipes;
  std::vector<double> root_values;
  std::size_t recipe_callbacks = 0, cuts = 0, cut_attempts = 0;
  HighsInt lp_status = 0, mip_status = 0;
  std::vector<Row> accepted_cuts;
  std::vector<std::size_t> last_conflict_rows;
  bool last_conflict_support_valid = false;
  std::size_t replay_nodes = 0, replay_conflicts = 0, replay_resolutions = 0;
  std::size_t replay_reused = 0, replay_clauses = 0, replay_screened = 0;
  bool replay_refuted = false, replay_model = false;
  std::size_t calls = 0, models = 0, rays = 0, rejected = 0;
  Proposal(STPMgr& m, SATSolver* s, NumberBudget& n)
      : manager(m), frontend(m), budget(s, m.UserFlags.lra_highs_seconds),
        numbers(n)
  {
  }
  ~Proposal()
  {
    if (manager.UserFlags.stats_flag)
      std::cerr << "LRA HiGHS: rows=" << rows.size()
                << ", columns=" << symbols.size() << ", lp_calls=" << calls
                << ", models=" << models << ", rays=" << rays
                << ", rejected=" << rejected << ", binaries=" << binaries.size()
                << ", mip_calls=" << mip_calls << ", mip_models=" << mip_models
                << ", lp_status=" << lp_status << ", mip_status=" << mip_status
                << ", recipe_callbacks=" << recipe_callbacks
                << ", cut_attempts=" << cut_attempts << ", cuts=" << cuts
                << ", replay_nodes=" << replay_nodes
                << ", replay_conflicts=" << replay_conflicts
                << ", replay_resolutions=" << replay_resolutions
                << ", replay_reused=" << replay_reused
                << ", replay_clauses=" << replay_clauses
                << ", replay_screened=" << replay_screened
                << ", replay_refuted=" << replay_refuted
                << ", replay_model=" << replay_model << '\n';
  }
  std::size_t column(LraSymbolId id)
  {
    auto [it, added] = columns.emplace(id.value, symbols.size());
    if (added)
      symbols.push_back(frontend.symbolNode(id));
    return it->second;
  }
  void collect(const ASTNode& input)
  {
    NumberOperationScope scope(numbers);
    ASTVec work{input};
    while (!work.empty() && budget.remaining() > 0)
    {
      const auto node = work.back();
      work.pop_back();
      if (node.GetKind() == AND)
      {
        for (const auto& c : node.GetChildren())
          work.push_back(c);
        continue;
      }
      const auto kind = node.GetKind();
      if ((manager.UserFlags.lra_highs_mip ||
           manager.UserFlags.lra_highs_cuts ||
           manager.UserFlags.lra_highs_replay) &&
          kind == OR && node.Degree() == 2)
        collectBinary(node);
      if (node.Degree() != 2 || !node[0].isRealTerm() ||
          !node[1].isRealTerm() ||
          (kind != EQ && kind != REAL_LT && kind != REAL_LE &&
           kind != REAL_GT && kind != REAL_GE))
        continue;
      const auto p = frontend.normalizePredicate(node);
      if (p.is_constant)
      {
        constant_conflict = constant_conflict || !p.constant_value;
        continue;
      }
      const auto rel = p.canonical.relation;
      const bool flip = rel == FrontendRelation::Greater ||
                        rel == FrontendRelation::GreaterEqual;
      Row row;
      row.rhs = flip ? p.canonical.lhs_minus_rhs.constant
                     : -p.canonical.lhs_minus_rhs.constant;
      row.equality = rel == FrontendRelation::Equal;
      row.strict =
          rel == FrontendRelation::Less || rel == FrontendRelation::Greater;
      for (const auto& t : p.canonical.lhs_minus_rhs.terms)
        row.terms.push_back(
            {column(t.symbol), flip ? -t.coefficient : t.coefficient});
      std::sort(row.terms.begin(), row.terms.end(),
                [](const auto& a, const auto& b) { return a.col < b.col; });
      rows.push_back(std::move(row));
    }
  }
  // Integrality comes from an asserted two-point domain, never from the
  // numerical solution or the Real sort. Normalization also handles reversed
  // equalities and scaled affine spellings of the same variable.
  void collectBinary(const ASTNode& node)
  {
    const auto symbol = frontend.binaryDomainSymbol(node);
    if (!symbol)
      return;
    const auto poly = frontend.normalize(*symbol);
    const auto c = column(poly.terms[0].symbol);
    if (std::find(binaries.begin(), binaries.end(), c) != binaries.end())
      return;
    binaries.push_back(c);
    // These hull bounds are exact consequences of the domain disjunction.
    rows.push_back({{{c, ExactRational(std::int64_t{-1})}},
                    ExactRational(),
                    false,
                    false});
    rows.push_back({{{c, ExactRational(std::int64_t{1})}},
                    ExactRational(std::int64_t{1}),
                    false,
                    false});
  }
  std::vector<ColumnBounds> endpoints()
  {
    NumberOperationScope scope(numbers);
    std::vector<ColumnBounds> result(symbols.size());
    for (std::size_t r = 0; r < rows.size(); ++r)
    {
      const auto& row = rows[r];
      if (row.terms.size() != 1)
        continue;
      const auto& t = row.terms[0];
      const auto value = row.rhs / t.coefficient;
      auto& b = result[t.col];
      if (row.equality || t.coefficient.sign() < 0)
        if (!b.lower || b.lower->value < value ||
            (b.lower->value == value && row.strict &&
             !rows[b.lower->row].strict))
          b.lower = Endpoint{value, r, t.coefficient.sign() > 0};
      if (row.equality || t.coefficient.sign() > 0)
        if (!b.upper || value < b.upper->value ||
            (b.upper->value == value && row.strict &&
             !rows[b.upper->row].strict))
          b.upper = Endpoint{value, r, t.coefficient.sign() < 0};
    }
    return result;
  }
  bool load(Engine& engine)
  {
    NumberOperationScope scope(numbers);
    if (!engine.ptr || symbols.empty() || symbols.size() > 100000 ||
        rows.size() > 200000)
      return false;
    const double infinity = Highs_getInfinity(engine.ptr);
    std::vector<double> lower(symbols.size(), -infinity),
        upper(symbols.size(), infinity);
    std::vector<double> cost(symbols.size(), 0.0), rl, ru, value;
    std::vector<HighsInt> start{0}, index;
    auto convert = [](const ExactRational& q)
    {
      const double d = approximate(q);
      if (!std::isfinite(d) || std::abs(d) >= 1e19 || (!q.isZero() && d == 0))
        throw std::runtime_error("LP coefficient outside supported range");
      return d;
    };
    const auto box = endpoints();
    for (std::size_t c = 0; c < symbols.size(); ++c)
    {
      if (box[c].lower)
        lower[c] = convert(box[c].lower->value);
      if (box[c].upper)
        upper[c] = convert(box[c].upper->value);
    }
    for (const auto& row : rows)
    {
      ru.push_back(convert(row.rhs));
      rl.push_back(row.equality ? ru.back() : -infinity);
      for (const auto& t : row.terms)
      {
        index.push_back(static_cast<HighsInt>(t.col));
        value.push_back(convert(t.coefficient));
      }
      if (value.size() > 4000000)
        return false;
      start.push_back(static_cast<HighsInt>(value.size()));
    }
    Highs_setBoolOptionValue(engine.ptr, "output_flag", 0);
    Highs_setIntOptionValue(engine.ptr, "threads", 1);
    // Original row identities are the certificate vocabulary. Keeping presolve
    // off also makes the basis and ray independent of postsolve heuristics.
    Highs_setStringOptionValue(engine.ptr, "presolve", "off");
    Highs_setStringOptionValue(engine.ptr, "solver", "simplex");
    return Highs_passLp(engine.ptr, static_cast<HighsInt>(symbols.size()),
                        static_cast<HighsInt>(rows.size()),
                        static_cast<HighsInt>(value.size()),
                        kHighsMatrixFormatRowwise, kHighsObjSenseMinimize, 0.0,
                        cost.data(), lower.data(), upper.data(), rl.data(),
                        ru.data(), start.data(), index.data(),
                        value.data()) != kHighsStatusError;
  }
  bool run(Engine& engine, bool mip = false)
  {
    if (budget.remaining() <= 0)
      return false;
    Highs_setDoubleOptionValue(engine.ptr, "time_limit",
                               Highs_getRunTime(engine.ptr) +
                                   budget.remaining() * (mip ? 0.5 : 1.0));
    if (mip)
      ++mip_calls;
    else
      ++calls;
    const auto result = Highs_run(engine.ptr);
    (mip ? mip_status : lp_status) = Highs_getModelStatus(engine.ptr);
    return result != kHighsStatusError && budget.remaining() > 0;
  }

  // Sparse reconstruction of the proposed original-row basis. Free columns
  // retain their numerical proposal. Every answer is subsequently checked
  // against all original bounds. Limits and polling also cover exact repair.
  bool repair(const std::vector<HighsInt>& status,
              const std::vector<HighsInt>& colstatus,
              std::vector<ModelCandidateValue>& values)
  {
    NumberOperationScope scope(numbers);
    std::map<std::size_t, Equation> pivots;
    // Preserve the proposed basis's nonbasic structural columns as well as
    // its nonbasic row slacks. Otherwise Gaussian elimination can choose a
    // different free parameter and move a degenerate vertex outside a bound.
    const bool hasStrict = std::any_of(
        rows.begin(), rows.end(), [](const Row& row) { return row.strict; });
    for (std::size_t c = 0; !hasStrict && c < values.size(); ++c)
    {
      if (colstatus[c] == kHighsBasisStatusBasic)
        continue;
      Equation eq;
      eq.terms.emplace(c, ExactRational(std::int64_t{1}));
      eq.value = values[c].value;
      pivots.emplace(c, std::move(eq));
    }
    std::size_t operations = 0, entries = 0;
    std::vector<std::size_t> order;
    for (std::size_t r = 0; r < rows.size(); ++r)
    {
      bool tightStrict = false;
      if (rows[r].strict)
      {
        ExactRational activity;
        for (const auto& t : rows[r].terms)
          activity += t.coefficient * values[t.col].value;
        tightStrict = std::abs(approximate(activity - rows[r].rhs)) <=
                      1e-8 * (1 + std::abs(approximate(rows[r].rhs)));
      }
      if (rows[r].equality || status[r] != kHighsBasisStatusBasic ||
          tightStrict)
        order.push_back(r);
    }
    std::stable_sort(order.begin(), order.end(), [&](auto a, auto b)
                     { return rows[a].terms.size() < rows[b].terms.size(); });
    for (const auto r : order)
    {
      if (budget.remaining() <= 0)
        return false;
      Equation eq;
      for (const auto& t : rows[r].terms)
        eq.terms[t.col] += t.coefficient;
      eq.value = rows[r].rhs;
      if (rows[r].strict)
        eq.delta = ExactRational(std::int64_t{-1});
      while (!eq.terms.empty())
      {
        const auto col = eq.terms.begin()->first;
        if (eq.terms.begin()->second.isZero())
        {
          eq.terms.erase(eq.terms.begin());
          continue;
        }
        const auto old = pivots.find(col);
        if (old == pivots.end())
          break;
        const auto factor =
            eq.terms.begin()->second / old->second.terms.begin()->second;
        for (const auto& [c, a] : old->second.terms)
        {
          eq.terms[c] -= factor * a;
          if (eq.terms[c].isZero())
            eq.terms.erase(c);
          if (++operations > 5000000 ||
              (operations % 1024 == 0 && budget.remaining() <= 0))
            return false;
        }
        eq.value -= factor * old->second.value;
        eq.delta -= factor * old->second.delta;
      }
      if (eq.terms.empty())
      {
        if (!eq.value.isZero() || !eq.delta.isZero())
          return false;
      }
      else
      {
        entries += eq.terms.size();
        if (entries > 1000000)
          return false;
        const auto col = eq.terms.begin()->first;
        pivots.emplace(col, std::move(eq));
      }
    }
    for (auto it = pivots.rbegin(); it != pivots.rend(); ++it)
    {
      if (budget.remaining() <= 0)
        return false;
      auto& eq = it->second;
      auto v = eq.value, d = eq.delta;
      for (auto t = std::next(eq.terms.begin()); t != eq.terms.end(); ++t)
      {
        v -= t->second * values[t->first].value;
        d -= t->second * values[t->first].delta;
      }
      values[it->first].value = v / eq.terms.begin()->second;
      values[it->first].delta = d / eq.terms.begin()->second;
    }
    return true;
  }

  // Endpoint rows remain registered even when HiGHS also uses them as column
  // bounds. Complete the ray's exact residual with those original endpoints;
  // branch-local selector equations participate by the same scoped rule.
  bool certify(Engine& engine, LraReconstruction* reconstruction,
               bool allowConflict = true)
  {
    last_conflict_rows.clear();
    last_conflict_support_valid = false;
    const auto status = Highs_getModelStatus(engine.ptr);
    if (status != kHighsModelStatusOptimal &&
        status != kHighsModelStatusInfeasible)
      return false;
    if (status == kHighsModelStatusInfeasible && !allowConflict)
      return false;
    ExactLraCore core(frontend.numberLimits());
    std::vector<VariableId> variables;
    for (std::size_t c = 0; c < symbols.size(); ++c)
    {
      const auto v = core.addVariable();
      if (!v.value)
        return false;
      variables.push_back(*v.value);
    }
    std::vector<CandidateBound> bounds;
    std::vector<std::pair<AtomId, std::optional<AtomId>>> atoms;
    std::uint64_t serial = 0;
    std::unordered_map<std::uint64_t, std::size_t> origin_rows;
    for (const auto& row : rows)
    {
      if (budget.remaining() <= 0)
        return false;
      std::vector<LinearTerm> terms;
      {
        NumberOperationScope scope(numbers);
        for (const auto& t : row.terms)
          terms.push_back({variables[t.col], t.coefficient});
      }
      const auto r = core.addRow(terms.data(), terms.data() + terms.size());
      if (!r.value)
        throw std::runtime_error("exact LP row registration declined: " +
                                 std::to_string(static_cast<int>(r.status)));
      const auto add = [&](Relation rel)
      {
        const OriginId pos{1, ++serial}, neg{1, ++serial};
        origin_rows.emplace(pos.serial, atoms.size());
        return core.addAtom(*r.value, rel, row.rhs, pos, neg);
      };
      const auto a = add(row.strict ? Relation::Less : Relation::LessEqual);
      if (!a.value)
        return false;
      bounds.push_back({*a.value, true});
      std::optional<AtomId> lower;
      if (row.equality)
      {
        auto b = add(Relation::GreaterEqual);
        if (!b.value)
          return false;
        lower = *b.value;
        bounds.push_back({*b.value, true});
      }
      atoms.emplace_back(*a.value, lower);
    }
    if (core.initialize() != InputStatus::Accepted || budget.remaining() <= 0)
      return false;
    if (status == kHighsModelStatusInfeasible)
    {
      std::vector<double> ray(rows.size());
      HighsInt available = 0;
      if (Highs_getDualRay(engine.ptr, &available, ray.data()) ==
              kHighsStatusError ||
          !available)
        return false;
      std::vector<ConflictCandidateTerm> terms;
      {
        NumberOperationScope scope(numbers);
        const auto box = endpoints();
        std::map<std::pair<std::size_t, bool>, ExactRational> weights;
        for (std::size_t r = 0; r < rows.size(); ++r)
        {
          if (!std::isfinite(ray[r]))
            return false;
          if (ray[r] < 0)
            weights[{r, false}] += -exactDyadic(ray[r]);
          else if (ray[r] > 0 && rows[r].equality)
            weights[{r, true}] += exactDyadic(ray[r]);
        }
        std::vector<ExactRational> residual(symbols.size());
        for (const auto& [side, w] : weights)
          for (const auto& t : rows[side.first].terms)
            residual[t.col] += (side.second ? -w : w) * t.coefficient;
        for (std::size_t c = 0; c < residual.size(); ++c)
        {
          if (residual[c].isZero())
            continue;
          const auto& bound =
              residual[c].sign() > 0 ? box[c].lower : box[c].upper;
          if (!bound)
            continue; // sparse weight recovery may still cancel it
          const auto a = bound->negate ? -rows[bound->row].terms[0].coefficient
                                       : rows[bound->row].terms[0].coefficient;
          const auto w = -residual[c] / a;
          if (w.sign() <= 0)
            return false;
          weights[{bound->row, bound->negate}] += w;
        }
        for (const auto& [side, w] : weights)
        {
          if (w.isZero())
            continue;
          const auto& a = atoms[side.first];
          if (side.second && !a.second)
            return false;
          terms.push_back({side.second ? *a.second : a.first, true, w});
        }
      }
      const auto conflict = core.certifyCandidateConflict(
          terms.data(), terms.data() + terms.size(), true, &budget, 4096);
      if (conflict.status == InputStatus::Accepted && conflict.value)
      {
        ++rays;
        last_conflict_support_valid = true;
        for (const auto& term : conflict.value->terms)
        {
          const auto row = origin_rows.find(term.origin.serial);
          if (row == origin_rows.end())
          {
            last_conflict_support_valid = false;
            break;
          }
          last_conflict_rows.push_back(row->second);
        }
        return true;
      }
      ++rejected;
      return false;
    }
    if (!reconstruction)
      return false;
    std::vector<double> primal(symbols.size());
    std::vector<HighsInt> colstatus(symbols.size()), rowstatus(rows.size());
    if (Highs_getSolution(engine.ptr, primal.data(), nullptr, nullptr,
                          nullptr) == kHighsStatusError ||
        Highs_getBasis(engine.ptr, colstatus.data(), rowstatus.data()) ==
            kHighsStatusError)
      return false;
    std::vector<ModelCandidateValue> values;
    {
      NumberOperationScope scope(numbers);
      const auto box = endpoints();
      for (std::size_t c = 0; c < symbols.size(); ++c)
      {
        if (!std::isfinite(primal[c]))
          return false;
        const auto bound = colstatus[c] == kHighsBasisStatusLower ? box[c].lower
                           : colstatus[c] == kHighsBasisStatusUpper
                               ? box[c].upper
                               : std::nullopt;
        values.push_back({variables[c],
                          bound ? bound->value : exactDyadic(primal[c]),
                          ExactRational()});
      }
    }
    auto model = core.certifyCandidateModel(
        values.data(), values.data() + values.size(), bounds.data(),
        bounds.data() + bounds.size());
    if (!model.value && repair(rowstatus, colstatus, values))
      model = core.certifyCandidateModel(
          values.data(), values.data() + values.size(), bounds.data(),
          bounds.data() + bounds.size());
    if (!model.value || budget.remaining() <= 0)
    {
      ++rejected;
      return false;
    }
    NumberOperationScope scope(numbers);
    const auto predicate = [&](const ASTNode& node)
    {
      const auto p = frontend.normalizePredicate(node);
      auto result = p.canonical.lhs_minus_rhs.constant;
      for (const auto& t : p.canonical.lhs_minus_rhs.terms)
      {
        const auto c = columns.find(t.symbol.value);
        if (c == columns.end())
          throw std::runtime_error("model omits a source symbol");
        result += t.coefficient * model.value->values[c->second].value;
      }
      switch (p.canonical.relation)
      {
        case FrontendRelation::Less:
          return result.sign() < 0;
        case FrontendRelation::LessEqual:
          return result.sign() <= 0;
        case FrontendRelation::Greater:
          return result.sign() > 0;
        case FrontendRelation::GreaterEqual:
          return result.sign() >= 0;
        case FrontendRelation::Equal:
          return result.isZero();
      }
      return false;
    };
    if (!acceptsRealFormula(reconstruction->original, predicate))
    {
      ++rejected;
      return false;
    }
    std::vector<RealModelDefinition> definitions;
    for (std::size_t c = 0; c < symbols.size(); ++c)
      definitions.push_back(
          {symbols[c], manager.CreateRealConst(
                           model.value->values[c].value.numeratorDecimal(),
                           model.value->values[c].value.denominatorDecimal())});
    reconstruction->definitions = std::move(definitions);
    reconstruction->witness = true;
    ++models;
    return true;
  }

#ifdef STP_HAVE_HIGHS_CUT_LOG
  static void cutCallback(int type, const char*,
                          const HighsCallbackDataOut* out, HighsCallbackDataIn*,
                          void* data) noexcept
  {
    if (type != kHighsCallbackMipRootCutRecipe || !out || !data)
      return;
    auto& self = *static_cast<Proposal*>(data);
    ++self.recipe_callbacks;
    try
    {
      if (self.cut_recipes.size() >= 128 || out->root_cut_recipe_size <= 0 ||
          out->root_cut_recipe_size > 4096 || !out->root_cut_recipe_row ||
          !out->root_cut_recipe_weight || self.budget.remaining() <= 0)
        return;
      std::vector<std::pair<std::size_t, double>> recipe;
      for (HighsInt i = 0; i < out->root_cut_recipe_size; ++i)
      {
        const auto r = out->root_cut_recipe_row[i];
        const double weight = out->root_cut_recipe_weight[i];
        // Cut-pool rows have no exact identity in this experiment. Even a
        // mistaken in-range hint only combines our own asserted rows: the
        // callback's floating cut coefficients are never used as a premise.
        if (r < 0 || static_cast<std::size_t>(r) >= self.rows.size() ||
            !std::isfinite(weight) || std::abs(weight) > 1e12)
          return;
        recipe.emplace_back(static_cast<std::size_t>(r), weight);
      }
      self.cut_recipes.push_back(std::move(recipe));
    }
    catch (...)
    {
    } // The optional logger must not throw through the C ABI.
  }
#endif

  ASTNode rootCuts(const ASTNode& input)
  {
    if (binaries.empty() || budget.remaining() <= 0)
      return input;
    NumberOperationScope scope(numbers);
    std::vector<bool> binary(symbols.size(), false);
    for (const auto c : binaries)
      binary[c] = true;
    ASTVec lemmas{input};
    bool refuted = false;
    const auto keepGoing = [&] { return budget.remaining() > 0; };
    const auto allowed = [&]
    {
      return !refuted && cuts < manager.UserFlags.lra_highs_cut_limit &&
             cut_attempts < 256 && keepGoing();
    };
    const auto emit = [&](const std::optional<Row>& cut)
    {
      if (!cut)
        return;
      if (cut->terms.empty())
      {
        if (cut->rhs.sign() < 0)
        {
          ++cuts;
          refuted = true;
        }
        return;
      }
      // Numerical screening affects usefulness only, never validity.
      if (root_values.size() != symbols.size())
        return;
      double activity = 0;
      for (const auto& t : cut->terms)
        activity += approximate(t.coefficient) * root_values[t.col];
      if (!std::isfinite(activity) || activity <= approximate(cut->rhs) + 1e-7)
        return;
      ASTVec terms;
      for (const auto& t : cut->terms)
      {
        const auto coefficient =
            manager.CreateRealConst(t.coefficient.numeratorDecimal(),
                                    t.coefficient.denominatorDecimal());
        terms.push_back(
            t.coefficient.isOne()
                ? symbols[t.col]
                : manager.CreateRealTerm(REAL_MUL,
                                         ASTVec{coefficient, symbols[t.col]}));
      }
      const auto lhs = terms.size() == 1
                           ? terms[0]
                           : manager.CreateRealTerm(REAL_ADD, terms);
      const auto rhs = manager.CreateRealConst(cut->rhs.numeratorDecimal(),
                                               cut->rhs.denominatorDecimal());
      const auto lemma = manager.CreateNode(REAL_LE, lhs, rhs);
      if (std::find(lemmas.begin(), lemmas.end(), lemma) == lemmas.end())
      {
        lemmas.push_back(lemma);
        accepted_cuts.push_back(*cut);
        ++cuts;
      }
    };
    const auto attempt =
        [&](const std::vector<std::pair<std::size_t, ExactRational>>& weights)
    {
      for (const bool complement : {false, true})
      {
        if (!allowed())
          return;
        ++cut_attempts;
        emit(certifyHighsCgCut(rows, binary, weights, complement, keepGoing));
      }
    };
    std::vector<bool> preferUpper(symbols.size(), false);
    if (root_values.size() == symbols.size())
      for (const auto c : binaries)
        preferUpper[c] = root_values[c] > 0.5;
    for (const auto& recipe : cut_recipes)
    {
      std::vector<std::pair<std::size_t, ExactRational>> weights;
      for (const auto& [r, weight] : recipe)
      {
        auto hint = exactDyadic(weight);
        // A perturbed half can otherwise turn an exact coefficient 1 into
        // 0.999... and make integer rounding useless. Every guessed rational
        // is still just a weight on our own exact premises, so the checker
        // rederives the cut independently of numerical closeness.
        for (std::uint64_t denominator = 1; denominator <= 64; ++denominator)
        {
          const auto numerator = static_cast<std::int64_t>(
              std::llround(weight * static_cast<double>(denominator)));
          const double rounded =
              static_cast<double>(numerator) / static_cast<double>(denominator);
          if (std::abs(weight - rounded) <=
              1e-9 * std::max(1.0, std::abs(weight)))
          {
            hint = ExactRational(numerator, denominator);
            break;
          }
        }
        weights.emplace_back(r, std::move(hint));
      }
      attempt(weights);
      for (const auto c : binaries)
      {
        if (!allowed())
          break;
        if (root_values.size() != symbols.size() ||
            !std::isfinite(root_values[c]) ||
            std::abs(root_values[c] - std::round(root_values[c])) < 1e-7)
          continue;
        ++cut_attempts;
        emit(certifyHighsSplitCut(rows, binary, weights, c, preferUpper,
                                  keepGoing));
      }
      // Tableau rows can be used in either direction when the exact source
      // side exists. Unsupported negative inequality weights are rejected.
      for (auto& term : weights)
        term.second = -term.second;
      attempt(weights);
    }
    // Single-row CG is also useful when MIP preprocessing closes the root
    // before any tableau callback. It uses the same exact checker.
    for (std::size_t r = 0;
         r < rows.size() && !refuted && keepGoing() &&
         cuts < manager.UserFlags.lra_highs_cut_limit && cut_attempts < 256;
         ++r)
    {
      for (const auto& t : rows[r].terms)
      {
        if (!binary[t.col] || t.coefficient.isZero())
          continue;
        auto scale = ExactRational(std::int64_t{1}) / t.coefficient;
        if (scale.sign() < 0)
          scale = -scale;
        attempt({{r, scale}});
        if (rows[r].equality)
          attempt({{r, -scale}});
        break;
      }
    }
    if (refuted)
      return manager.ASTFalse;
    return lemmas.size() == 1 ? input : manager.CreateNode(AND, lemmas);
  }

  ASTNode replay(const ASTNode& input, LraReconstruction* reconstruction)
  {
    if (input == manager.ASTFalse || binaries.empty() ||
        budget.remaining() <= 0 ||
        manager.UserFlags.lra_highs_replay_nodes == 0)
      return input;
    {
      NumberOperationScope scope(numbers);
      for (const auto& cut : accepted_cuts)
        rows.push_back(cut);
    }
    const auto baseRows = rows.size();
    const auto box = endpoints();
    Engine engine;
    if (!load(engine))
      return input;
    const double infinity = Highs_getInfinity(engine.ptr);
    std::vector<double> lower(symbols.size(), -infinity),
        upper(symbols.size(), infinity);
    {
      NumberOperationScope scope(numbers);
      for (std::size_t c = 0; c < symbols.size(); ++c)
      {
        if (box[c].lower)
          lower[c] = approximate(box[c].lower->value);
        if (box[c].upper)
          upper[c] = approximate(box[c].upper->value);
      }
    }
    using Choice = std::pair<std::size_t, int>;
    using Path = std::vector<Choice>;
    Path path;
    std::vector<Path> closed;
    std::vector<int> assignment(symbols.size(), -1);
    ASTVec clauses{input};
    bool globalConflict = false;
    enum class Outcome
    {
      Open,
      Refuted,
      Model
    };
    const auto remember = [&](Path support)
    {
      if (support.empty())
      {
        globalConflict = true;
        return;
      }
      NumberOperationScope scope(numbers);
      ASTVec disjuncts;
      for (const auto& [c, bit] : support)
      {
        const auto value = manager.CreateRealConst(bit ? "1" : "0");
        disjuncts.push_back(
            manager.CreateNode(NOT, manager.CreateNode(EQ, symbols[c], value)));
      }
      const auto clause = disjuncts.size() == 1
                              ? disjuncts[0]
                              : manager.CreateNode(OR, disjuncts);
      if (std::find(clauses.begin(), clauses.end(), clause) == clauses.end())
      {
        clauses.push_back(clause);
        closed.push_back(std::move(support));
      }
    };
    std::function<Outcome()> visit = [&]() -> Outcome
    {
      // A previously certified clause can close a node without another LP.
      for (const auto& support : closed)
        if (std::all_of(support.begin(), support.end(), [&](const Choice& c)
                        { return assignment[c.first] == c.second; }))
        {
          ++replay_reused;
          return Outcome::Refuted;
        }
      if (budget.remaining() <= 0 ||
          replay_nodes >=
              std::min(manager.UserFlags.lra_highs_replay_nodes, 8192U))
        return Outcome::Open;
      ++replay_nodes;
      std::vector<double> primal(symbols.size(), 0.5);
      bool havePoint = false;
      if (run(engine))
      {
        havePoint =
            Highs_getModelStatus(engine.ptr) == kHighsModelStatusOptimal &&
            Highs_getSolution(engine.ptr, primal.data(), nullptr, nullptr,
                              nullptr) != kHighsStatusError;
        const bool fractional =
            havePoint &&
            std::any_of(binaries.begin(), binaries.end(),
                        [&](std::size_t c)
                        {
                          return !std::isfinite(primal[c]) ||
                                 std::abs(primal[c] - std::round(primal[c])) >
                                     1e-6;
                        });
        // A fractional selector cannot already satisfy its 0/1 domain. Skip
        // expensive model reconstruction and branch; this screen derives no
        // fact, and near-integer proposals still receive full exact checks.
        if (fractional)
          ++replay_screened;
        const auto before = models;
        if (!fractional && certify(engine, reconstruction))
        {
          if (models != before)
            return Outcome::Model;
          ++replay_conflicts;
          Path support;
          if (last_conflict_support_valid)
          {
            for (std::size_t d = 0; d < path.size(); ++d)
              if (std::find(last_conflict_rows.begin(),
                            last_conflict_rows.end(),
                            baseRows + d) != last_conflict_rows.end())
                support.push_back(path[d]);
          }
          else
            support = path;
          remember(std::move(support));
          return Outcome::Refuted;
        }
      }
      // Failure to recover a certificate never closes a numerical node.
      // Use its fractional point only to select the next exhaustive 0/1 split.
      if (path.size() >= 128 || budget.remaining() <= 0)
        return Outcome::Open;
      if (!havePoint)
        std::fill(primal.begin(), primal.end(), 0.5);
      std::optional<std::size_t> selected;
      double score = -1;
      for (const auto c : binaries)
      {
        if (assignment[c] != -1)
          continue;
        const double fraction =
            std::isfinite(primal[c])
                ? std::min(std::abs(primal[c]), std::abs(1 - primal[c]))
                : 0;
        if (!selected || fraction > score)
        {
          selected = c;
          score = fraction;
        }
      }
      if (!selected)
        return Outcome::Open;
      const auto c = *selected;
      const int first = std::isfinite(primal[c]) && primal[c] >= 0.5 ? 1 : 0;
      bool both = true;
      for (const int bit : {first, 1 - first})
      {
        Outcome child = Outcome::Open;
        {
          {
            NumberOperationScope scope(numbers);
            rows.push_back({{{c, ExactRational(std::int64_t{1})}},
                            ExactRational(static_cast<std::int64_t>(bit)),
                            true,
                            false});
          }
          path.emplace_back(c, bit);
          assignment[c] = bit;
          struct Restore
          {
            Proposal& self;
            Engine& engine;
            Path& path;
            std::vector<int>& assignment;
            std::size_t col;
            double lower, upper;
            ~Restore()
            {
              Highs_changeColBounds(engine.ptr, static_cast<HighsInt>(col),
                                    lower, upper);
              self.rows.pop_back();
              path.pop_back();
              assignment[col] = -1;
            }
          } restore{*this, engine, path, assignment, c, lower[c], upper[c]};
          // Only bounds change: the LP rows and warm numerical basis survive
          // descent, backtracking and moves to sibling nodes.
          if (Highs_changeColBounds(engine.ptr, static_cast<HighsInt>(c),
                                    static_cast<double>(bit),
                                    static_cast<double>(bit)) !=
              kHighsStatusError)
            child = visit();
        }
        if (child == Outcome::Model)
          return child;
        if (globalConflict)
          return Outcome::Refuted;
        both = both && child == Outcome::Refuted;
      }
      if (!both)
        return Outcome::Open;
      // The asserted binary domain covers these two children. Resolving their
      // verified conflicts proves precisely the parent assumptions impossible.
      ++replay_resolutions;
      remember(path);
      return Outcome::Refuted;
    };
    const auto result = visit();
    replay_refuted = result == Outcome::Refuted;
    replay_model = result == Outcome::Model;
    replay_clauses = clauses.size() - 1;
    if (replay_refuted)
      return manager.ASTFalse;
    if (replay_model)
      return manager.ASTTrue;
    return clauses.size() == 1 ? input : manager.CreateNode(AND, clauses);
  }

  bool mipModel(Engine& engine, LraReconstruction* reconstruction)
  {
    if (binaries.empty() ||
        (!reconstruction && !manager.UserFlags.lra_highs_cuts) ||
        budget.remaining() <= 0)
      return false;
    for (const auto c : binaries)
    {
      if (Highs_changeColIntegrality(engine.ptr, static_cast<HighsInt>(c),
                                     kHighsVarTypeInteger) ==
              kHighsStatusError ||
          Highs_changeColBounds(engine.ptr, static_cast<HighsInt>(c), 0.0,
                                1.0) == kHighsStatusError)
        return false;
    }
#ifdef STP_HAVE_HIGHS_CUT_LOG
    if (manager.UserFlags.lra_highs_cuts)
    {
      if (Highs_getStpRootCutLogVersion() != 1)
        return false;
      Highs_setCallback(engine.ptr, cutCallback, this);
      Highs_startCallback(engine.ptr, kHighsCallbackMipRootCutRecipe);
      if (!manager.UserFlags.lra_highs_mip)
        Highs_setIntOptionValue(engine.ptr, "mip_max_nodes", 1);
    }
#endif
    Highs_setStringOptionValue(engine.ptr, "solver", "choose");
    Highs_setIntOptionValue(engine.ptr, "mip_max_improving_sols", 1);
    if (!run(engine, true))
      return false;
    HighsInt primalStatus = 0;
    if (Highs_getIntInfoValue(engine.ptr, "primal_solution_status",
                              &primalStatus) == kHighsStatusError ||
        primalStatus != kHighsSolutionStatusFeasible)
      return false;
    std::vector<double> primal(symbols.size());
    if (Highs_getSolution(engine.ptr, primal.data(), nullptr, nullptr,
                          nullptr) == kHighsStatusError)
      return false;
    const auto originalRows = rows.size();
    struct Restore
    {
      std::vector<Row>& rows;
      std::size_t size;
      ~Restore()
      {
        rows.erase(rows.begin() + static_cast<std::ptrdiff_t>(size),
                   rows.end());
      }
    } restore{rows, originalRows};
    {
      NumberOperationScope scope(numbers);
      for (const auto c : binaries)
      {
        if (!std::isfinite(primal[c]) || primal[c] < -1e-6 ||
            primal[c] > 1 + 1e-6)
          return false;
        // Rounding is only a proposal: all binary equations and the entire
        // original formula will be checked using exact arithmetic below.
        const auto bit = std::int64_t{primal[c] >= 0.5 ? 1 : 0};
        rows.push_back({{{c, ExactRational(std::int64_t{1})}},
                        ExactRational(bit),
                        true,
                        false});
      }
    }
    // A MIP incumbent has no valid LP basis. Recover one using the original
    // constraints and exact selector equations, with no imported MIP cuts.
    Engine fixed;
    if (load(fixed) && run(fixed) && certify(fixed, reconstruction, false))
    {
      ++mip_models;
      return true;
    }
    return false;
  }
};
} // namespace
#endif

bool highsEnabledForQuery(STPMgr& manager, const ASTNode& input,
                          SATSolver* solver)
{
#ifdef STP_HAVE_HIGHS
  const auto& flags = manager.UserFlags;
  if (flags.lra_highs_lp || flags.lra_highs_cuts || flags.lra_highs_replay)
    return true;
  if (!flags.lra_highs_mip || flags.lra_highs_seconds == 0)
    return false;
  try
  {
    Budget budget(solver, flags.lra_highs_seconds);
    Frontend frontend(manager);
    ASTVec work{input};
    std::unordered_set<std::uint64_t> seen;
    while (!work.empty() && seen.size() < 200000 && budget.remaining() > 0)
    {
      const auto node = work.back();
      work.pop_back();
      if (!seen.insert(node.GetNodeNum()).second)
        continue;
      if (node.GetKind() == AND)
        for (const auto& child : node.GetChildren())
          work.push_back(child);
      else if (frontend.binaryDomainSymbol(node))
        return true;
    }
  }
  catch (const std::exception&)
  {
    // Eligibility is advisory and read-only. Unsupported candidates and
    // exhausted resources leave ordinary solving available.
  }
#else
  (void)manager;
  (void)input;
  (void)solver;
#endif
  return false;
}

ASTNode presolveHighs(STPMgr& manager, const ASTNode& input, SATSolver* solver,
                      LraReconstruction* reconstruction, NumberBudget& numbers)
{
#ifdef STP_HAVE_HIGHS
  // Without storage a certified candidate is not turned into replay
  // definitions, so a caller that declines replay still gets refutations.
  if (reconstruction && !reconstruction->replay_allowed)
    reconstruction = nullptr;
  Proposal proposal(manager, solver, numbers);
  try
  {
    proposal.collect(input);
    if (proposal.constant_conflict)
      return manager.ASTFalse;
    Engine engine;
    if (proposal.load(engine))
    {
      if (proposal.run(engine))
      {
        if (proposal.lp_status == kHighsModelStatusOptimal)
        {
          proposal.root_values.resize(proposal.symbols.size());
          if (Highs_getSolution(engine.ptr, proposal.root_values.data(),
                                nullptr, nullptr, nullptr) == kHighsStatusError)
            proposal.root_values.clear();
        }
        if (proposal.certify(engine, reconstruction))
          return proposal.rays ? manager.ASTFalse : manager.ASTTrue;
      }
      if ((manager.UserFlags.lra_highs_mip ||
           manager.UserFlags.lra_highs_cuts) &&
          proposal.mipModel(engine, reconstruction))
        return manager.ASTTrue;
      ASTNode refined =
          manager.UserFlags.lra_highs_cuts ? proposal.rootCuts(input) : input;
      if (manager.UserFlags.lra_highs_replay)
        return proposal.replay(refined, reconstruction);
      return refined;
    }
  }
  catch (const std::exception& e)
  {
    if (manager.UserFlags.stats_flag)
      std::cerr << "LRA HiGHS declined: " << e.what() << '\n';
  }
#else
  (void)manager;
  (void)solver;
  (void)reconstruction;
  (void)numbers;
#endif
  return input;
}
} // namespace stp::lra

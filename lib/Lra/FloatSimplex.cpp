#include "FloatSimplex.h"
#include "SoiSearch.h"

#include <algorithm>
#include <cmath>
#include <stdexcept>

namespace stp::lra
{

namespace
{

/* Feasibility tests are tolerant; bound bookkeeping is not.  A wrong call
 * here misroutes -- a wasted exact check, a delayed conflict -- and the
 * exact tier judges, so the constants are chosen to absorb accumulated
 * pivot rounding, not to be sharp. */
constexpr double kAbsoluteTolerance = 1e-9;
constexpr double kRelativeTolerance = 1e-12;
/* Substitution leaves cancellation residues; cells this small are noise
 * from an exact zero and dropping them keeps rows short.  Advisory-tier
 * licence: dropping a genuinely tiny coefficient can only misroute.  A
 * residue that survives becomes a certificate term with a weight around
 * 1e-11 whose true value is zero, and the exact combination then fails
 * to cancel -- seen as a hundred rejected certificates per solve at the
 * tighter setting. */
constexpr double kDropTolerance = 1e-9;

/* The cross-link is only free while it fits the padding the variable
 * leaves; if the cell ever grows, the trade has to be re-argued. */
static_assert(sizeof(FloatSimplex::Term) == 16,
              "FloatSimplex::Term must stay two words");
/* The largest infinitesimal coefficient an assignment may carry.  A
 * double holds about sixteen significant digits, so a row sum whose
 * terms reach 1e16 can no longer resolve a difference of one; the cap
 * keeps four digits of headroom under that.  Bound deltas are units,
 * so nothing legitimate comes near it. */
constexpr double kInfinitesimalCap = 1e12;
/* Trips past this many rebuilds ask the caller for a fresh factorized
 * tier instead of another rebuild: one rebuild rescues sc-20 and
 * NoriSharma, whose blow-up is a single spike; a second trip is the
 * tableau's own history, which a rebuild replays and a fresh factor over
 * the pristine rows does not. */
constexpr std::uint64_t kPromoteAfterRebuilds = 1;
/* Factorized mode: a direction component at the violated variable below
 * this is no pivot. */
constexpr double kTinyPivot = 1.0e-12;

bool cellBeforeVariable(FloatSimplex::Term const& cell,
                        FloatSimplex::Var variable) noexcept;

/* The absolute floor belongs to the caller's units: for a variable the
 * tableau holds scaled it scales with the variable, and the relative part
 * is what it was. */
double toleranceAt(double reference, double scale = 1.0) noexcept
{
  return kAbsoluteTolerance * scale + kRelativeTolerance * std::fabs(reference);
}

/* Tolerant comparisons for feasibility routing: lexicographic on
 * (value, delta), each component within tolerance of the bound. */
bool belowBound(FloatSimplex::DVal const& value,
                FloatSimplex::DVal const& bound, double scale = 1.0) noexcept
{
  double const tolerance = toleranceAt(bound.value, scale);
  if (value.value < bound.value - tolerance)
    return true;
  if (value.value > bound.value + tolerance)
    return false;
  return value.delta < bound.delta - tolerance;
}

bool aboveBound(FloatSimplex::DVal const& value,
                FloatSimplex::DVal const& bound, double scale = 1.0) noexcept
{
  double const tolerance = toleranceAt(bound.value, scale);
  if (value.value > bound.value + tolerance)
    return true;
  if (value.value < bound.value - tolerance)
    return false;
  return value.delta > bound.delta + tolerance;
}

/* Exact lexicographic ordering over the stored doubles, for bound
 * bookkeeping and the trail. */
bool boundStrictlyLess(FloatSimplex::DVal const& left,
                       FloatSimplex::DVal const& right) noexcept
{
  return left.value < right.value ||
         (left.value == right.value && left.delta < right.delta);
}

}  // namespace

std::optional<bool> FloatSimplex::preferredPolarity(Atom atom) const noexcept
{
  if (!buildUsable() || poisoned_ || wants_promotion_ || atom >= atoms_.size())
    return std::nullopt;
  auto const& info = atoms_[atom];
  std::size_t work = 0;
  DVal const value = evaluateVariable(info.variable, 0, work);
  double const gap = value.value - info.threshold;
  double const tolerance = toleranceAt(
      std::max(std::fabs(value.value), std::fabs(info.threshold)), scale_[info.variable]);
  if (!std::isfinite(value.value) || !std::isfinite(value.delta) ||
      !std::isfinite(gap) || std::fabs(gap) <= tolerance)
    return std::nullopt;
  switch (info.relation)
  {
    case Relation::Less:
    case Relation::LessEqual: return gap < 0.0;
    case Relation::Greater:
    case Relation::GreaterEqual: return gap > 0.0;
  }
  return std::nullopt;
}

FloatSimplex::DVal FloatSimplex::evaluateVariable(Var variable, unsigned depth,
                                                  std::size_t& work) const noexcept
{
  /* A dormant row's basic keeps no maintained value; its row over the
   * current assignment gives one.  Read-only: the row is not rewritten,
   * so a term that has since entered the basis is followed into its own
   * row (an active row is current; a dormant one recurses).  Bounded in
   * depth and cells, past which the stale value is returned -- this
   * serves advice and model seeds, both of which the exact tier judges. */
  if (!dormant_rows_ || factorized_ || variable >= row_of_basic_.size())
    return alpha_[variable];
  std::uint32_t const row_index = row_of_basic_[variable];
  if (row_index == kNoRow || row_dormant_[row_index] == 0 || depth >= 32U)
    return alpha_[variable];
  DVal accumulated{0.0, 0.0};
  for (Term const& cell : rows_[row_index].cells)
  {
    if (++work > 4096U)
      return alpha_[variable];
    DVal const held = evaluateVariable(cell.variable, depth + 1U, work);
    accumulated.value += cell.coefficient * held.value;
    accumulated.delta += cell.coefficient * held.delta;
  }
  ++dormant_evaluations_;
  return accumulated;
}

FloatSimplex::DVal FloatSimplex::assignmentOf(Var variable) const noexcept
{
  std::size_t work = 0;
  DVal const value = evaluateVariable(variable, 0, work);
  double const scale = scale_.empty() ? 1.0 : scale_[variable];
  return DVal{value.value / scale, value.delta / scale};
}

FloatSimplex::Var FloatSimplex::addColumn()
{
  Var const variable = static_cast<Var>(cols_.size());
  cols_.emplace_back();
  row_of_basic_.push_back(kNoRow);
  lower_.push_back(DVal{0.0, 0.0});
  upper_.push_back(DVal{0.0, 0.0});
  has_lower_.push_back(0);
  has_upper_.push_back(0);
  lower_atom_.push_back(kNoAtom);
  upper_atom_.push_back(kNoAtom);
  lower_positive_.push_back(0);
  upper_positive_.push_back(0);
  lower_asserted_.emplace_back();
  upper_asserted_.emplace_back();
  if (finalized_)
  {
    alpha_.emplace_back();
    scale_.push_back(1.0);
    pristine_cols_.emplace_back();
    row_index_of_rowvar_.push_back(kNoRow);
    if (movement_initialized_)
      movement_.push_back(3);
    if (factorized_)
    {
      variable_basic_.push_back(0);
      basis_position_.push_back(-1);
      direction_.push_back(0.0);
      gather_.push_back(0.0);
    }
  }
  return variable;
}

namespace
{
/* Lexicographic (value, delta) with a margin: the residual is computed
 * in doubles, and a generalisation that only just contradicts would be
 * a rejected certificate, not a wrong answer -- but a rejected
 * certificate costs an exact replay, so the margin errs conservative. */
bool residualNegative(FloatSimplex::DVal const& residual,
                      double scale = 1.0) noexcept
{
  double const margin = 1.0e-9 * scale + 1.0e-12 * std::fabs(residual.value);
  if (residual.value < -margin)
    return true;
  if (residual.value > margin)
    return false;
  return residual.delta < -margin;
}
}  // namespace

void FloatSimplex::emitCertificate()
{
  /* The residual: each bound weighted by its Farkas coefficient, lower
   * bounds subtracted; the conflict is the claim that it is negative.
   * Any slack below zero can be spent moving a bound outwards to a
   * weaker one the search has also asserted -- weakest first, greedy,
   * left to right, as the exact tier does it. */
  DVal residual{0.0, 0.0};
  for (SupportTerm const& term : support_scratch_)
  {
    double const sign = term.upper ? 1.0 : -1.0;
    residual.value += sign * term.weight * term.bound.value;
    residual.delta += sign * term.weight * term.bound.delta;
  }
  /* The residual is in the violated variable's units, the first term's. */
  double const residual_scale =
      support_scratch_.empty() ? 1.0 : scaleOf(support_scratch_.front().variable);
  if (residualNegative(residual, residual_scale))
  {
    for (SupportTerm& term : support_scratch_)
    {
      std::vector<AssertedBound> const& asserted =
          term.upper ? upper_asserted_[term.variable]
                     : lower_asserted_[term.variable];
      AssertedBound const* best = nullptr;
      DVal best_residual = residual;
      for (AssertedBound const& candidate : asserted)
      {
        if (candidate.atom == term.atom)
          continue;
        /* Weaker means larger for an upper bound, smaller for a lower
         * one; the strictly-better test keeps the weakest found. */
        bool const weaker =
            term.upper ? boundStrictlyLess(term.bound, candidate.bound)
                       : boundStrictlyLess(candidate.bound, term.bound);
        if (!weaker)
          continue;
        if (best != nullptr)
        {
          bool const weaker_than_best =
              term.upper ? boundStrictlyLess(best->bound, candidate.bound)
                         : boundStrictlyLess(candidate.bound, best->bound);
          if (!weaker_than_best)
            continue;
        }
        double const sign = term.upper ? 1.0 : -1.0;
        DVal proposed = residual;
        proposed.value +=
            sign * term.weight * (candidate.bound.value - term.bound.value);
        proposed.delta +=
            sign * term.weight * (candidate.bound.delta - term.bound.delta);
        if (!residualNegative(proposed, residual_scale))
          continue;
        best = &candidate;
        best_residual = proposed;
      }
      if (best != nullptr)
      {
        term.atom = best->atom;
        term.positive = best->positive;
        term.bound = best->bound;
        residual = best_residual;
        ++generalisations_;
      }
    }
  }
  certificate_.items.clear();
  certificate_.items.reserve(support_scratch_.size());
  for (SupportTerm const& term : support_scratch_)
  {
    /* A bound on a scaled variable is the caller's bound times the
     * scale, so the caller's weight is this weight times the scale --
     * an exact power of two, which keeps the weight a dyadic. */
    double const scale = scale_.empty() ? 1.0 : scale_[term.variable];
    certificate_.items.push_back(
        CertificateItem{term.atom, term.positive, term.weight * scale});
  }
}

FloatSimplex::Var FloatSimplex::addRow(const Term* begin, const Term* end)
{
  if (finalized_)
    return appendRow(begin, end);
  Var const basic = addColumn();
  std::uint32_t const row_index = static_cast<std::uint32_t>(rows_.size());
  rows_.emplace_back();
  rows_.back().basic = basic;
  row_of_basic_[basic] = row_index;
  for (const Term* term = begin; term != end; ++term)
  {
    noteFinite(term->coefficient);
    if (term->coefficient != 0.0)
      addCell(row_index, term->variable, term->coefficient);
  }
  return basic;
}

FloatSimplex::Var FloatSimplex::appendRow(const Term* begin, const Term* end)
{
  // New rows are stated over structural variables in caller units. Keep
  // the old basis and normalize just the new row into its coordinates.
  for (auto term = begin; term != end; ++term)
    if (term->variable >= cols_.size() ||
        row_index_of_rowvar_[term->variable] != kNoRow)
      throw std::invalid_argument("appended float row requires structural variables");
  Var const basic = addColumn();
  auto const index = static_cast<std::uint32_t>(rows_.size());
  Row original;
  original.basic = basic;
  double largest = 0.0;
  for (auto term = begin; term != end; ++term)
    largest = std::fmax(largest, std::fabs(term->coefficient));
  if (largest > 0.0 && std::isfinite(largest))
  {
    int exponent = 0;
    std::frexp(largest, &exponent);
    scale_[basic] = std::ldexp(1.0, 1 - exponent);
  }
  for (auto term = begin; term != end; ++term)
  {
    double const a = term->coefficient * scale_[basic] / scale_[term->variable];
    noteFinite(a);
    original.cells.push_back(Term{term->variable, a});
  }
  std::sort(original.cells.begin(), original.cells.end(), [](Term const& a, Term const& b) {
    return a.variable < b.variable;
  });
  std::vector<Term> merged;
  for (auto const& cell : original.cells)
  {
    if (!merged.empty() && merged.back().variable == cell.variable)
    {
      merged.back().coefficient += cell.coefficient;
      if (merged.back().coefficient == 0.0)
        merged.pop_back();
    }
    else if (cell.coefficient != 0.0)
      merged.push_back(cell);
  }
  original.cells.swap(merged);
  for (auto const& cell : original.cells)
    pristine_cols_[cell.variable].push_back(Term{index, cell.coefficient});
  pristine_rows_.push_back(original);
  pristine_nonzeros_ += original.cells.size();
  row_index_of_rowvar_[basic] = index;
  rows_.emplace_back();
  rows_.back().basic = basic;
  row_of_basic_[basic] = index;
  row_touched_.push_back(0);
  row_violated_.push_back(0);
  row_queued_.push_back(0);
  row_dormant_.push_back(0);
  row_visiting_.push_back(0);
  touched_rows_.reserve(rows_.size());
  violated_rows_.reserve(rows_.size());
  conflict_rows_.reserve(rows_.size());
  updateWorkBudgets();
  if (factorized_)
  {
    // Append an identity column/row to the old basis header. Refactor the
    // enlarged matrix on demand; no old basic variable is displaced.
    rows_.back().cells = original.cells;
    variable_basic_[basic] = 1;
    basis_position_[basic] = static_cast<std::int32_t>(basis_header_.size());
    basis_header_.push_back(basic);
    basis_stale_ = true;
    recomputeRow(index, true);
  }
  else
  {
    std::vector<Term> expanded;
    for (Term const& cell : original.cells)
    {
      auto const inner = row_of_basic_[cell.variable];
      if (inner == kNoRow)
        expanded.push_back(cell);
      else
      {
        /* A structural in the basis has an active row (it entered by a
         * pivot on one); the dormant case is defensive. */
        if (row_dormant_[inner] != 0)
          normaliseDormantRow(inner);
        for (Term const& held : rows_[inner].cells)
          expanded.push_back(Term{held.variable, held.coefficient * cell.coefficient});
      }
    }
    std::sort(expanded.begin(), expanded.end(), [](Term const& a, Term const& b) {
      return a.variable < b.variable;
    });
    /* An appended row has no bound yet: under dormancy, and if it is wide
     * enough to be worth deferring, it holds its cells and stays out of
     * the columns until one arrives. */
    std::vector<Term> built;
    for (std::size_t i = 0; i < expanded.size();)
    {
      Var const v = expanded[i].variable;
      double a = 0.0;
      do { a += expanded[i++].coefficient; }
      while (i < expanded.size() && expanded[i].variable == v);
      noteFinite(a);
      if (a != 0.0)
        built.push_back(Term{v, 0, a});
    }
    bool const dormant = dormant_rows_ && !boundedVariable(basic) &&
                         built.size() >= dormant_min_cells_;
    if (dormant)
      rows_[index].cells = built;
    else
      for (Term const& term : built)
        addCell(index, term.variable, term.coefficient);
    if (dormant)
    {
      row_dormant_[index] = 1;
      ++dormant_count_;
    }
    else
    {
      queueConflictRow(index, true);
      recomputeRow(index, false);
    }
  }
  return basic;
}

FloatSimplex::Atom FloatSimplex::addAtom(Var row_variable,
                                         Relation positive_relation,
                                         double threshold)
{
  if (finalized_)
    threshold *= scale_[row_variable];
  noteFinite(threshold);
  Atom const atom = static_cast<Atom>(atoms_.size());
  atoms_.push_back(AtomInfo{row_variable, positive_relation, threshold});
  return atom;
}

bool FloatSimplex::finalize()
{
  alpha_.assign(cols_.size(), DVal{0.0, 0.0});
  pristine_nonzeros_ = 0;
  for (const auto& row : rows_)
    pristine_nonzeros_ += row.cells.size();
  updateWorkBudgets();
  row_touched_.assign(rows_.size(), 1);
  touched_rows_.clear();
  touched_rows_.reserve(rows_.size());
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
    touched_rows_.push_back(row_index);
  row_violated_.assign(rows_.size(), 0);
  row_queued_.assign(rows_.size(), 0);
  row_dormant_.assign(rows_.size(), 0);
  row_visiting_.assign(rows_.size(), 0);
  dormant_count_ = 0;
  violated_rows_.clear();
  violated_rows_.reserve(rows_.size());
  refresh_debt_ = 0;
  equilibrate();
  pristine_rows_ = rows_;
  pristine_cols_.assign(cols_.size(), {});
  row_index_of_rowvar_.assign(cols_.size(), kNoRow);
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(pristine_rows_.size());
       ++row_index)
  {
    row_index_of_rowvar_[pristine_rows_[row_index].basic] = row_index;
    for (const Term& cell : pristine_rows_[row_index].cells)
      pristine_cols_[cell.variable].push_back(
          Term{row_index, cell.coefficient});
  }
  if (dormant_rows_)
    dormantUnboundedRows();
  finalized_ = true;
  return buildUsable();
}

void FloatSimplex::setDormantRows(bool enabled, std::uint32_t min_cells)
{
  dormant_min_cells_ = min_cells;
  if (!finalized_)
  {
    dormant_rows_ = enabled;
    return;
  }
  if (!trail_.empty())
    throw std::runtime_error("float row dormancy requires no asserted bounds");
  if (enabled == dormant_rows_)
    return;
  dormant_rows_ = enabled;
  if (factorized_)
    return;
  if (enabled)
  {
    dormantUnboundedRows();
    return;
  }
  /* Disabling: bring every dormant row back.  No bound is asserted, so
   * nothing can be violated and nothing needs judging. */
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
  {
    if (row_dormant_[row_index] == 0)
      continue;
    normaliseDormantRow(row_index);
    if (poisoned_)
      return;
    recomputeRow(row_index, false);
    row_dormant_[row_index] = 0;
    linkRow(row_index);
  }
  dormant_count_ = 0;
}

void FloatSimplex::unlinkRow(std::uint32_t row_index) noexcept
{
  for (Term const& cell : rows_[row_index].cells)
    eraseColumnEntry(cell.variable, cell.col_position, row_index);
}

void FloatSimplex::linkRow(std::uint32_t row_index) noexcept
{
  for (Term& cell : rows_[row_index].cells)
  {
    cell.col_position = static_cast<std::uint32_t>(cols_[cell.variable].size());
    cols_[cell.variable].push_back(row_index);
  }
}

void FloatSimplex::dormantUnboundedRows() noexcept
{
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
  {
    if (row_dormant_[row_index] != 0 || boundedVariable(rows_[row_index].basic) ||
        rows_[row_index].cells.size() < dormant_min_cells_)
      continue;
    unlinkRow(row_index);
    row_dormant_[row_index] = 1;
    row_violated_[row_index] = 0;
    ++dormant_count_;
  }
  /* A dormant row is not on the frontier: it holds no value to verify. */
  std::size_t keep = 0;
  for (std::size_t i = 0; i < touched_rows_.size(); ++i)
  {
    std::uint32_t const candidate = touched_rows_[i];
    if (row_dormant_[candidate] != 0)
      row_touched_[candidate] = 0;
    else
      touched_rows_[keep++] = candidate;
  }
  touched_rows_.resize(keep);
}

void FloatSimplex::normaliseDormantRow(std::uint32_t row_index)
{
  /* Replace every term that is no longer nonbasic by its row.  A term was
   * nonbasic when this row was last written, so a row it now refers to
   * was written later: the references form a DAG, and a cycle is a
   * broken invariant this tier answers with poison rather than a throw. */
  std::vector<Term>& cells = rows_[row_index].cells;
  bool pending = false;
  for (Term const& cell : cells)
    if (row_of_basic_[cell.variable] != kNoRow)
    {
      pending = true;
      break;
    }
  if (!pending)
    return;
  if (row_visiting_[row_index] != 0)
  {
    poisoned_ = true;
    return;
  }
  row_visiting_[row_index] = 1;
  std::vector<Term> result;
  result.reserve(cells.size() * 2U);
  for (Term const& cell : cells)
  {
    std::uint32_t const inner = row_of_basic_[cell.variable];
    if (inner == kNoRow)
    {
      result.push_back(Term{cell.variable, 0, cell.coefficient});
      continue;
    }
    if (row_dormant_[inner] != 0)
    {
      normaliseDormantRow(inner);
      if (poisoned_)
      {
        row_visiting_[row_index] = 0;
        return;
      }
    }
    for (Term const& held : rows_[inner].cells)
      result.push_back(Term{held.variable, 0, cell.coefficient * held.coefficient});
  }
  std::sort(result.begin(), result.end(), [](Term const& a, Term const& b) {
    return a.variable < b.variable;
  });
  std::vector<Term> merged;
  merged.reserve(result.size());
  for (Term const& term : result)
  {
    if (!merged.empty() && merged.back().variable == term.variable)
    {
      merged.back().coefficient += term.coefficient;
      if (std::fabs(merged.back().coefficient) < kDropTolerance)
        merged.pop_back();
      continue;
    }
    if (std::fabs(term.coefficient) < kDropTolerance)
      continue;
    merged.push_back(term);
  }
  for (Term const& term : merged)
    noteFinite(term.coefficient);
  if (!finite_inputs_)
    poisoned_ = true;
  cells.swap(merged);
  row_visiting_[row_index] = 0;
}

void FloatSimplex::activateRow(std::uint32_t row_index)
{
  ++activations_;
  if (dormant_count_ != 0)
    --dormant_count_;
  normaliseDormantRow(row_index);
  if (poisoned_)
    return;
  Row& row = rows_[row_index];
  DVal fresh{0.0, 0.0};
  for (Term const& cell : row.cells)
  {
    fresh.value += cell.coefficient * alpha_[cell.variable].value;
    fresh.delta += cell.coefficient * alpha_[cell.variable].delta;
  }
  if (!std::isfinite(fresh.value) || !std::isfinite(fresh.delta))
  {
    poisoned_ = true;
    return;
  }
  alpha_[row.basic] = fresh;
  noteInfinitesimal(fresh);
  row_dormant_[row_index] = 0;
  linkRow(row_index);
  queueConflictRow(row_index, true);
  markViolation(row_index, row.basic);
}

/* Row scaling in powers of two.  Each row is scaled by the power of two
 * that brings its largest coefficient into [1, 2): an instance whose rows
 * mix 0.004 and 500, as the clock-synchronisation family does, otherwise
 * turns a few substitutions into coefficients spanning ten binades, and the
 * tableau's doubles stop certifying.  A row variable r = sum a x becomes
 * s*r = sum (s a) x: its scale is its row's s, a structural's is one, and
 * a cell's coefficient is multiplied by the row's scale and divided by its
 * variable's.  Thresholds follow their variable's scale; the relation's
 * direction does not change, every scale being positive.  Columns are
 * deliberately left alone: scaling them as well was measured to help
 * nothing that row scaling had not and to cost the flux-balance LPs, whose
 * column scales reach 2^-16.  Powers of two keep every scaled value, and
 * every certificate weight unscaled on the way out, an exact dyadic. */
void FloatSimplex::equilibrate()
{
  scale_.assign(cols_.size(), 1.0);
  if (rows_.empty())
    return;
  auto const power_of_two_near = [](double magnitude) {
    if (!(magnitude > 0.0) || !std::isfinite(magnitude))
      return 1.0;
    int exponent = 0;
    std::frexp(magnitude, &exponent);  // magnitude = m * 2^exponent, m in [0.5, 1)
    return std::ldexp(1.0, 1 - exponent);  // brings magnitude into [1, 2)
  };
  for (std::size_t row_index = 0; row_index < rows_.size(); ++row_index)
  {
    double largest = 0.0;
    for (Term const& cell : rows_[row_index].cells)
      largest = std::fmax(largest, std::fabs(cell.coefficient));
    scale_[rows_[row_index].basic] = power_of_two_near(largest);
  }
  for (std::size_t row_index = 0; row_index < rows_.size(); ++row_index)
  {
    double const row_scale = scale_[rows_[row_index].basic];
    for (Term& cell : rows_[row_index].cells)
      cell.coefficient = cell.coefficient * row_scale / scale_[cell.variable];
  }
  for (AtomInfo& info : atoms_)
    info.threshold *= scale_[info.variable];
}

void FloatSimplex::rebuildAssignment()
{
  ++rebuilds_;
  std::fill(alpha_.begin(), alpha_.end(), DVal{0.0, 0.0});
  assignment_unusable_ = false;
  poisoned_ = false;
  /* Both of these recompute every basic row variable from its own row
   * over the assignment just zeroed, which is the origin either way. */
  if (factorized_)
    switchToFactorized();
  else
    restartBasis();
}

void FloatSimplex::resetSearchState(bool basis_only)
{
  if (!trail_.empty())
    throw std::runtime_error("float search reset requires no asserted bounds");
  const auto restarts = restarts_;
  const auto rebuilds = rebuilds_;
  if (basis_only)
    restartBasis();
  else
    rebuildAssignment();
  restarts_ = restarts;
  rebuilds_ = rebuilds;
}

bool FloatSimplex::rebuildBudgetSpent() const noexcept
{
  /* One rebuild rescues an instance whose assignment went bad once --
   * measured on sc-20, which needs exactly one and then runs clean.  An
   * instance that needs a stream of them is telling us the tier cannot
   * hold it: every rebuild throws the warm basis away and starts from
   * the origin, so the eight to thirty-five rebuilds seen on the
   * LassoRanker phase templates cost far more than degrading to the
   * exact mirror would.  Past the budget the check abandons instead,
   * and the caller's abandonment cascade takes over. */
  return rebuilds_ >= 2;
}

void FloatSimplex::noteInfinitesimal(DVal const& value) noexcept
{
  if (std::fabs(value.delta) > kInfinitesimalCap)
  {
    if (!assignment_unusable_ && rebuilds_ >= kPromoteAfterRebuilds)
      wants_promotion_ = true;
    assignment_unusable_ = true;
  }
}

void FloatSimplex::setDenseRecovery(bool enabled) noexcept
{
  dense_recovery_ = enabled;
  updateWorkBudgets();
}

void FloatSimplex::updateWorkBudgets() noexcept
{
  check_pivot_cap_ = 10U * static_cast<std::uint64_t>(rows_.size()) + 1000U;
  check_merge_cap_ = 100U * static_cast<std::uint64_t>(rows_.size()) + 50000U;
  if (dense_recovery_)
    check_merge_cap_ = std::max(
        check_merge_cap_,
        4U * std::min(pristine_nonzeros_, std::uint64_t{2000000}) + 50000U);
}

void FloatSimplex::restartBasis()
{
  movement_initialized_ = false;
  if (factorized_)
  {
    switchToFactorized();  // fresh slack basis in the same representation
    return;
  }
  rows_ = pristine_rows_;
  for (std::vector<std::uint32_t>& bucket : cols_)
    bucket.clear();
  std::fill(row_of_basic_.begin(), row_of_basic_.end(), kNoRow);
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
  {
    row_of_basic_[rows_[row_index].basic] = row_index;
    for (Term& cell : rows_[row_index].cells)
    {
      cell.col_position =
          static_cast<std::uint32_t>(cols_[cell.variable].size());
      cols_[cell.variable].push_back(row_index);
    }
  }
  /* Nonbasic assignments persist; every row variable is basic again and
   * its assignment is recomputed when the frontier drains it. */
  row_touched_.assign(rows_.size(), 1);
  touched_rows_.clear();
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
    touched_rows_.push_back(row_index);
  row_violated_.assign(rows_.size(), 0);
  row_queued_.assign(rows_.size(), 0);
  row_dormant_.assign(rows_.size(), 0);
  row_visiting_.assign(rows_.size(), 0);
  dormant_count_ = 0;
  violated_rows_.clear();
  refresh_debt_ = 0;
  last_conflict_row_ = kNoRow;
  certificate_.valid = false;
  poisoned_ = false;
  /* Pristine rows are over structurals, nonbasic in the slack basis, so
   * the unbounded ones go dormant without normalising. */
  if (dormant_rows_)
    dormantUnboundedRows();
  ++restarts_;
}

void FloatSimplex::switchToFactorized()
{
  movement_initialized_ = false;
  /* Slack basis: every row variable basic at its own row's position, the
   * basis matrix the identity.  Nonbasic assignments persist; every basic
   * row variable's assignment is recomputed directly from its pristine
   * row. */
  factorized_ = true;
  row_dormant_.assign(pristine_rows_.size(), 0);
  row_visiting_.assign(pristine_rows_.size(), 0);
  dormant_count_ = 0;
  direction_.assign(cols_.size(), 0.0);
  direction_touched_.clear();
  gather_.assign(cols_.size(), 0.0);
  gather_touched_.clear();
  factorized_dismissed_ = kNoVar;
  factorized_last_violated_ = kNoVar;
  variable_basic_.assign(cols_.size(), 0);
  basis_position_.assign(cols_.size(), -1);
  basis_header_.assign(pristine_rows_.size(), kNoVar);
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(pristine_rows_.size());
       ++row_index)
  {
    Var const basic = pristine_rows_[row_index].basic;
    variable_basic_[basic] = 1;
    basis_header_[row_index] = basic;
    basis_position_[basic] = static_cast<std::int32_t>(row_index);
  }
  basis_stale_ = true;
  row_violated_.assign(pristine_rows_.size(), 0);
  row_queued_.assign(pristine_rows_.size(), 0);
  violated_rows_.clear();
  refresh_debt_ = 0;
  poisoned_ = false;
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(pristine_rows_.size());
       ++row_index)
  {
    if (!recomputeRow(row_index, true))
      break;
  }
  last_conflict_row_ = kNoRow;
  certificate_.valid = false;
  poisoned_ = false;
  ++restarts_;
}

bool FloatSimplex::factorizedRefactor()
{
  /* The basis matrix, column by column from the header: a basic row
   * variable is a unit column at its own row, a basic structural is its
   * pristine column with the sign of [I | -C]. */
  std::size_t const dimension = pristine_rows_.size();
  basis_columns_.resize(dimension);
  for (std::size_t position = 0; position < dimension; ++position)
  {
    Var const basic = basis_header_[position];
    std::vector<FloatBasis::Entry>& column = basis_columns_[position];
    column.clear();
    std::uint32_t const own_row = row_index_of_rowvar_[basic];
    if (own_row != kNoRow)
    {
      column.push_back(FloatBasis::Entry{own_row, 1.0});
      continue;
    }
    column.reserve(pristine_cols_[basic].size());
    for (const Term& entry : pristine_cols_[basic])
      column.push_back(FloatBasis::Entry{entry.variable, -entry.coefficient});
  }
  basis_stale_ = !basis_.refactor(static_cast<FloatBasis::Index>(dimension),
                                  basis_columns_);
  if (basis_stale_)
  {
    ++refactor_failures_;
    // Retry with stability-first full-column pricing, at most four times
    // per float core. A failure still requests a fresh slack basis upstream.
    if (dense_recovery_ && robust_refactors_ < 4)
    {
      ++robust_refactors_;
      basis_stale_ = !basis_.refactor(static_cast<FloatBasis::Index>(dimension),
                                      basis_columns_, true);
    }
  }
  refactor_failed_ = basis_stale_;
  return !basis_stale_;
}

bool FloatSimplex::factorizedDirection(Var variable)
{
  /* d = B^{-1} a_variable over basis positions, laid out per basic
   * variable in direction_.  The entering column is a unit column for a
   * row variable and -C[:, c] for a structural. */
  for (Var touched : direction_touched_)
    direction_[touched] = 0.0;
  direction_touched_.clear();
  if (basis_stale_ && !factorizedRefactor())
    return false;
  std::vector<double>& rhs = basis_scratch_;
  std::vector<FloatBasis::Index>& touched = basis_scratch_touched_;
  if (rhs.size() != pristine_rows_.size())
    rhs.assign(pristine_rows_.size(), 0.0);
  for (FloatBasis::Index const index : touched)
    rhs[index] = 0.0;
  touched.clear();
  std::uint32_t const own_row = row_index_of_rowvar_[variable];
  if (own_row != kNoRow)
  {
    rhs[own_row] = 1.0;
    touched.push_back(own_row);
  }
  else
  {
    for (const Term& entry : pristine_cols_[variable])
    {
      rhs[entry.variable] = -entry.coefficient;
      touched.push_back(entry.variable);
    }
  }
  if (!basis_.ftran(rhs, touched))
    return false;
  for (FloatBasis::Index const position : touched)
  {
    double const component = rhs[position];
    if (component == 0.0)
      continue;
    if (!std::isfinite(component))
    {
      poisoned_ = true;
      return false;
    }
    Var const basic = basis_header_[position];
    direction_[basic] = component;
    direction_touched_.push_back(basic);
  }
  return true;
}

void FloatSimplex::factorizedUpdateNonbasic(Var variable, DVal target)
{
  if (!factorizedDirection(variable))
  {
    poisoned_ = true;
    return;
  }
  double const value_delta = target.value - alpha_[variable].value;
  double const delta_delta = target.delta - alpha_[variable].delta;
  for (Var touched : direction_touched_)
  {
    /* Zero on apply: the touched list can hold duplicates when an
     * accumulation passes exactly through zero, and a second application
     * must be a no-op. */
    double const component = direction_[touched];
    direction_[touched] = 0.0;
    alpha_[touched].value -= component * value_delta;
    alpha_[touched].delta -= component * delta_delta;
    if (!std::isfinite(alpha_[touched].value) ||
        !std::isfinite(alpha_[touched].delta))
      poisoned_ = true;
    noteInfinitesimal(alpha_[touched]);
    /* Only basic row variables carry bounds; structural basics never
     * enter the violated set. */
    std::uint32_t const row_index = row_index_of_rowvar_[touched];
    if (row_index != kNoRow && variable_basic_[touched] != 0)
      markViolation(row_index, touched);
  }
  refresh_debt_ += direction_touched_.size();
  alpha_[variable] = target;
  noteInfinitesimal(alpha_[variable]);
}

FloatSimplex::Verdict FloatSimplex::factorizedCheck(
    ExactLraResourceObserver& observer)
{
  if (!buildUsable() || poisoned_)
    return Verdict::Abandoned;
  if (basis_stale_ && !factorizedRefactor())
    return Verdict::Abandoned;
  std::uint64_t check_pivots = 0;
  for (;;)
  {
    /* Violated pick over the maintained set.  The flags were set where
     * the basic assignments changed; the list is compacted here, and the
     * chosen variable is recomputed from its pristine constraint before
     * anything is built on it -- w_r equals its row over the current
     * assignment identically, so a fresh sum cannot be a drift artefact.
     * Fewest-cells pricing normally; strict Bland (minimum variable) once
     * a check has burned 256 pivots -- the heuristic alone can cycle, and
     * a cycling check should switch well before its budget is gone. */
    Var violated = kNoVar;
    std::uint32_t violated_row = kNoRow;
    std::size_t violated_cells = 0;
    bool needs_increase = false;
    bool const bland =
        check_pivots > std::min<std::uint64_t>(check_pivot_cap_ / 4, 256);
    for (;;)
    {
      violated = kNoVar;
      violated_row = kNoRow;
      std::size_t keep = 0;
      for (std::size_t i = 0; i < violated_rows_.size(); ++i)
      {
        std::uint32_t const row_index = violated_rows_[i];
        Var const candidate = pristine_rows_[row_index].basic;
        if (row_violated_[row_index] == 0 || variable_basic_[candidate] == 0)
        {
          row_violated_[row_index] = 0;
          row_queued_[row_index] = 0;
          continue;
        }
        /* Re-judge against the current bounds: an undo loosens bounds
         * without touching assignments. */
        DVal const& assignment = alpha_[candidate];
        bool increase = false;
        if (has_lower_[candidate] != 0 &&
            belowBound(assignment, lower_[candidate], scaleOf(candidate)))
          increase = true;
        else if (!(has_upper_[candidate] != 0 &&
                   aboveBound(assignment, upper_[candidate], scaleOf(candidate))))
        {
          row_violated_[row_index] = 0;
          row_queued_[row_index] = 0;
          continue;
        }
        violated_rows_[keep++] = row_index;
        if (candidate == factorized_dismissed_ &&
            assignment.value == dismissed_alpha_.value &&
            assignment.delta == dismissed_alpha_.delta &&
            lower_[candidate].value == dismissed_lower_.value &&
            lower_[candidate].delta == dismissed_lower_.delta &&
            upper_[candidate].value == dismissed_upper_.value &&
            upper_[candidate].delta == dismissed_upper_.delta)
          continue;
        std::size_t const cells = pristine_rows_[row_index].cells.size();
        bool better;
        if (violated == kNoVar)
          better = true;
        else if (bland)
          better = candidate < violated;
        else
          better = cells < violated_cells ||
                   (cells == violated_cells && candidate < violated);
        if (better)
        {
          violated = candidate;
          violated_row = row_index;
          violated_cells = cells;
          needs_increase = increase;
        }
      }
      violated_rows_.resize(keep);
      if (violated == kNoVar)
        return Verdict::Feasible;
      if (!recomputeRow(violated_row, true))
        return Verdict::Abandoned;
      if (row_violated_[violated_row] != 0)
      {
        needs_increase = has_lower_[violated] != 0 &&
                         belowBound(alpha_[violated], lower_[violated], scaleOf(violated));
        break;
      }
      /* The flag was drift; it is cleared now, pick again. */
    }
    if (observer.pollBeforePivot() != StopReason::Continue)
      return Verdict::Abandoned;
    /* BTRAN: the violated variable's tableau row.  rho solves B^T rho =
     * e_p for the violated variable's basis position, by row, and the
     * substitution-convention coefficient of nonbasic q in that row is
     * -(rho^T a_q): -rho_j for a nonbasic row variable w_j, and
     * sum_i rho_i C[i,c] for a structural x_c, gathered over the rows
     * rho reaches. */
    std::vector<Term>& row_coefficients = row_coefficients_;
    auto const computeRow = [&](Var target) -> bool {
      std::int32_t const target_position = basis_position_[target];
      if (target_position < 0)
      {
        poisoned_ = true;
        return false;
      }
      std::vector<double>& rho = basis_row_;
      std::vector<FloatBasis::Index>& rho_touched = basis_row_touched_;
      if (rho.size() != pristine_rows_.size())
        rho.assign(pristine_rows_.size(), 0.0);
      for (FloatBasis::Index const index : rho_touched)
        rho[index] = 0.0;
      rho_touched.clear();
      rho[static_cast<std::size_t>(target_position)] = 1.0;
      rho_touched.push_back(static_cast<FloatBasis::Index>(target_position));
      if (!basis_.btran(rho, rho_touched))
        return false;
      row_coefficients.clear();
      for (Var touched : gather_touched_)
        gather_[touched] = 0.0;
      gather_touched_.clear();
      for (std::uint32_t const row : rho_touched)
      {
        double const multiplier = rho[row];
        if (multiplier == 0.0)
          continue;
        if (!std::isfinite(multiplier))
        {
          poisoned_ = true;
          return false;
        }
        Var const row_variable = pristine_rows_[row].basic;
        if (variable_basic_[row_variable] == 0 &&
            std::fabs(multiplier) >= kDropTolerance)
          row_coefficients.push_back(Term{row_variable, -multiplier});
        for (const Term& cell : pristine_rows_[row].cells)
        {
          if (gather_[cell.variable] == 0.0)
            gather_touched_.push_back(cell.variable);
          gather_[cell.variable] += multiplier * cell.coefficient;
        }
      }
      for (Var touched : gather_touched_)
      {
        double const coefficient = gather_[touched];
        if (variable_basic_[touched] != 0)
          continue;  // basic structural
        if (std::fabs(coefficient) < kDropTolerance)
          continue;
        if (!std::isfinite(coefficient))
        {
          poisoned_ = true;
          return false;
        }
        row_coefficients.push_back(Term{touched, coefficient});
      }
      return true;
    };
    if (!computeRow(violated))
      return Verdict::Abandoned;
    /* Entering selection: same eligibility and fewest-holders pricing as
     * the substitution engine; structural variables have no bounds and
     * are always eligible.  The same scan can instead prefer the largest
     * coefficient, which the recovery below asks for when the pivot the
     * pricing chose turns out to be noise. */
    auto const selectEntering = [&](bool by_magnitude, Var excluded) -> Var {
      Var entering = kNoVar;
      std::size_t entering_holders = 0;
      double entering_magnitude = 0.0;
      for (const Term& candidate : row_coefficients)
      {
        if (candidate.variable == excluded)
          continue;
        bool const wants_higher =
            needs_increase == (candidate.coefficient > 0.0);
        bool eligible;
        if (row_index_of_rowvar_[candidate.variable] == kNoRow)
        {
          eligible = true;  // structural: unbounded either way
        }
        else if (wants_higher)
        {
          eligible = has_upper_[candidate.variable] == 0 ||
                     boundStrictlyLess(alpha_[candidate.variable],
                                       upper_[candidate.variable]);
        }
        else
        {
          eligible = has_lower_[candidate.variable] == 0 ||
                     boundStrictlyLess(lower_[candidate.variable],
                                       alpha_[candidate.variable]);
        }
        if (!eligible)
          continue;
        std::size_t const holders =
            row_index_of_rowvar_[candidate.variable] == kNoRow
                ? pristine_cols_[candidate.variable].size()
                : 1U;
        double const magnitude = std::fabs(candidate.coefficient);
        bool better;
        if (entering == kNoVar)
          better = true;
        else if (by_magnitude)
          better = magnitude > entering_magnitude;
        else if (bland)
          better = candidate.variable < entering;
        else
          better = holders < entering_holders ||
                   (holders == entering_holders &&
                    candidate.variable < entering);
        if (better)
        {
          entering = candidate.variable;
          entering_holders = holders;
          entering_magnitude = magnitude;
        }
      }
      return entering;
    };
    Var entering = selectEntering(false, kNoVar);
    /* A conflict clause is as long as the conflict row, and the pick
     * above could only price rows by their pristine length.  Before
     * certifying, look at the other violated basics and take the
     * shortest row among those that are conflicts themselves: a BTRAN
     * per candidate at conflict time, none per pivot.  The search pays
     * its own way: after a warm-up it continues only while one conflict
     * in eight has found a shorter row (the rows of a LassoRanker
     * template are uniformly short and the search there is pure cost;
     * on sc and miplib it halves the clauses), with the counts decayed
     * so a solve can change its mind. */
    bool const search_rows = shortest_examined_ < 128 ||
                             shortest_improved_ * 8 >= shortest_examined_;
    if (entering == kNoVar && search_rows)
    {
      Var best = violated;
      bool best_increase = needs_increase;
      std::size_t best_length = row_coefficients.size();
      std::vector<Term> best_row = row_coefficients;
      std::size_t const count = violated_rows_.size();
      if (++shortest_examined_ >= 1024)
      {
        shortest_examined_ /= 2;
        shortest_improved_ /= 2;
      }
      for (std::size_t i = 0; i < count; ++i)
      {
        std::uint32_t const row_index = violated_rows_[i];
        Var const candidate = pristine_rows_[row_index].basic;
        if (candidate == violated || variable_basic_[candidate] == 0 ||
            row_violated_[row_index] == 0)
          continue;
        if (!recomputeRow(row_index, true))
          return Verdict::Abandoned;
        if (row_violated_[row_index] == 0)
          continue;
        bool increase;
        if (has_lower_[candidate] != 0 &&
            belowBound(alpha_[candidate], lower_[candidate], scaleOf(candidate)))
          increase = true;
        else if (has_upper_[candidate] != 0 &&
                 aboveBound(alpha_[candidate], upper_[candidate], scaleOf(candidate)))
          increase = false;
        else
          continue;
        needs_increase = increase;
        if (!computeRow(candidate))
          return Verdict::Abandoned;
        if (selectEntering(false, kNoVar) != kNoVar)
          continue;
        if (row_coefficients.size() < best_length)
        {
          best = candidate;
          best_increase = increase;
          best_length = row_coefficients.size();
          best_row = row_coefficients;
        }
      }
      if (best != violated)
        ++shortest_improved_;
      violated = best;
      needs_increase = best_increase;
      violated_row = row_index_of_rowvar_[best];
      row_coefficients = best_row;
    }
    if (entering == kNoVar)
    {
      /* Certificate: the violated bound at weight one, each blocking
       * nonbasic row-variable bound at its coefficient magnitude. */
      certificate_.valid = true;
      certificate_.items.clear();
      support_scratch_.clear();
      Atom const violated_atom = needs_increase ? lower_atom_[violated]
                                                : upper_atom_[violated];
      bool const violated_positive =
          (needs_increase ? lower_positive_[violated]
                          : upper_positive_[violated]) != 0;
      if (violated_atom == kNoAtom)
        certificate_.valid = false;
      else
        support_scratch_.push_back(SupportTerm{
            violated_atom, violated_positive, 1.0, violated, !needs_increase,
            needs_increase ? lower_[violated] : upper_[violated]});
      for (const Term& candidate : row_coefficients)
      {
        if (row_index_of_rowvar_[candidate.variable] == kNoRow)
          continue;  // structural coefficients were all ineligible == zero
        bool const blocking_upper =
            needs_increase == (candidate.coefficient > 0.0);
        Atom const blocking_atom =
            blocking_upper ? upper_atom_[candidate.variable]
                           : lower_atom_[candidate.variable];
        bool const blocking_positive =
            (blocking_upper ? upper_positive_[candidate.variable]
                            : lower_positive_[candidate.variable]) != 0;
        if (blocking_atom == kNoAtom)
        {
          certificate_.valid = false;
          break;
        }
        support_scratch_.push_back(SupportTerm{
            blocking_atom, blocking_positive, std::fabs(candidate.coefficient),
            candidate.variable, blocking_upper,
            blocking_upper ? upper_[candidate.variable]
                           : lower_[candidate.variable]});
      }
      if (certificate_.valid)
        emitCertificate();
      factorized_last_violated_ = violated;
      last_conflict_row_ = kNoRow;
      return Verdict::InfeasibleCandidate;
    }
    /* Pivot: FTRAN the entering column, step the entering variable so
     * the violated one lands exactly on its bound, update the basis and
     * refactor. */
    if (!factorizedDirection(entering))
      return Verdict::Abandoned;
    double violated_component = direction_[violated];
    if (!(std::fabs(violated_component) > kTinyPivot))
    {
      /* The column disagrees with the row: the coefficient the row
       * showed was noise, or the factor has drifted.  A fresh factor
       * settles the second; the best-scaled eligible candidate replaces
       * the first.  Only when both leave the pivot tiny is the check
       * abandoned. */
      bool recovered = false;
      if (factorizedRefactor() && factorizedDirection(entering))
      {
        violated_component = direction_[violated];
        recovered = std::fabs(violated_component) > kTinyPivot;
      }
      if (!recovered)
      {
        Var const alternative = selectEntering(true, entering);
        if (alternative != kNoVar && factorizedDirection(alternative))
        {
          violated_component = direction_[violated];
          if (std::fabs(violated_component) > kTinyPivot)
          {
            entering = alternative;
            recovered = true;
          }
        }
      }
      if (!recovered)
        return Verdict::Abandoned;
    }
    DVal const target = needs_increase ? lower_[violated]
                                       : upper_[violated];
    double const step_value =
        (alpha_[violated].value - target.value) / violated_component;
    double const step_delta =
        (alpha_[violated].delta - target.delta) / violated_component;
    if (!std::isfinite(step_value) || !std::isfinite(step_delta))
      return Verdict::Abandoned;
    for (Var touched : direction_touched_)
    {
      /* Zero on apply, as in factorizedUpdateNonbasic: duplicates in the
       * touched list must not double-apply. */
      double const component = direction_[touched];
      direction_[touched] = 0.0;
      alpha_[touched].value -= component * step_value;
      alpha_[touched].delta -= component * step_delta;
      if (!std::isfinite(alpha_[touched].value) ||
          !std::isfinite(alpha_[touched].delta))
      {
        poisoned_ = true;
        return Verdict::Abandoned;
      }
      noteInfinitesimal(alpha_[touched]);
    }
    alpha_[entering].value += step_value;
    alpha_[entering].delta += step_delta;
    alpha_[violated] = target;
    noteInfinitesimal(alpha_[entering]);
    /* Re-judge every basic row variable the step moved; the one that
     * leaves sits on its bound and drops out of the set. */
    for (Var touched : direction_touched_)
    {
      std::uint32_t const touched_row = row_index_of_rowvar_[touched];
      if (touched_row != kNoRow && variable_basic_[touched] != 0)
        markViolation(touched_row, touched);
    }
    refresh_debt_ += direction_touched_.size();
    /* An assignment that has stopped adding up cannot be pivoted back
     * into shape: rebuild it and let the caller decide what to do with
     * the abandoned check. */
    if (assignment_unusable_)
    {
      if (!wants_promotion_ && !rebuildBudgetSpent())
        rebuildAssignment();
      return Verdict::Abandoned;
    }
    /* Basis update: the leaving variable's position takes the entering
     * column, from the spike the direction FTRAN left in the basis; a
     * refused update (a tiny pivot) or a full update file refactors from
     * the header. */
    std::int32_t const leaving_position = basis_position_[violated];
    if (leaving_position < 0)
    {
      poisoned_ = true;
      return Verdict::Abandoned;
    }
    bool const updated =
        basis_.update(static_cast<FloatBasis::Index>(leaving_position));
    variable_basic_[violated] = 0;
    variable_basic_[entering] = 1;

    basis_header_[static_cast<std::size_t>(leaving_position)] = entering;
    basis_position_[entering] = leaving_position;
    basis_position_[violated] = -1;
    row_violated_[violated_row] = 0;
    if (row_index_of_rowvar_[entering] != kNoRow)
      markViolation(row_index_of_rowvar_[entering], entering);
    ++pivots_;
    observer.accountPivot(false);
    if (!updated || basis_.refactorDue())
    {
      if (!factorizedRefactor())
        return Verdict::Abandoned;
    }
    if (++check_pivots > check_pivot_cap_)
      return Verdict::Abandoned;
  }
}

void FloatSimplex::collectPinnedBounds(std::vector<PinnedBound>& out) const
{
  out.clear();
  const auto close = [](const DVal& assignment, const DVal& bound) noexcept {
    return std::fabs(assignment.value - bound.value) <=
               1.0e-9 * std::fmax(1.0, std::fabs(bound.value)) &&
           std::fabs(assignment.delta - bound.delta) <=
               1.0e-9 * std::fmax(1.0, std::fabs(bound.delta));
  };
  const auto count = static_cast<Var>(alpha_.size());
  for (Var variable = 0; variable < count; ++variable)
  {
    if (has_lower_[variable] != 0 && lower_atom_[variable] != kNoAtom &&
        close(alpha_[variable], lower_[variable]))
      out.push_back(PinnedBound{lower_atom_[variable],
                                lower_positive_[variable] != 0});
    if (has_upper_[variable] != 0 && upper_atom_[variable] != kNoAtom &&
        close(alpha_[variable], upper_[variable]))
      out.push_back(PinnedBound{upper_atom_[variable],
                                upper_positive_[variable] != 0});
  }
}

void FloatSimplex::dismissLastConflict() noexcept
{
  if (factorized_)
  {
    if (factorized_last_violated_ != kNoVar)
    {
      factorized_dismissed_ = factorized_last_violated_;
      dismissed_alpha_ = alpha_[factorized_dismissed_];
      dismissed_lower_ = lower_[factorized_dismissed_];
      dismissed_upper_ = upper_[factorized_dismissed_];
    }
    factorized_last_violated_ = kNoVar;
    return;
  }
  if (last_conflict_row_ != kNoRow &&
      last_conflict_row_ < row_violated_.size())
    row_violated_[last_conflict_row_] = 0;
  last_conflict_row_ = kNoRow;
}

void FloatSimplex::markViolation(std::uint32_t row_index, Var basic) noexcept
{
  queueConflictRow(row_index);
  DVal const& assignment = alpha_[basic];
  bool const violated =
      (has_lower_[basic] != 0 && belowBound(assignment, lower_[basic], scaleOf(basic))) ||
      (has_upper_[basic] != 0 && aboveBound(assignment, upper_[basic], scaleOf(basic)));
  if (!violated)
  {
    row_violated_[row_index] = 0;  // lazy removal; the picks compact
    return;
  }
  row_violated_[row_index] = 1;
  if (row_queued_[row_index] == 0)
  {
    row_queued_[row_index] = 1;
    violated_rows_.push_back(row_index);
  }
}

bool FloatSimplex::recomputeRow(std::uint32_t row_index, bool pristine) noexcept
{
  Row const& row = pristine ? pristine_rows_[row_index] : rows_[row_index];
  DVal fresh{0.0, 0.0};
  for (const Term& cell : row.cells)
  {
    fresh.value += cell.coefficient * alpha_[cell.variable].value;
    fresh.delta += cell.coefficient * alpha_[cell.variable].delta;
  }
  if (!std::isfinite(fresh.value) || !std::isfinite(fresh.delta))
  {
    poisoned_ = true;
    return false;
  }
  alpha_[row.basic] = fresh;
  noteInfinitesimal(fresh);
  markViolation(row_index, row.basic);
  return true;
}

bool FloatSimplex::refreshDue() const noexcept
{
  return refresh_debt_ >
         32U * static_cast<std::uint64_t>(rows_.size()) + 65536U;
}

void FloatSimplex::refreshAllRows() noexcept
{
  refresh_debt_ = 0;
  if (factorized_)
  {
    for (std::uint32_t row_index = 0;
         row_index < static_cast<std::uint32_t>(pristine_rows_.size());
         ++row_index)
    {
      if (variable_basic_[pristine_rows_[row_index].basic] == 0)
      {
        row_violated_[row_index] = 0;
        continue;
      }
      if (!recomputeRow(row_index, true))
        return;
    }
    return;
  }
  for (std::uint32_t row_index = 0;
       row_index < static_cast<std::uint32_t>(rows_.size()); ++row_index)
  {
    if (row_dormant_[row_index] != 0)
      continue;
    if (!recomputeRow(row_index, false))
      return;
  }
}

void FloatSimplex::noteFinite(double candidate) noexcept
{
  if (!std::isfinite(candidate))
    finite_inputs_ = false;
}

namespace
{
/* Row cells stay sorted by variable; lookups and merges rely on it. */
bool cellBeforeVariable(FloatSimplex::Term const& cell,
                        FloatSimplex::Var variable) noexcept
{
  return cell.variable < variable;
}
}  // namespace

double FloatSimplex::coefficientOf(const Row& row, Var variable) const noexcept
{
  const auto found = std::lower_bound(row.cells.begin(), row.cells.end(),
                                      variable, cellBeforeVariable);
  if (found != row.cells.end() && found->variable == variable)
    return found->coefficient;
  return 0.0;
}

void FloatSimplex::eraseColumnEntry(Var variable, std::uint32_t position,
                                    std::uint32_t row_index) noexcept
{
  std::vector<std::uint32_t>& bucket = cols_[variable];
  if (position >= bucket.size() || bucket[position] != row_index)
    return;  // the cross-link disagrees; leave the column alone
  bucket[position] = bucket.back();
  bucket.pop_back();
  if (position >= bucket.size())
    return;  // the entry was the last one; nothing moved
  /* The entry that took the vacated slot has to be told where it now
   * lives, and its cell is one binary search away in its own row. */
  std::vector<Term>& moved = rows_[bucket[position]].cells;
  auto const found = std::lower_bound(moved.begin(), moved.end(), variable,
                                      cellBeforeVariable);
  if (found != moved.end() && found->variable == variable)
    found->col_position = position;
}

void FloatSimplex::addCell(std::uint32_t row_index, Var variable,
                           double coefficient)
{
  std::vector<Term>& cells = rows_[row_index].cells;
  const auto position =
      std::lower_bound(cells.begin(), cells.end(), variable,
                       cellBeforeVariable);
  auto const slot = static_cast<std::uint32_t>(cols_[variable].size());
  cells.insert(position, Term{variable, slot, coefficient});
  cols_[variable].push_back(row_index);
}

void FloatSimplex::removeCell(std::uint32_t row_index, Var variable) noexcept
{
  std::vector<Term>& cells = rows_[row_index].cells;
  const auto found = std::lower_bound(cells.begin(), cells.end(), variable,
                                      cellBeforeVariable);
  if (found == cells.end() || found->variable != variable)
    return;
  std::uint32_t const position = found->col_position;
  cells.erase(found);
  eraseColumnEntry(variable, position, row_index);
}

void FloatSimplex::addScaledExpression(std::uint32_t row_index, double scale,
                                       const std::vector<Term>& expression)
{
  queueConflictRow(row_index, true);
  Row& row = rows_[row_index];
  check_merge_cells_ += row.cells.size() + expression.size();
  merge_scratch_.clear();
  merge_scratch_.reserve(row.cells.size() + expression.size());
  std::size_t old_index = 0;
  std::size_t new_index = 0;
  while (old_index < row.cells.size() || new_index < expression.size())
  {
    if (new_index == expression.size() ||
        (old_index < row.cells.size() &&
         row.cells[old_index].variable < expression[new_index].variable))
    {
      merge_scratch_.push_back(row.cells[old_index]);
      ++old_index;
      continue;
    }
    Var const variable = expression[new_index].variable;
    double contribution = scale * expression[new_index].coefficient;
    ++new_index;
    /* A cell the row already had keeps its slot in the column: the
     * diff below leaves that membership alone, so losing the
     * cross-link here would strand the entry. */
    std::uint32_t position = 0;
    if (old_index < row.cells.size() &&
        row.cells[old_index].variable == variable)
    {
      contribution += row.cells[old_index].coefficient;
      position = row.cells[old_index].col_position;
      ++old_index;
    }
    if (!std::isfinite(contribution))
    {
      poisoned_ = true;
      return;  // row left as it was; the poisoned flag abandons checks
    }
    if (std::fabs(contribution) < kDropTolerance)
      continue;
    merge_scratch_.push_back(Term{variable, position, contribution});
  }
  /* Column index diff: both lists are sorted, so one joint walk finds the
   * memberships that changed. */
  std::size_t oi = 0;
  std::size_t ni = 0;
  while (oi < row.cells.size() || ni < merge_scratch_.size())
  {
    Var const old_var =
        oi < row.cells.size() ? row.cells[oi].variable : kNoVar;
    Var const new_var =
        ni < merge_scratch_.size() ? merge_scratch_[ni].variable : kNoVar;
    if (old_var == new_var)
    {
      ++oi;
      ++ni;
      continue;
    }
    if (new_var == kNoVar || (old_var != kNoVar && old_var < new_var))
    {
      eraseColumnEntry(old_var, row.cells[oi].col_position, row_index);
      ++oi;
    }
    else
    {
      merge_scratch_[ni].col_position =
          static_cast<std::uint32_t>(cols_[new_var].size());
      cols_[new_var].push_back(row_index);
      ++ni;
    }
  }
  row.cells.swap(merge_scratch_);
}

void FloatSimplex::updateNonbasic(Var variable, DVal target) noexcept
{
  double const value_delta = target.value - alpha_[variable].value;
  double const delta_delta = target.delta - alpha_[variable].delta;
  for (std::uint32_t const row_index : cols_[variable])
  {
    Row const& row = rows_[row_index];
    double const coefficient = coefficientOf(row, variable);
    DVal& basic = alpha_[row.basic];
    basic.value += coefficient * value_delta;
    basic.delta += coefficient * delta_delta;
    if (!std::isfinite(basic.value) || !std::isfinite(basic.delta))
      poisoned_ = true;
    noteInfinitesimal(basic);
    markViolation(row_index, row.basic);
  }
  refresh_debt_ += cols_[variable].size();
  alpha_[variable] = target;
  refreshMovement(variable);
  noteInfinitesimal(alpha_[variable]);
}

void FloatSimplex::pivot(std::uint32_t row_index, Var entering)
{
  queueConflictRow(row_index, true);
  Row& row = rows_[row_index];
  Var const leaving = row.basic;
  double const pivot_coefficient = coefficientOf(row, entering);
  double const inverse = 1.0 / pivot_coefficient;
  if (!std::isfinite(inverse))
  {
    poisoned_ = true;
    return;
  }
  /* The row states leaving = sum a_j x_j; solved for the entering variable
   * it becomes entering = inverse * leaving - sum_{j != entering}
   * (a_j * inverse) x_j, assembled sorted so substitution can merge. */
  std::vector<Term> expression;
  expression.reserve(row.cells.size());
  for (const Term& cell : row.cells)
  {
    if (cell.variable == entering)
      continue;
    double const coefficient = -cell.coefficient * inverse;
    if (!std::isfinite(coefficient))
      poisoned_ = true;
    expression.push_back(Term{cell.variable, coefficient});
  }
  const auto position = std::lower_bound(expression.begin(),
                                         expression.end(), leaving,
                                         cellBeforeVariable);
  expression.insert(position, Term{leaving, inverse});
  if (poisoned_)
    return;
  /* Dismantle the old row wholesale. */
  for (const Term& cell : row.cells)
    eraseColumnEntry(cell.variable, cell.col_position, row_index);
  row.cells.clear();
  /* Substitute the entering variable out of every other row.  The loop
   * mutates cols_, so it walks a copy. */
  std::vector<std::uint32_t> const holders = cols_[entering];
  for (std::uint32_t const other_index : holders)
  {
    double const held = coefficientOf(rows_[other_index], entering);
    removeCell(other_index, entering);
    addScaledExpression(other_index, held, expression);
    if (poisoned_)
      return;
    /* The substitution rewrites the row's expression, not its basic
     * variable's value: the violated set is untouched. */
  }
  row.basic = entering;
  row_of_basic_[leaving] = kNoRow;
  row_of_basic_[entering] = row_index;
  row.cells = expression;
  for (Term& term : row.cells)
  {
    term.col_position = static_cast<std::uint32_t>(cols_[term.variable].size());
    cols_[term.variable].push_back(row_index);
  }
  ++pivots_;
}

void FloatSimplex::pivotAndUpdate(std::uint32_t row_index, Var entering,
                                  DVal target)
{
  Row const& row = rows_[row_index];
  Var const leaving = row.basic;
  double const pivot_coefficient = coefficientOf(row, entering);
  double const theta_value =
      (target.value - alpha_[leaving].value) / pivot_coefficient;
  double const theta_delta =
      (target.delta - alpha_[leaving].delta) / pivot_coefficient;
  if (!std::isfinite(theta_value) || !std::isfinite(theta_delta))
  {
    poisoned_ = true;
    return;
  }
  alpha_[leaving] = target;
  if (movement_initialized_)
    movement_[leaving] = movementMask(leaving);
  alpha_[entering].value += theta_value;
  alpha_[entering].delta += theta_delta;
  if (!std::isfinite(alpha_[entering].value) ||
      !std::isfinite(alpha_[entering].delta))
    poisoned_ = true;
  noteInfinitesimal(alpha_[entering]);
  for (std::uint32_t const other_index : cols_[entering])
  {
    if (other_index == row_index)
      continue;
    Row const& other = rows_[other_index];
    double const coefficient = coefficientOf(other, entering);
    DVal& basic = alpha_[other.basic];
    basic.value += coefficient * theta_value;
    basic.delta += coefficient * theta_delta;
    if (!std::isfinite(basic.value) || !std::isfinite(basic.delta))
      poisoned_ = true;
    noteInfinitesimal(basic);
    markViolation(other_index, other.basic);
  }
  refresh_debt_ += cols_[entering].size();
  if (poisoned_)
    return;
  pivot(row_index, entering);
  /* The pivot row now belongs to the entering variable, which just moved
   * by theta; the leaving one sits on its bound as a nonbasic. */
  if (!poisoned_)
    markViolation(row_index, entering);
}

FloatSimplex::AssertOutcome FloatSimplex::assertAtom(Atom atom, bool positive,
                                                     std::uint32_t user_tag)
{
  AtomInfo const& info = atoms_[atom];
  /* The negation of a relation is the opposite side with flipped
   * strictness: not (t < c) is t >= c, not (t <= c) is t > c. */
  std::uint8_t side = kSideNone;
  double delta = 0.0;
  switch (info.relation)
  {
    case Relation::Less:
      side = positive ? kSideUpper : kSideLower;
      delta = positive ? -1.0 : 0.0;
      break;
    case Relation::LessEqual:
      side = positive ? kSideUpper : kSideLower;
      delta = positive ? 0.0 : 1.0;
      break;
    case Relation::Greater:
      side = positive ? kSideLower : kSideUpper;
      delta = positive ? 1.0 : 0.0;
      break;
    case Relation::GreaterEqual:
      side = positive ? kSideLower : kSideUpper;
      delta = positive ? 0.0 : -1.0;
      break;
  }
  DVal const bound{info.threshold, delta};
  Var const variable = info.variable;
  /* Every assert joins its side's asserted list, tightening or not:
   * the generalisation wants the weaker ones. */
  (side == kSideUpper ? upper_asserted_ : lower_asserted_)[variable]
      .push_back(AssertedBound{atom, positive, bound});
  if (dormant_rows_ && !factorized_)
  {
    std::uint32_t const held = row_of_basic_[variable];
    if (held != kNoRow && row_dormant_[held] != 0)
      activateRow(held);
  }
  bool tightened = false;
  bool clash = false;
  if (side == kSideUpper)
  {
    tightened =
        !has_upper_[variable] || boundStrictlyLess(bound, upper_[variable]);
    clash = tightened && has_lower_[variable] != 0 &&
            boundStrictlyLess(bound, lower_[variable]);
  }
  else
  {
    tightened =
        !has_lower_[variable] || boundStrictlyLess(lower_[variable], bound);
    clash = tightened && has_upper_[variable] != 0 &&
            boundStrictlyLess(upper_[variable], bound);
  }
  TrailEntry entry{atom,  positive, kSideNone, variable, DVal{0.0, 0.0},
                   false, user_tag, kNoAtom,   false};
  if (tightened && !clash)
  {
    entry.restored_side = side;
    if (side == kSideUpper)
    {
      entry.previous_bound = upper_[variable];
      entry.previously_bounded = has_upper_[variable] != 0;
      entry.previous_atom = upper_atom_[variable];
      entry.previous_atom_positive = upper_positive_[variable] != 0;
      upper_[variable] = bound;
      has_upper_[variable] = 1;
      upper_atom_[variable] = atom;
      upper_positive_[variable] = positive ? 1 : 0;
      bool const nonbasic = factorized_
                                ? variable_basic_[variable] == 0
                                : row_of_basic_[variable] == kNoRow;
      if (nonbasic)
      {
        if (!poisoned_ && boundStrictlyLess(bound, alpha_[variable]))
        {
          if (factorized_)
            factorizedUpdateNonbasic(variable, bound);
          else
            updateNonbasic(variable, bound);
        }
      }
      else if (!factorized_)
      {
        markViolation(row_of_basic_[variable], variable);
      }
      else if (row_index_of_rowvar_[variable] != kNoRow)
      {
        markViolation(row_index_of_rowvar_[variable], variable);
      }
    }
    else
    {
      entry.previous_bound = lower_[variable];
      entry.previously_bounded = has_lower_[variable] != 0;
      entry.previous_atom = lower_atom_[variable];
      entry.previous_atom_positive = lower_positive_[variable] != 0;
      lower_[variable] = bound;
      has_lower_[variable] = 1;
      lower_atom_[variable] = atom;
      lower_positive_[variable] = positive ? 1 : 0;
      bool const nonbasic = factorized_
                                ? variable_basic_[variable] == 0
                                : row_of_basic_[variable] == kNoRow;
      if (nonbasic)
      {
        if (!poisoned_ && boundStrictlyLess(alpha_[variable], bound))
        {
          if (factorized_)
            factorizedUpdateNonbasic(variable, bound);
          else
            updateNonbasic(variable, bound);
        }
      }
      else if (!factorized_)
      {
        markViolation(row_of_basic_[variable], variable);
      }
      else if (row_index_of_rowvar_[variable] != kNoRow)
      {
        markViolation(row_index_of_rowvar_[variable], variable);
      }
    }
  }
  if (clash)
  {
    /* Two bounds on one variable contradict: the certificate is the pair
     * itself, weight one each.  Not a row conflict, so there is nothing
     * for a later dismissal to mute. */
    last_conflict_row_ = kNoRow;
    factorized_last_violated_ = kNoVar;
    certificate_.valid = false;
    certificate_.items.clear();
    Atom const opposite_atom =
        side == kSideUpper ? lower_atom_[variable] : upper_atom_[variable];
    bool const opposite_positive =
        (side == kSideUpper ? lower_positive_[variable]
                            : upper_positive_[variable]) != 0;
    if (opposite_atom != kNoAtom)
    {
      certificate_.items.push_back(CertificateItem{atom, positive, 1.0});
      certificate_.items.push_back(
          CertificateItem{opposite_atom, opposite_positive, 1.0});
      certificate_.valid = true;
    }
  }
  trail_.push_back(entry);
  if (!factorized_ && row_of_basic_[variable] == kNoRow)
    refreshMovement(variable);
  return clash ? AssertOutcome::LocalConflict : AssertOutcome::Ok;
}

void FloatSimplex::undoTo(std::size_t mark) noexcept
{
  while (trail_.size() > mark)
  {
    TrailEntry const& entry = trail_.back();
    {
      /* The assert's side, tightening or not, from the atom itself. */
      Relation const relation = atoms_[entry.atom].relation;
      bool const less =
          relation == Relation::Less || relation == Relation::LessEqual;
      bool const upper = less == entry.positive;
      std::vector<AssertedBound>& asserted =
          (upper ? upper_asserted_ : lower_asserted_)[entry.variable];
      if (!asserted.empty())
        asserted.pop_back();
    }
    if (entry.restored_side == kSideUpper)
    {
      upper_[entry.variable] = entry.previous_bound;
      has_upper_[entry.variable] = entry.previously_bounded ? 1 : 0;
      upper_atom_[entry.variable] = entry.previous_atom;
      upper_positive_[entry.variable] = entry.previous_atom_positive ? 1 : 0;
    }
    else if (entry.restored_side == kSideLower)
    {
      lower_[entry.variable] = entry.previous_bound;
      has_lower_[entry.variable] = entry.previously_bounded ? 1 : 0;
      lower_atom_[entry.variable] = entry.previous_atom;
      lower_positive_[entry.variable] = entry.previous_atom_positive ? 1 : 0;
    }
    /* The assignment stays: undo only loosens bounds, and a point inside
     * the tight box is inside the loose one.  A live row stays live when
     * its variable loses its last bound: the search re-asserts the same
     * atoms after every backtrack, and re-normalising the row each time
     * cost more than keeping it in the index. */
    if (!factorized_)
    {
      if (row_of_basic_[entry.variable] == kNoRow)
        refreshMovement(entry.variable);
      else
        markViolation(row_of_basic_[entry.variable], entry.variable);
    }
    trail_.pop_back();
  }
}

unsigned char FloatSimplex::movementMask(Var v) const noexcept
{
  // The same strict lexicographic comparisons as entering eligibility;
  // a tolerance here would invent blocked directions.
  return (has_upper_[v] == 0 || boundStrictlyLess(alpha_[v], upper_[v]) ? 1 : 0) |
         (has_lower_[v] == 0 || boundStrictlyLess(lower_[v], alpha_[v]) ? 2 : 0);
}

void FloatSimplex::queueConflictRow(std::uint32_t i, bool dirty) noexcept
{
  if (!early_conflicts_ || !movement_initialized_ || factorized_)
    return;
  Row& row = rows_[i];
  row.movement_dirty |= dirty;
  if (!row.conflict_queued)
  {
    conflict_rows_.push_back(i); // capacity reserved before tracking starts
    row.conflict_queued = true;
  }
}

void FloatSimplex::refreshMovement(Var v) noexcept
{
  if (!early_conflicts_ || !movement_initialized_ || factorized_)
    return;
  unsigned char const old = movement_[v], now = movementMask(v);
  if (old == now)
    return;
  movement_[v] = now;
  for (std::uint32_t i : cols_[v])
  {
    Row& row = rows_[i];
    if (!row.movement_dirty)
    {
      double const coefficient = coefficientOf(row, v);
      if (coefficient == 0.0)
        continue;
      bool const positive = coefficient > 0.0;
      unsigned const up = positive ? 1 : 2, down = positive ? 2 : 1;
      row.can_raise -= (old & up) != 0;
      row.can_raise += (now & up) != 0;
      row.can_lower -= (old & down) != 0;
      row.can_lower += (now & down) != 0;
    }
    queueConflictRow(i);
  }
}

std::uint32_t FloatSimplex::earlyConflict()
{
  if (!early_conflicts_)
    return kNoRow;
  if (!movement_initialized_)
  {
    conflict_rows_.clear();
    conflict_rows_.reserve(rows_.size());
    movement_.resize(alpha_.size());
    for (Var v = 0; v < alpha_.size(); ++v)
      movement_[v] = movementMask(v);
    movement_initialized_ = true;
    for (std::uint32_t i = 0; i < rows_.size(); ++i)
    {
      rows_[i].conflict_queued = false;
      if (row_dormant_[i] != 0)
        continue;
      queueConflictRow(i, true);
    }
  }
  while (!conflict_rows_.empty())
  {
    std::uint32_t const i = conflict_rows_.back();
    Row& row = rows_[i];
    if (row.movement_dirty)
    {
      row.can_raise = row.can_lower = 0;
      for (Term const& cell : row.cells)
      {
        if (cell.coefficient == 0.0)
          continue;
        bool const positive = cell.coefficient > 0.0;
        row.can_raise += (movement_[cell.variable] & (positive ? 1 : 2)) != 0;
        row.can_lower += (movement_[cell.variable] & (positive ? 2 : 1)) != 0;
      }
      row.movement_dirty = false;
    }
    Var const v = row.basic;
    if (row_violated_[i] != 0 &&
        ((row.can_raise == 0 && has_lower_[v] != 0 &&
          belowBound(alpha_[v], lower_[v], scaleOf(v))) ||
         (row.can_lower == 0 && has_upper_[v] != 0 &&
          aboveBound(alpha_[v], upper_[v], scaleOf(v)))))
      return i;
    row.conflict_queued = false;
    conflict_rows_.pop_back();
  }
  return kNoRow;
}

bool FloatSimplex::soiStep(bool& pivoted)
{
  using Search = SoiLineSearch<DVal, double>;
  std::vector<char> seen(alpha_.size(), 0);
  std::vector<Var> candidates;
  for (std::uint32_t i : violated_rows_)
    if (row_violated_[i])
      for (Term const& cell : rows_[i].cells)
        if (!seen[cell.variable])
        {
          seen[cell.variable] = 1;
          candidates.push_back(cell.variable);
        }
  std::sort(candidates.begin(), candidates.end());
  if (candidates.size() > 256)
    candidates.resize(256);
  Var entering = kNoVar;
  std::optional<Search::Move> best;
  for (Var v : candidates)
  {
    if ((has_lower_[v] && alpha_[v] < lower_[v]) ||
        (has_upper_[v] && upper_[v] < alpha_[v]))
      return false;
    for (bool increase : {true, false})
    {
      if ((movementMask(v) & (increase ? 1 : 2)) == 0)
        continue;
      Search search;
      double const direction = increase ? 1.0 : -1.0;
      if (increase ? has_upper_[v] : has_lower_[v])
      {
        auto const& bound = increase ? upper_[v] : lower_[v];
        search.limit((bound - alpha_[v]) / direction, bound);
      }
      for (std::uint32_t i : cols_[v])
      {
        Row const& row = rows_[i];
        Var const basic = row.basic;
        double const a = coefficientOf(row, v) * direction;
        if (has_lower_[basic])
          search.addBound(alpha_[basic], lower_[basic], a, true, i, row.cells.size());
        if (has_upper_[basic])
          search.addBound(alpha_[basic], upper_[basic], a, false, i, row.cells.size());
      }
      auto move = search.best();
      if (move && (!best || best->gain < move->gain ||
                   (best->gain == move->gain &&
                    cols_[v].size() < cols_[entering].size())))
      {
        entering = v;
        best = std::move(move);
      }
    }
  }
  if (!best)
    return false;
  pivoted = best->row != Search::no_row;
  if (pivoted)
    pivotAndUpdate(best->row, entering, best->target);
  else
  {
    updateNonbasic(entering, best->target);
    ++soi_bound_flips_;
  }
  ++soi_steps_;
  return true;
}

FloatSimplex::Verdict FloatSimplex::check(ExactLraResourceObserver& observer,
                                          bool full_refresh)
{
  if (assignment_unusable_)
  {
    if (wants_promotion_ || rebuildBudgetSpent())
      return Verdict::Abandoned;
    rebuildAssignment();
  }
  if (!buildUsable() || poisoned_)
    return Verdict::Abandoned;
  if (full_refresh || refreshDue())
    refreshAllRows();
  if (factorized_)
    return factorizedCheck(observer);
  if (poisoned_)
    return Verdict::Abandoned;
  std::uint64_t check_pivots = 0;
  std::size_t soi_steps = 0;
  bool soi = soi_;
  check_merge_cells_ = 0;
  for (;;)
  {
    /* The touched frontier is only ever populated by a basis restart; in
     * steady state the violated set is maintained where assignments
     * change and nothing here rescans the tableau. */
    while (!touched_rows_.empty())
    {
      std::uint32_t const candidate = touched_rows_.back();
      touched_rows_.pop_back();
      row_touched_[candidate] = 0;
      if (row_dormant_[candidate] != 0)
        continue;
      if (!recomputeRow(candidate, false))
        return Verdict::Abandoned;
    }
    /* Pick the shortest live violated row -- the pairing the exact tier
     * uses (minimum row to fix, fewest-holder column to enter) is what
     * bounds fill-in: the pivot installs this row's expression into every
     * holder, so its length is the growth factor.  Ties break to the
     * smaller basic variable; the per-check pivot cap covers cycling.
     * Stale entries are compacted on the way, and the pick is recomputed
     * fresh from its cells before anything is built on it, so accumulated
     * update drift cannot manufacture a violation the exact tier then has
     * to refute. */
    std::uint32_t violated_row = kNoRow;
    Var violated_variable = kNoVar;
    std::size_t violated_cells = 0;
    bool needs_increase = false;
    bool early = false;
    for (;;)
    {
      violated_row = earlyConflict();
      early = violated_row != kNoRow;
      if (early)
      {
        violated_variable = rows_[violated_row].basic;
        if (!recomputeRow(violated_row, false))
          return Verdict::Abandoned;
        if (row_violated_[violated_row] != 0)
          break;
        continue;
      }
      violated_row = kNoRow;
      violated_variable = kNoVar;
      std::size_t keep = 0;
      for (std::size_t i = 0; i < violated_rows_.size(); ++i)
      {
        std::uint32_t const candidate = violated_rows_[i];
        if (row_violated_[candidate] == 0)
        {
          row_queued_[candidate] = 0;
          continue;
        }
        Var const basic = rows_[candidate].basic;
        /* Re-validate against the current bounds: an undo loosens bounds
         * without touching rows, and the cached assignment is still valid
         * (undo never moves it), so this is a pair of comparisons, not a
         * recompute. */
        DVal const& assignment = alpha_[basic];
        if (!(has_lower_[basic] != 0 &&
              belowBound(assignment, lower_[basic], scaleOf(basic))) &&
            !(has_upper_[basic] != 0 &&
              aboveBound(assignment, upper_[basic], scaleOf(basic))))
        {
          row_violated_[candidate] = 0;
          row_queued_[candidate] = 0;
          continue;
        }
        violated_rows_[keep++] = candidate;
        std::size_t const cells = rows_[candidate].cells.size();
        if (violated_variable == kNoVar || cells < violated_cells ||
            (cells == violated_cells && basic < violated_variable))
        {
          violated_row = candidate;
          violated_variable = basic;
          violated_cells = cells;
        }
      }
      violated_rows_.resize(keep);
      if (violated_variable == kNoVar)
        return Verdict::Feasible;
      if (!recomputeRow(violated_row, false))
        return Verdict::Abandoned;
      if (row_violated_[violated_row] != 0)
        break;
      /* The flag was drift; it is cleared now, pick again. */
    }
    {
      DVal const& assignment = alpha_[violated_variable];
      needs_increase = has_lower_[violated_variable] != 0 &&
                       belowBound(assignment, lower_[violated_variable], scaleOf(violated_variable));
    }
    if (observer.pollBeforePivot() != StopReason::Continue)
      return Verdict::Abandoned;
    if (soi && !early)
    {
      bool pivoted = false;
      if (soi_steps < rows_.size() + 16U && soiStep(pivoted))
      {
        ++soi_steps;
        if (pivoted)
          observer.accountPivot(false);
        if (poisoned_ || ++check_pivots > check_pivot_cap_ ||
            check_merge_cells_ > check_merge_cap_)
          return Verdict::Abandoned;
        continue;
      }
      soi = false;
      ++soi_fallbacks_;
    }
    Row const& row = rows_[violated_row];
    Var entering = kNoVar;
    std::size_t entering_holders = 0;
    for (const Term& cell : row.cells)
    {
      if (cell.coefficient == 0.0)
        continue;
      /* Raising x_j moves the basic variable by a_j; the entering variable
       * must have headroom in the direction that repairs the violation.
       * Headroom is judged exactly over the stored doubles: a tolerance
       * here reads "within noise of its bound" as "stuck" and, on families
       * whose magnitudes sit near the absolute epsilon, manufactures
       * phantom infeasibility.  Tolerance belongs only in the violation
       * test -- what the check tries to repair -- never in what it is
       * allowed to move. */
      bool const wants_higher = needs_increase == (cell.coefficient > 0.0);
      bool eligible = false;
      if (wants_higher)
        eligible = has_upper_[cell.variable] == 0 ||
                   boundStrictlyLess(alpha_[cell.variable],
                                     upper_[cell.variable]);
      else
        eligible = has_lower_[cell.variable] == 0 ||
                   boundStrictlyLess(lower_[cell.variable],
                                     alpha_[cell.variable]);
      if (!eligible)
        continue;
      /* Fewest holder rows first -- substitution rewrites one row per
       * holder, so this is what keeps fill-in down; a hub variable picked
       * by plain minimum index densifies the tableau in a few pivots.
       * Ties break to the smaller index; the per-check pivot cap covers
       * the cycling risk the pure heuristic reintroduces. */
      std::size_t const holders = cols_[cell.variable].size();
      if (entering == kNoVar || holders < entering_holders ||
          (holders == entering_holders && cell.variable < entering))
      {
        entering = cell.variable;
        entering_holders = holders;
      }
    }
    if (entering == kNoVar)
    {
      /* Extract the Farkas certificate: the violated bound at weight one,
       * and each cell's blocking bound at the magnitude of its tableau
       * coefficient.  Needing to increase the basic variable means the
       * violated bound is its lower one and positive cells block at their
       * uppers; needing to decrease mirrors both. */
      certificate_.valid = true;
      certificate_.items.clear();
      support_scratch_.clear();
      Row const& conflict_row = rows_[violated_row];
      support_scratch_.reserve(conflict_row.cells.size() + 1U);
      {
        Atom const violated_atom = needs_increase
                                       ? lower_atom_[violated_variable]
                                       : upper_atom_[violated_variable];
        bool const violated_positive =
            (needs_increase ? lower_positive_[violated_variable]
                            : upper_positive_[violated_variable]) != 0;
        if (violated_atom == kNoAtom)
          certificate_.valid = false;
        else
          support_scratch_.push_back(SupportTerm{
              violated_atom, violated_positive, 1.0, violated_variable,
              !needs_increase,
              needs_increase ? lower_[violated_variable]
                             : upper_[violated_variable]});
      }
      for (const Term& cell : conflict_row.cells)
      {
        if (cell.coefficient == 0.0)
          continue;
        bool const blocking_upper = needs_increase == (cell.coefficient > 0.0);
        Atom const blocking_atom = blocking_upper
                                       ? upper_atom_[cell.variable]
                                       : lower_atom_[cell.variable];
        bool const blocking_positive =
            (blocking_upper ? upper_positive_[cell.variable]
                            : lower_positive_[cell.variable]) != 0;
        if (blocking_atom == kNoAtom)
        {
          certificate_.valid = false;
          break;
        }
        support_scratch_.push_back(SupportTerm{
            blocking_atom, blocking_positive, std::fabs(cell.coefficient),
            cell.variable, blocking_upper,
            blocking_upper ? upper_[cell.variable] : lower_[cell.variable]});
      }
      if (certificate_.valid)
        emitCertificate();
      /* The row stays in the violated set untouched: re-picked cheaply
       * while the exact tier confirms, dormant once the caller dismisses
       * a refuted candidate. */
      last_conflict_row_ = violated_row;
      early_conflicts_count_ += early ? 1U : 0U;
      return Verdict::InfeasibleCandidate;
    }
    DVal const target = needs_increase ? lower_[violated_variable]
                                       : upper_[violated_variable];
    pivotAndUpdate(violated_row, entering, target);
    observer.accountPivot(false);
    if (poisoned_)
      return Verdict::Abandoned;
    if (++check_pivots > check_pivot_cap_ ||
        check_merge_cells_ > check_merge_cap_)
      return Verdict::Abandoned;
  }
}

}  // namespace stp::lra

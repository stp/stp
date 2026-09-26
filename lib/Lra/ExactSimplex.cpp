#include "ExactSimplex.h"

#include "Storage/StorageFailure.h"
#include "SoiSearch.h"

#include <algorithm>
#include <limits>
#include <utility>

namespace stp::lra
{

namespace
{

bool cellBefore(ExactSimplex::Cell const& cell, std::uint32_t variable) noexcept
{
  return cell.variable < variable;
}

}  // namespace

ExactSimplex::ExactSimplex(CoreGeneration generation, BoundStore& bound_store)
    : generation_(generation), bound_store_(bound_store)
{}

ExactSimplex::Ordinal ExactSimplex::ordinalOf(VariableId variable,
                                              char const* operation) const
{
  if (variable.generation() != generation_ ||
      variable.ordinal() >= status_.size())
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal, operation,
                         "unknown variable");
  }
  return variable.ordinal();
}

void ExactSimplex::registerVariable(VariableId variable, char const* operation)
{
  if (variable.generation() != generation_ ||
      variable.ordinal() != status_.size())
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal, operation,
                         "variables must be current and monotonic");
  }
  bound_store_.validateVariable(variable);
  status_.push_back(Status::Nonbasic);
  row_of_.push_back(kNone);
  cols_.emplace_back();
  value_.emplace_back();
  lower_stack_.emplace_back();
  upper_stack_.emplace_back();
  lower_ptr_.push_back(nullptr);
  upper_ptr_.push_back(nullptr);
  active_bound_count_.push_back(0);
  movement_.push_back(3);
}

void ExactSimplex::initialize()
{
  if (status_.size() != bound_store_.variableStore().size())
  {
    throw EngineInvariantFailure("simplex variable dimensions differ");
  }
}

void ExactSimplex::addVariable(VariableId variable)
{
  registerVariable(variable, "ExactSimplex::addVariable");
}

void ExactSimplex::addRow(VariableId variable, std::vector<RowTerm> terms)
{
  registerVariable(variable, "ExactSimplex::addRow");
  Ordinal const basic = variable.ordinal();
  Row row;
  row.basic = basic;
  row.cells.reserve(terms.size());
  for (RowTerm const& term : terms)
  {
    if (term.variable.generation() != generation_ ||
        term.variable.ordinal() >= basic)
    {
      throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                           "ExactSimplex::addRow", "row term out of range");
    }
    if (term.coefficient.isZero())
      continue;
    row.cells.push_back(Cell{term.variable.ordinal(), 0, term.coefficient});
  }
  std::sort(row.cells.begin(), row.cells.end(),
            [](Cell const& lhs, Cell const& rhs) {
              return lhs.variable < rhs.variable;
            });
  /* Merge repeated variables; a sum that cancels leaves no cell. */
  std::vector<Cell> merged;
  merged.reserve(row.cells.size());
  for (Cell& cell : row.cells)
  {
    if (!merged.empty() && merged.back().variable == cell.variable)
    {
      merged.back().coefficient += cell.coefficient;
      if (merged.back().coefficient.isZero())
        merged.pop_back();
      continue;
    }
    merged.push_back(std::move(cell));
  }
  row.cells.swap(merged);
  Ordinal const index = static_cast<Ordinal>(rows_.size());
  rows_.push_back(std::move(row));
  row_violated_.push_back(0);
  row_queued_.push_back(0);
  visiting_scratch_.push_back(0);
  row_of_[basic] = index;
  status_[basic] = Status::Dormant;  // no bound yet: out of the columns
}

/* ---- bounds -------------------------------------------------------- */

DeltaRational const& ExactSimplex::lowerValue(Ordinal v) const { return *lower_ptr_[v]; }

DeltaRational const& ExactSimplex::upperValue(Ordinal v) const { return *upper_ptr_[v]; }

bool ExactSimplex::outOfLower(Ordinal v) const
{
  return hasLower(v) && value_[v] < lowerValue(v);
}

bool ExactSimplex::outOfUpper(Ordinal v) const
{
  return hasUpper(v) && upperValue(v) < value_[v];
}

Checkpoint ExactSimplex::push()
{
  /* Tokens are nonzero and never reused within a generation, as the
   * registration's own trail expects. */
  if (next_checkpoint_token_ >= std::numeric_limits<std::uint32_t>::max())
  {
    throw StorageFailure(StorageFailureKind::ResourceLimit,
                         "ExactSimplex::push",
                         "checkpoint token exhausted");
  }
  Checkpoint const checkpoint{generation_, next_checkpoint_token_};
  levels_.push_back(Level{checkpoint, active_bounds_.size()});
  ++next_checkpoint_token_;
  return checkpoint;
}

void ExactSimplex::pop(Checkpoint checkpoint)
{
  // Tokens increase on every push and are never reused in a generation.
  // Popping erases a suffix, preserving this order even when a later push
  // returns to the same stack depth. The token is not a vector index.
  auto const found =
      std::lower_bound(levels_.begin(), levels_.end(), checkpoint.depth,
                       [](Level const& level, std::uint32_t token) {
        return level.checkpoint.depth < token;
      });
  if (checkpoint.generation != generation_ || found == levels_.end() ||
      !(found->checkpoint == checkpoint))
  {
    throw StorageFailure(StorageFailureKind::InvalidCheckpoint,
                         "ExactSimplex::pop",
                         "stale or foreign checkpoint");
  }
  pivot_in_progress_ = true;
  std::size_t const keep = found->active_size;
  /* Bounds come off in reverse; the assignment stays where it is -- it
   * satisfied every row and bound before, and bounds only got looser. */
  while (active_bounds_.size() > keep)
  {
    BoundRef const reference = active_bounds_.back();
    active_bounds_.pop_back();
    EngineBound const& bound = bound_store_[reference];
    Ordinal const v = bound.variable().ordinal();
    std::vector<BoundRef>& stack =
        bound.side() == BoundSide::Upper ? upper_stack_[v] : lower_stack_[v];
    if (!stack.empty() && stack.back() == reference)
    {
      stack.pop_back();
      DeltaRational const* const top =
          stack.empty() ? nullptr : &bound_store_[stack.back()].value();
      (bound.side() == BoundSide::Upper ? upper_ptr_[v] : lower_ptr_[v]) = top;
    }
    if (active_bound_count_[v] == 0)
      throw EngineInvariantFailure("active-bound count underflow");
    --active_bound_count_[v];
    if (status_[v] == Status::Nonbasic)
      refreshMovement(v);
    if (status_[v] == Status::Basic)
    {
      if (active_bound_count_[v] == 0)
        deactivate(row_of_[v]);
      else
        markViolation(row_of_[v]);
    }
  }
  levels_.erase(found, levels_.end());
  pivot_in_progress_ = false;
}

ExactSimplex::Explanation ExactSimplex::assertBound(BoundRef reference)
{
  EngineBound const& bound = bound_store_[reference];
  Ordinal const v = ordinalOf(bound.variable(), "ExactSimplex::assertBound");
  bool const lower = bound.side() == BoundSide::Lower;
  /* A bound that contradicts the opposite bound already asserted is a
   * conflict on the spot, of the two. */
  if (lower ? hasUpper(v) && upperValue(v) < bound.value()
            : hasLower(v) && bound.value() < lowerValue(v))
  {
    BoundRef const opposite =
        lower ? upper_stack_[v].back() : lower_stack_[v].back();
    return Explanation{{opposite, ExactRational(std::int64_t{1})},
                       {reference, ExactRational(std::int64_t{1})}};
  }
  pivot_in_progress_ = true;
  std::vector<BoundRef>& stack = lower ? lower_stack_[v] : upper_stack_[v];
  bool const tightens =
      stack.empty() ||
      (lower ? bound_store_[stack.back()].value() < bound.value()
             : bound.value() < bound_store_[stack.back()].value());
  if (tightens)
  {
    stack.push_back(reference);
    (lower ? lower_ptr_[v] : upper_ptr_[v]) = &bound.value();
  }
  active_bounds_.push_back(reference);
  ++active_bound_count_[v];
  switch (status_[v])
  {
    case Status::Dormant:
      activate(row_of_[v]);
      break;
    case Status::Basic:
      markViolation(row_of_[v]);
      break;
    case Status::Nonbasic:
      if (tightens && (lower ? value_[v] < bound.value()
                             : bound.value() < value_[v]))
        changeNonbasicValue(v, bound.value());
      refreshMovement(v);
      break;
  }
  pivot_in_progress_ = false;
  return {};
}

/* ---- rows and columns ---------------------------------------------- */

ExactSimplex::Cell* ExactSimplex::findCell(Ordinal row, Ordinal variable)
{
  std::vector<Cell>& cells = rows_[row].cells;
  auto const found =
      std::lower_bound(cells.begin(), cells.end(), variable, cellBefore);
  if (found == cells.end() || found->variable != variable)
    return nullptr;
  return &*found;
}

ExactSimplex::Cell const* ExactSimplex::findCell(Ordinal row, Ordinal variable) const
{
  std::vector<Cell> const& cells = rows_[row].cells;
  auto const found =
      std::lower_bound(cells.begin(), cells.end(), variable, cellBefore);
  if (found == cells.end() || found->variable != variable)
    return nullptr;
  return &*found;
}

void ExactSimplex::linkCell(Ordinal row, Cell& cell)
{
  std::vector<Ordinal>& column = cols_[cell.variable];
  cell.col_position = static_cast<Ordinal>(column.size());
  column.push_back(row);
}

void ExactSimplex::unlinkCell(Ordinal row, Cell const& cell)
{
  std::vector<Ordinal>& column = cols_[cell.variable];
  Ordinal const position = cell.col_position;
  if (position >= column.size() || column[position] != row)
    throw EngineInvariantFailure("column cross-link is stale");
  Ordinal const moved = column.back();
  column[position] = moved;
  column.pop_back();
  if (moved != row)
  {
    Cell* const other = findCell(moved, cell.variable);
    if (other == nullptr)
      throw EngineInvariantFailure("moved row lacks the linked cell");
    other->col_position = position;
  }
}

void ExactSimplex::linkRow(Ordinal row)
{
  queueConflictRow(row, true);
  for (Cell& cell : rows_[row].cells)
    linkCell(row, cell);
}

void ExactSimplex::unlinkRow(Ordinal row)
{
  for (Cell const& cell : rows_[row].cells)
    unlinkCell(row, cell);
}

void ExactSimplex::normalise(Ordinal row, std::vector<char>& visiting)
{
  /* Replace every term that is no longer nonbasic by its row.  An active
   * basic's row is current; a dormant one is normalised first.  The
   * references form a DAG: a row's terms were nonbasic when the row was
   * last written, so any row they refer to was written later. */
  std::vector<Cell>& cells = rows_[row].cells;
  bool pending = false;
  for (Cell const& cell : cells)
    if (status_[cell.variable] != Status::Nonbasic)
    {
      pending = true;
      break;
    }
  if (!pending)
    return;
  if (visiting[row] != 0)
    throw EngineInvariantFailure("dormant rows form a cycle");
  visiting[row] = 1;
  std::vector<Cell> result;
  result.reserve(cells.size() * 2U);
  for (Cell const& cell : cells)
  {
    if (status_[cell.variable] == Status::Nonbasic)
    {
      result.push_back(Cell{cell.variable, 0, cell.coefficient});
      continue;
    }
    Ordinal const inner = row_of_[cell.variable];
    if (inner == kNone)
      throw EngineInvariantFailure("basic variable without a row");
    if (status_[cell.variable] == Status::Dormant)
      normalise(inner, visiting);
    for (Cell const& term : rows_[inner].cells)
    {
      ExactRational product;
      multiply(product, cell.coefficient, term.coefficient);
      result.push_back(Cell{term.variable, 0, std::move(product)});
    }
  }
  std::sort(result.begin(), result.end(),
            [](Cell const& lhs, Cell const& rhs) {
              return lhs.variable < rhs.variable;
            });
  std::vector<Cell> merged;
  merged.reserve(result.size());
  for (Cell& cell : result)
  {
    if (!merged.empty() && merged.back().variable == cell.variable)
    {
      merged.back().coefficient += cell.coefficient;
      if (merged.back().coefficient.isZero())
        merged.pop_back();
      continue;
    }
    merged.push_back(std::move(cell));
  }
  statistics_.normalised_cells += merged.size();
  cells.swap(merged);
  visiting[row] = 0;
}

void ExactSimplex::activate(Ordinal row)
{
  ++statistics_.activations;
  normalise(row, visiting_scratch_);
  Ordinal const basic = rows_[row].basic;
  DeltaRational computed;
  for (Cell const& cell : rows_[row].cells)
    computed.addScaled(cell.coefficient, value_[cell.variable]);
  value_[basic] = std::move(computed);
  status_[basic] = Status::Basic;
  linkRow(row);
  markViolation(row);
}

void ExactSimplex::deactivate(Ordinal row)
{
  ++statistics_.deactivations;
  unlinkRow(row);
  status_[rows_[row].basic] = Status::Dormant;
  row_violated_[row] = 0;
}

void ExactSimplex::substitute(Ordinal row, ExactRational const& scale,
                              std::vector<Cell> const& expression)
{
  queueConflictRow(row, true);
  /* row += scale * expression, both sorted; new cells join the columns,
   * cancelled ones leave them. */
  std::vector<Cell>& cells = rows_[row].cells;
  merge_scratch_.clear();
  merge_scratch_.reserve(cells.size() + expression.size());
  std::size_t old_index = 0;
  std::size_t new_index = 0;
  while (old_index < cells.size() || new_index < expression.size())
  {
    if (new_index == expression.size() ||
        (old_index < cells.size() &&
         cells[old_index].variable < expression[new_index].variable))
    {
      merge_scratch_.push_back(std::move(cells[old_index]));
      ++old_index;
      continue;
    }
    Cell const& term = expression[new_index];
    ++new_index;
    ExactRational contribution;
    multiply(contribution, scale, term.coefficient);
    if (old_index < cells.size() && cells[old_index].variable == term.variable)
    {
      Cell& old = cells[old_index];
      ++old_index;
      contribution += old.coefficient;
      if (contribution.isZero())
      {
        unlinkCell(row, old);
        continue;
      }
      merge_scratch_.push_back(Cell{term.variable, old.col_position, std::move(contribution)});
      continue;
    }
    Cell fresh{term.variable, 0, std::move(contribution)};
    linkCell(row, fresh);
    merge_scratch_.push_back(std::move(fresh));
  }
  cells.swap(merge_scratch_);
}

/* ---- assignment ----------------------------------------------------- */

void ExactSimplex::markViolation(Ordinal row)
{
  queueConflictRow(row);
  Ordinal const basic = rows_[row].basic;
  bool const violated = outOfLower(basic) || outOfUpper(basic);
  if (!violated)
  {
    row_violated_[row] = 0;
    return;
  }
  row_violated_[row] = 1;
  if (row_queued_[row] == 0)
  {
    row_queued_[row] = 1;
    violated_rows_.push_back(row);
  }
}

void ExactSimplex::changeNonbasicValue(Ordinal variable, DeltaRational const& target)
{
  DeltaRational const difference = target - value_[variable];
  for (Ordinal const row : cols_[variable])
  {
    Cell const* const cell = findCell(row, variable);
    if (cell == nullptr)
      throw EngineInvariantFailure("column lists a row without the cell");
    value_[rows_[row].basic].addScaled(cell->coefficient, difference);
    markViolation(row);
  }
  value_[variable] = target;
  refreshMovement(variable);
}

void ExactSimplex::pivot(Ordinal row, Ordinal entering, DeltaRational const& target)
{
  Row& pivot_row = rows_[row];
  Ordinal const leaving = pivot_row.basic;
  Cell const* const pivot_cell = findCell(row, entering);
  if (pivot_cell == nullptr || pivot_cell->coefficient.isZero())
    throw EngineInvariantFailure("pivot on a missing coefficient");
  ExactRational const pivot_coefficient = pivot_cell->coefficient;
  /* The leaving variable lands on the selected bound; the entering
   * one moves by what that takes; every other active row holding the
   * entering variable follows. */
  DeltaRational const theta = (target - value_[leaving]) / pivot_coefficient;
  for (Ordinal const other : cols_[entering])
  {
    if (other == row)
      continue;
    Cell const* const cell = findCell(other, entering);
    if (cell == nullptr)
      throw EngineInvariantFailure("column lists a row without the cell");
    value_[rows_[other].basic].addScaled(cell->coefficient, theta);
  }
  value_[entering] += theta;
  value_[leaving] = target;
  // Leaving has no column yet. Record its new headroom before inserting
  // it into the changed rows (whose counts will be recomputed).
  if (movement_initialized_)
    movement_[leaving] = movementMask(leaving);
  /* The pivot row solved for the entering variable: entering =
   * leaving / a - sum_{j != entering} (a_j / a) x_j. */
  ExactRational const inverse = pivot_coefficient.inverse();
  std::vector<Cell> expression;
  expression.reserve(pivot_row.cells.size());
  for (Cell const& cell : pivot_row.cells)
  {
    if (cell.variable == entering)
      continue;
    ExactRational product;
    multiply(product, cell.coefficient, inverse);
    product.negate();
    expression.push_back(Cell{cell.variable, 0, std::move(product)});
  }
  {
    Cell leaving_cell{leaving, 0, inverse};
    auto const position = std::lower_bound(expression.begin(), expression.end(),
                                           leaving, cellBefore);
    expression.insert(position, std::move(leaving_cell));
  }
  /* Substitute into every other active holder; the loop mutates the
   * column, so it walks a copy. */
  std::vector<Ordinal> const holders = cols_[entering];
  for (Ordinal const other : holders)
  {
    if (other == row)
      continue;
    Cell const* const held = findCell(other, entering);
    if (held == nullptr)
      throw EngineInvariantFailure("column lists a row without the cell");
    ExactRational const scale = held->coefficient;
    unlinkCell(other, *held);
    {
      std::vector<Cell>& cells = rows_[other].cells;
      auto const at = std::lower_bound(cells.begin(), cells.end(), entering, cellBefore);
      cells.erase(at);
    }
    substitute(other, scale, expression);
    markViolation(other);
  }
  /* The pivot row itself. */
  unlinkRow(row);
  pivot_row.cells.swap(expression);
  pivot_row.basic = entering;
  row_of_[leaving] = kNone;
  row_of_[entering] = row;
  status_[leaving] = Status::Nonbasic;
  row_violated_[row] = 0;
  if (active_bound_count_[entering] != 0)
  {
    status_[entering] = Status::Basic;
    linkRow(row);
    markViolation(row);
  }
  else
  {
    status_[entering] = Status::Dormant;
  }
  ++statistics_.pivots;
}

/* ---- the check ------------------------------------------------------ */

unsigned char ExactSimplex::movementMask(Ordinal v) const
{
  return (!hasUpper(v) || value_[v] < upperValue(v) ? 1 : 0) |
         (!hasLower(v) || lowerValue(v) < value_[v] ? 2 : 0);
}

void ExactSimplex::queueConflictRow(Ordinal row, bool dirty)
{
  if (!early_conflicts_ || !movement_initialized_)
    return;
  Row& r = rows_[row];
  r.movement_dirty |= dirty;
  if (!r.conflict_queued)
  {
    conflict_rows_.push_back(row);
    r.conflict_queued = true;
  }
}

void ExactSimplex::refreshMovement(Ordinal v)
{
  if (!early_conflicts_ || !movement_initialized_)
    return;
  unsigned char const old = movement_[v], now = movementMask(v);
  if (old == now)
    return;
  movement_[v] = now;
  for (Ordinal index : cols_[v])
  {
    Row& row = rows_[index];
    if (!row.movement_dirty)
    {
      bool const positive = findCell(index, v)->coefficient.sign() > 0;
      unsigned const up = positive ? 1 : 2, down = positive ? 2 : 1;
      row.can_raise -= (old & up) != 0;
      row.can_raise += (now & up) != 0;
      row.can_lower -= (old & down) != 0;
      row.can_lower += (now & down) != 0;
    }
    queueConflictRow(index);
  }
}

ExactSimplex::Ordinal ExactSimplex::earlyConflict()
{
  if (!early_conflicts_)
    return kNone;
  if (!movement_initialized_)
  {
    conflict_rows_.clear();
    for (Ordinal v = 0; v < status_.size(); ++v)
      movement_[v] = movementMask(v);
    movement_initialized_ = true;
    for (Ordinal i = 0; i < rows_.size(); ++i)
    {
      rows_[i].conflict_queued = false;
      queueConflictRow(i, true);
    }
  }
  while (!conflict_rows_.empty())
  {
    Ordinal const i = conflict_rows_.back();
    Row& row = rows_[i];
    if (status_[row.basic] == Status::Basic)
    {
      if (row.movement_dirty)
      {
        row.can_raise = row.can_lower = 0;
        for (Cell const& cell : row.cells)
        {
          bool const positive = cell.coefficient.sign() > 0;
          row.can_raise += (movement_[cell.variable] & (positive ? 1 : 2)) != 0;
          row.can_lower += (movement_[cell.variable] & (positive ? 2 : 1)) != 0;
        }
        row.movement_dirty = false;
      }
      if ((row.can_raise == 0 && outOfLower(row.basic)) ||
          (row.can_lower == 0 && outOfUpper(row.basic)))
        return i; // Keep it queued: repeated checks must still find it.
    }
    row.conflict_queued = false;
    conflict_rows_.pop_back();
  }
  return kNone;
}

bool ExactSimplex::soiStep(bool& pivoted)
{
  using Search = SoiLineSearch<DeltaRational, ExactRational>;
  std::vector<char> seen(status_.size(), 0);
  std::vector<Ordinal> candidates;
  for (Ordinal i : violated_rows_)
    if (status_[rows_[i].basic] == Status::Basic &&
        (outOfLower(rows_[i].basic) || outOfUpper(rows_[i].basic)))
      for (Cell const& cell : rows_[i].cells)
        if (!seen[cell.variable])
        {
          seen[cell.variable] = 1;
          candidates.push_back(cell.variable);
        }
  std::sort(candidates.begin(), candidates.end());
  // Bound pricing work independently of the complete repair's pivot budget.
  if (candidates.size() > 256)
    candidates.resize(256);
  Ordinal entering = kNone;
  std::optional<Search::Move> best;
  for (Ordinal v : candidates)
  {
    if (outOfLower(v) || outOfUpper(v))
      return false;
    for (bool increase : {true, false})
    {
      if ((movementMask(v) & (increase ? 1 : 2)) == 0)
        continue;
      Search search;
      ExactRational const direction(std::int64_t{increase ? 1 : -1});
      if (increase ? hasUpper(v) : hasLower(v))
      {
        auto const& bound = increase ? upperValue(v) : lowerValue(v);
        search.limit((bound - value_[v]) / direction, bound);
      }
      for (Ordinal i : cols_[v])
      {
        Row const& row = rows_[i];
        Ordinal const basic = row.basic;
        ExactRational const a = findCell(i, v)->coefficient * direction;
        if (hasLower(basic))
          search.addBound(value_[basic], lowerValue(basic), a, true,
                          i, row.cells.size());
        if (hasUpper(basic))
          search.addBound(value_[basic], upperValue(basic), a, false,
                          i, row.cells.size());
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
  pivot_in_progress_ = true;
  pivoted = best->row != Search::no_row;
  if (pivoted)
    pivot(best->row, entering, best->target);
  else
  {
    changeNonbasicValue(entering, best->target);
    ++statistics_.soi_bound_flips;
  }
  pivot_in_progress_ = false;
  ++statistics_.soi_steps;
  return true;
}

ExactSimplex::Result ExactSimplex::check(ExactSimplexObserver& observer)
{
  bool soi = soi_;
  std::size_t soi_steps = 0;
  bool bland = false;
  std::size_t repeats = 0;
  for (;;)
  {
    Ordinal const conflict = earlyConflict();
    if (conflict != kNone)
    {
      Ordinal const basic = rows_[conflict].basic;
      ++statistics_.early_conflicts;
      return Result{ResultStatus::Unsatisfied,
                    conflictingBounds(basic, outOfLower(basic))};
    }
    /* The shortest live violated row; the smallest basic under Bland. */
    Ordinal picked = kNone;
    std::size_t picked_cells = 0;
    std::size_t keep = 0;
    for (std::size_t i = 0; i < violated_rows_.size(); ++i)
    {
      Ordinal const row = violated_rows_[i];
      Ordinal const basic = rows_[row].basic;
      if (row_violated_[row] == 0 || status_[basic] != Status::Basic ||
          !(outOfLower(basic) || outOfUpper(basic)))
      {
        row_violated_[row] = 0;
        row_queued_[row] = 0;
        continue;
      }
      violated_rows_[keep++] = row;
      std::size_t const cells = rows_[row].cells.size();
      bool better;
      if (picked == kNone)
        better = true;
      else if (bland)
        better = basic < rows_[picked].basic;
      else
        better = cells < picked_cells ||
                 (cells == picked_cells && basic < rows_[picked].basic);
      if (better)
      {
        picked = row;
        picked_cells = cells;
      }
    }
    violated_rows_.resize(keep);
    if (picked == kNone)
      return Result{ResultStatus::Satisfied, {}};
    if (!bland && repeats > status_.size())
      bland = true;
    StopReason const stop = observer.pollBeforePivot();
    if (stop == StopReason::Interrupted)
      return Result{ResultStatus::Interrupted, {}};
    if (stop == StopReason::ResourceLimit)
      return Result{ResultStatus::ResourceLimit, {}};
    if (stop != StopReason::Continue)
      throw EngineInvariantFailure("observer returned an invalid stop reason");
    if (soi)
    {
      bool pivoted = false;
      if (soi_steps < status_.size() + 16U && soiStep(pivoted))
      {
        ++soi_steps;
        if (pivoted)
          observer.accountPivot(false);
        continue;
      }
      soi = false; // bounded optimization, then the complete DdM/Bland path
      ++statistics_.soi_fallbacks;
    }
    Ordinal const basic = rows_[picked].basic;
    bool const below = outOfLower(basic);
    /* Entering: a cell that can move the basic variable back -- headroom
     * judged exactly -- with the fewest active holder rows, the smallest
     * ordinal under Bland. */
    Ordinal entering = kNone;
    std::size_t entering_holders = 0;
    for (Cell const& cell : rows_[picked].cells)
    {
      Ordinal const x = cell.variable;
      bool const positive = cell.coefficient.sign() > 0;
      bool const raise = below == positive;  // the basic moves the right way when x rises
      bool const legal =
          raise ? (!hasUpper(x) || value_[x] < upperValue(x))
                : (!hasLower(x) || lowerValue(x) < value_[x]);
      if (!legal)
        continue;
      std::size_t const holders = cols_[x].size();
      bool better;
      if (entering == kNone)
        better = true;
      else if (bland)
        better = x < entering;
      else
        better = holders < entering_holders ||
                 (holders == entering_holders && x < entering);
      if (better)
      {
        entering = x;
        entering_holders = holders;
      }
    }
    if (entering == kNone)
    {
      Explanation explanation = conflictingBounds(basic, below);
      return Result{ResultStatus::Unsatisfied, std::move(explanation)};
    }
    if (bland)
      ++statistics_.bland_steps;
    else
      ++statistics_.heuristic_steps;
    ++repeats;
    pivot_in_progress_ = true;
    DeltaRational const target = below ? lowerValue(basic) : upperValue(basic);
    pivot(picked, entering, target);
    pivot_in_progress_ = false;
    observer.accountPivot(bland);
  }
}

/* ---- explanations --------------------------------------------------- */

ExactSimplex::Explanation ExactSimplex::conflictingBounds(Ordinal basic,
                                                          bool conflict_on_lower) const
{
  Explanation explanation;
  Row const& row = rows_[row_of_[basic]];
  explanation.reserve(row.cells.size() + 1U);
  explanation.push_back(ExplanationTerm{
      conflict_on_lower ? lower_stack_[basic].back() : upper_stack_[basic].back(),
      ExactRational(std::int64_t{1})});
  for (Cell const& cell : row.cells)
  {
    bool const negative = cell.coefficient.sign() < 0;
    /* Below its lower bound, the basic could only rise if a positive cell
     * rose (blocked by that cell's upper) or a negative one fell (its
     * lower); above its upper, the mirror. */
    bool const blocking_lower = negative == conflict_on_lower;
    std::vector<BoundRef> const& stack =
        blocking_lower ? lower_stack_[cell.variable] : upper_stack_[cell.variable];
    if (stack.empty())
      throw EngineInvariantFailure("conflict row cell without its blocking bound");
    ExactRational weight = cell.coefficient;
    if (negative)
      weight.negate();
    explanation.push_back(ExplanationTerm{stack.back(), std::move(weight)});
  }
  generaliseExplanation(explanation);
  return explanation;
}

DeltaRational ExactSimplex::explanationResidual(Explanation const& explanation) const
{
  /* Upper bounds add their weighted value, lower bounds subtract theirs;
   * the combination the terms certify is negative exactly when the
   * bounds contradict. */
  DeltaRational residual;
  for (ExplanationTerm const& term : explanation)
  {
    EngineBound const& bound = bound_store_[term.bound];
    if (bound.side() == BoundSide::Upper)
      residual.addScaled(term.coefficient, bound.value());
    else
      residual.addScaled(-term.coefficient, bound.value());
  }
  return residual;
}

void ExactSimplex::generaliseExplanation(Explanation& explanation) const
{
  /* Restate each term on the weakest bound of its variable that still
   * leaves the residual negative: the no-good handed back is then the
   * weakest, and rules out the most.  Weakest first, greedy, left to
   * right; each variable's stack holds its asserted bounds in tightening
   * order, so the front is the weakest. */
  DeltaRational residual = explanationResidual(explanation);
  if (residual.sign() >= 0)
    return;
  for (ExplanationTerm& term : explanation)
  {
    EngineBound const& current = bound_store_[term.bound];
    Ordinal const v = current.variable().ordinal();
    bool const upper = current.side() == BoundSide::Upper;
    std::vector<BoundRef> const& stack = upper ? upper_stack_[v] : lower_stack_[v];
    for (BoundRef candidate : stack)
    {
      if (candidate == term.bound)
        break;  // reached the bound in use: nothing weaker works
      DeltaRational const& candidate_value = bound_store_[candidate].value();
      DeltaRational shifted = residual;
      /* Swapping the bound changes the residual by the weighted
       * difference of the values, in the sign of the type. */
      DeltaRational difference = candidate_value - current.value();
      if (!upper)
        difference.negate();
      shifted.addScaled(term.coefficient, difference);
      if (shifted.sign() < 0)
      {
        residual = std::move(shifted);
        term.bound = candidate;
        ++statistics_.explanation_generalisations;
        break;
      }
    }
  }
}

/* ---- models --------------------------------------------------------- */

std::optional<DeltaRational> ExactSimplex::decisionValue(VariableId variable) const
{
  Ordinal stack[64];
  std::size_t work = 0;
  auto evaluate = [&](auto const& self, Ordinal v, std::size_t depth)
      -> std::optional<DeltaRational> {
    if (status_[v] != Status::Dormant)
      return value_[v];
    if (depth == 64)
      return std::nullopt;
    for (std::size_t i = 0; i < depth; ++i)
      if (stack[i] == v)
        return std::nullopt;
    stack[depth] = v;
    DeltaRational result;
    for (Cell const& cell : rows_[row_of_[v]].cells)
    {
      if (++work > 256)
        return std::nullopt;
      auto held = self(self, cell.variable, depth + 1);
      if (!held)
        return std::nullopt;
      result.addScaled(cell.coefficient, *held);
    }
    return result;
  };
  return evaluate(evaluate, ordinalOf(variable, "decisionValue"), 0);
}

std::size_t ExactSimplex::separateCoincidentValues()
{
  if (pivot_in_progress_)
    return 0;

  // Which values are held more than once, and by whom. Only a variable that
  // shares its value has anything to gain from moving, and a variable that
  // moves must not land on a value someone else holds, so the same map
  // answers both questions.
  std::map<DeltaRational, std::vector<Ordinal>> holders;
  for (Ordinal v = 0; v != value_.size(); ++v)
    holders[value_[v]].push_back(v);

  std::size_t moved = 0;
  for (auto& entry : holders)
  {
    if (entry.second.size() < 2)
      continue;
    // Leave the first holder where it is: separating a class of n needs
    // n-1 moves, and moving them all would be churn for the same result.
    for (std::size_t i = 1; i != entry.second.size(); ++i)
    {
      Ordinal const v = entry.second[i];
      if (status_[v] != Status::Nonbasic)
        continue;
      if (hasLower(v) && hasUpper(v) && lowerValue(v) == upperValue(v))
        continue;

      DeltaRational low;
      DeltaRational high;
      bool has_low = false;
      bool has_high = false;
      if (!safeAdjustInterval(v, low, has_low, high, has_high))
        continue;

      DeltaRational target;
      if (!chooseSeparatedValue(v, low, has_low, high, has_high, holders,
                                target))
        continue;
      // A move updates holder rows before the nonbasic value. Preserve the
      // mutation marker if arithmetic stops midway, so the core invalidates
      // the incomplete assignment instead of treating it as retryable.
      pivot_in_progress_ = true;
      changeNonbasicValue(v, target);
      pivot_in_progress_ = false;
      holders[target].push_back(v);
      ++moved;
    }
  }
  if (moved != 0)
    statistics_.value_separations += moved;
  return moved;
}

// The interval of values v may take with every asserted bound still
// satisfied: its own, and those of the basic variable of each row it
// occurs in, which shifts by the row's coefficient for every unit v moves.
// Rows that are dormant are absent from the column lists and need no term
// here -- a dormant row's basic value is recomputed from its cells when the
// row is activated, so a nonbasic move cannot leave one stale.
bool ExactSimplex::safeAdjustInterval(Ordinal v, DeltaRational& low,
                                      bool& has_low, DeltaRational& high,
                                      bool& has_high) const
{
  has_low = false;
  has_high = false;
  if (hasLower(v))
  {
    low = lowerValue(v);
    has_low = true;
  }
  if (hasUpper(v))
  {
    high = upperValue(v);
    has_high = true;
  }

  for (Ordinal const row : cols_[v])
  {
    Cell const* const cell = findCell(row, v);
    if (cell == nullptr || cell->coefficient.isZero())
      return false;
    Ordinal const basic = rows_[row].basic;
    ExactRational const& a = cell->coefficient;
    // basic = ... + a*v, so moving v to t moves basic by a*(t - value_[v]);
    // requiring L <= basic' <= U bounds t from each side, with the sense of
    // the division deciding which side.
    const bool positive = a.sign() > 0;
    if (hasLower(basic))
    {
      DeltaRational limit = value_[v];
      DeltaRational slack = value_[basic];
      slack -= lowerValue(basic);
      slack /= a;
      limit -= slack;
      if (positive)
      {
        if (!has_low || limit > low) { low = limit; has_low = true; }
      }
      else if (!has_high || limit < high) { high = limit; has_high = true; }
    }
    if (hasUpper(basic))
    {
      DeltaRational limit = value_[v];
      DeltaRational slack = value_[basic];
      slack -= upperValue(basic);
      slack /= a;
      limit -= slack;
      if (positive)
      {
        if (!has_high || limit < high) { high = limit; has_high = true; }
      }
      else if (!has_low || limit > low) { low = limit; has_low = true; }
    }
  }
  return !has_low || !has_high || low <= high;
}

// A value inside the interval that nobody holds. The candidates are ordered
// so the model stays as close to the one the search produced as the slack
// allows: an endpoint first, then the midpoint, rather than an arbitrary
// interior point.
bool ExactSimplex::chooseSeparatedValue(
    Ordinal v, DeltaRational const& low, bool has_low, DeltaRational const& high,
    bool has_high, std::map<DeltaRational, std::vector<Ordinal>> const& holders,
    DeltaRational& target) const
{
  std::vector<DeltaRational> candidates;
  if (has_low)
    candidates.push_back(low);
  if (has_high)
    candidates.push_back(high);
  if (has_low && has_high)
  {
    DeltaRational middle = low;
    middle += high;
    middle /= ExactRational(std::int64_t{2});
    candidates.push_back(middle);
  }
  else if (has_low)
  {
    DeltaRational above = low;
    above += DeltaRational(ExactRational(std::int64_t{1}));
    candidates.push_back(above);
  }
  else if (has_high)
  {
    DeltaRational below = high;
    below -= DeltaRational(ExactRational(std::int64_t{1}));
    candidates.push_back(below);
  }
  else
  {
    DeltaRational away = value_[v];
    away += DeltaRational(ExactRational(std::int64_t{1}));
    candidates.push_back(away);
  }

  for (DeltaRational const& candidate : candidates)
  {
    if (candidate == value_[v])
      continue;
    if (has_low && candidate < low)
      continue;
    if (has_high && candidate > high)
      continue;
    if (holders.find(candidate) != holders.end())
      continue;
    target = candidate;
    return true;
  }
  return false;
}

DeltaRational ExactSimplex::value(VariableId variable) const
{
  std::vector<DeltaRational> out;
  values(std::vector<VariableId>{variable}, out);
  return std::move(out.front());
}

void ExactSimplex::values(std::vector<VariableId> const& variables,
                          std::vector<DeltaRational>& out) const
{
  /* A dormant row keeps no value; its row, normalised over the current
   * nonbasics, gives one.  Normalisation rewrites the row in place, which
   * is why the engine is mutable here in spirit and const in signature:
   * the rewritten row is the same row. */
  ExactSimplex& self = const_cast<ExactSimplex&>(*this);
  out.clear();
  out.reserve(variables.size());
  for (VariableId requested : variables)
  {
    Ordinal const v = ordinalOf(requested, "ExactSimplex::values");
    if (status_[v] != Status::Dormant)
    {
      out.push_back(value_[v]);
      continue;
    }
    Ordinal const row = row_of_[v];
    self.normalise(row, self.visiting_scratch_);
    DeltaRational computed;
    for (Cell const& cell : rows_[row].cells)
      computed.addScaled(cell.coefficient, value_[cell.variable]);
    self.value_[v] = computed;
    out.push_back(std::move(computed));
  }
}

ExactRational ExactSimplex::modelInfinitesimal() const
{
  /* The infinitesimal a model can substitute: the smallest ratio at which
   * a bounded variable's delta part would carry it across its bound,
   * halved; one when nothing limits it.  Bounded variables are never
   * dormant, so their values are current. */
  std::optional<ExactRational> limiting;
  ExactRational const one(std::int64_t{1});
  for (Ordinal v = 0; v < status_.size(); ++v)
  {
    if (status_[v] == Status::Dormant)
      continue;
    DeltaRational const& current = value_[v];
    if (current.infinitesimal().isZero())
      continue;
    if (hasLower(v))
    {
      DeltaRational const& lower = lowerValue(v);
      if (lower.rational() < current.rational() && current.infinitesimal() < lower.infinitesimal())
      {
        ExactRational ratio = (current.rational() - lower.rational()) / (lower.infinitesimal() - current.infinitesimal());
        if (!limiting || ratio < *limiting)
          limiting = std::move(ratio);
      }
    }
    if (hasUpper(v))
    {
      DeltaRational const& upper = upperValue(v);
      if (current.rational() < upper.rational() && upper.infinitesimal() < current.infinitesimal())
      {
        ExactRational ratio = (upper.rational() - current.rational()) / (current.infinitesimal() - upper.infinitesimal());
        if (!limiting || ratio < *limiting)
          limiting = std::move(ratio);
      }
    }
  }
  if (!limiting || one < *limiting)
    return one;
  return *limiting / ExactRational(std::int64_t{2});
}

bool ExactSimplex::invariantHolds() const
{
  /* Every nonbasic variable within its bounds; every cross-link exact. */
  for (Ordinal v = 0; v < status_.size(); ++v)
    if (status_[v] == Status::Nonbasic && (outOfLower(v) || outOfUpper(v)))
      return false;
  for (Ordinal v = 0; v < cols_.size(); ++v)
    for (Ordinal const row : cols_[v])
    {
      Cell const* const cell = findCell(row, v);
      if (cell == nullptr || cols_[v][cell->col_position] != row)
        return false;
    }
  return true;
}

void ExactSimplex::clearUnassertedTableau()
{
  if (!active_bounds_.empty() || !levels_.empty() || pivot_in_progress_)
    throw EngineInvariantFailure("tableau restart requires no asserted bounds");
  movement_initialized_ = false;
  movement_.clear();
  conflict_rows_.clear();
  std::vector<Status>().swap(status_);
  std::vector<Ordinal>().swap(row_of_);
  std::vector<Row>().swap(rows_);
  std::vector<std::vector<Ordinal>>().swap(cols_);
  std::vector<DeltaRational>().swap(value_);
  std::vector<std::vector<BoundRef>>().swap(lower_stack_);
  std::vector<std::vector<BoundRef>>().swap(upper_stack_);
  std::vector<DeltaRational const*>().swap(lower_ptr_);
  std::vector<DeltaRational const*>().swap(upper_ptr_);
  std::vector<char>().swap(visiting_scratch_);
  std::vector<std::uint32_t>().swap(active_bound_count_);
  std::vector<BoundRef>().swap(active_bounds_);
  std::vector<Level>().swap(levels_);
  std::vector<char>().swap(row_violated_);
  std::vector<char>().swap(row_queued_);
  std::vector<Ordinal>().swap(violated_rows_);
  std::vector<Cell>().swap(merge_scratch_);
  pivot_in_progress_ = false;
}

}  // namespace stp::lra

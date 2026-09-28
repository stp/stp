#include "FloatBasis.h"

#include <algorithm>
#include <cmath>

namespace stp::lra
{

namespace
{

/* Threshold partial pivoting: a Markowitz candidate must be at least this
 * fraction of the largest active entry in its column.  Stability against
 * sparsity, the usual LP trade. */
constexpr double kPivotThreshold = 0.01;
/* Below this a pivot is a zero, and the factorisation reports the matrix
 * singular rather than dividing by noise. */
constexpr double kSingularPivot = 1.0e-12;
/* This many updates, or this much growth of the upper factor and the row
 * etas over the fresh factor, is worth a fresh factorisation. */
constexpr std::size_t kUpdateBudget = 128;
/* Back substitution walks the whole upper factor once the steps the
 * sources feed directly number more than this fraction of the
 * dimension: past that the closure is most of the basis and the graph
 * search costs more than the streaming pass it would save. */
constexpr FloatBasis::Index kDenseDivisor = 8;

using Index = FloatBasis::Index;
using Entry = FloatBasis::Entry;

bool entryBefore(Entry const& entry, Index index) noexcept
{
  return entry.index < index;
}

const Entry* findEntry(const std::vector<Entry>& cells, Index index) noexcept
{
  auto const found = std::lower_bound(cells.begin(), cells.end(), index,
                                      entryBefore);
  if (found == cells.end() || found->index != index)
    return nullptr;
  return &*found;
}

}  // namespace

bool FloatBasis::refactorDue() const noexcept
{
  return ready_ && (row_etas_.size() >= kUpdateBudget ||
                    upper_nonzeros_ + eta_nonzeros_ >
                        2U * factor_nonzeros_ + dimension_);
}

bool FloatBasis::refactor(Index dimension,
                          const std::vector<std::vector<Entry>>& columns,
                          bool robust)
{
  ready_ = false;
  refactor_failure_ = RefactorFailure::None;
  failure_step_ = kNoIndex;
  failure_pivot_ = 0.0;
  row_etas_.clear();
  eta_nonzeros_ = 0;
  factor_nonzeros_ = 0;
  upper_nonzeros_ = 0;
  dimension_ = dimension;
  next_rank_ = dimension;
  step_of_row_.assign(dimension, kNoIndex);
  step_of_column_.assign(dimension, kNoIndex);
  mark_.assign(dimension, 0);
  listed_.assign(dimension, 0);
  work_.assign(dimension, 0.0);
  work_touched_.clear();
  spike_.assign(dimension, 0.0);
  spike_rows_.clear();
  spike_valid_ = false;
  upper_dependents_.resize(dimension);
  for (Index index = 0; index < dimension; ++index)
    upper_dependents_[index].clear();
  order_next_.resize(dimension);
  order_prev_.resize(dimension);
  for (Index index = 0; index < dimension; ++index)
  {
    order_prev_[index] = index == 0 ? kNoIndex : index - 1U;
    order_next_[index] = index + 1U == dimension ? kNoIndex : index + 1U;
  }
  order_head_ = 0;
  order_tail_ = dimension - 1U;
  if (columns.size() != dimension)
    return refactorFailed(RefactorFailure::InvalidInput);
  if (dimension == 0)
  {
    ready_ = true;
    return true;
  }
  /* The active matrix, row-wise with sorted columns, plus for each
   * column the rows that ever held an entry in it -- a list that may go
   * stale as eliminations cancel entries, so every use verifies against
   * the row itself.  The scratch keeps its capacity from one
   * factorisation to the next: a refactorisation allocates nothing
   * once warm. */
  std::vector<std::vector<Entry>>& rows = rows_;
  std::vector<std::vector<Index>>& column_rows = column_rows_;
  std::vector<Index>& row_count = row_count_;
  std::vector<Index>& column_count = column_count_;
  rows.resize(dimension);
  column_rows.resize(dimension);
  for (Index index = 0; index < dimension; ++index)
  {
    rows[index].clear();
    column_rows[index].clear();
  }
  row_count.assign(dimension, 0);
  column_count.assign(dimension, 0);
  for (Index column = 0; column < dimension; ++column)
  {
    for (Entry const& entry : columns[column])
    {
      if (entry.index >= dimension || !std::isfinite(entry.value))
        return refactorFailed(RefactorFailure::InvalidInput);
      if (entry.value == 0.0)
        continue;
      rows[entry.index].push_back(Entry{column, entry.value});
    }
  }
  for (Index row = 0; row < dimension; ++row)
  {
    std::vector<Entry>& cells = rows[row];
    std::sort(cells.begin(), cells.end(),
              [](Entry const& lhs, Entry const& rhs) {
                return lhs.index < rhs.index;
              });
    /* Duplicate columns in one row would break the sorted lookup. */
    for (std::size_t i = 1; i < cells.size(); ++i)
      if (cells[i].index == cells[i - 1].index)
        return refactorFailed(RefactorFailure::InvalidInput);
    row_count[row] = static_cast<Index>(cells.size());
    for (Entry const& cell : cells)
    {
      column_rows[cell.index].push_back(row);
      ++column_count[cell.index];
    }
  }
  std::vector<char>& row_active = row_active_;
  std::vector<char>& column_active = column_active_;
  row_active.assign(dimension, 1);
  column_active.assign(dimension, 1);
  /* Singleton columns first: pivoting one costs nothing and creates no
   * fill, and a basis of a Dutertre--de Moura tableau is mostly unit
   * columns.  Every pivot may expose new singletons.  The active
   * columns sit in a swap-removal list so that Markowitz selection
   * scans what is left, not the dimension. */
  std::vector<Index>& singletons = singletons_;
  std::vector<Index>& active_columns = active_columns_;
  std::vector<Index>& active_slot = active_slot_;
  singletons.clear();
  active_columns.resize(dimension);
  active_slot.resize(dimension);
  for (Index column = 0; column < dimension; ++column)
  {
    if (column_count[column] == 0)
      return refactorFailed(RefactorFailure::EmptyColumn);
    if (column_count[column] == 1)
      singletons.push_back(column);
    active_columns[column] = column;
    active_slot[column] = column;
  }
  std::vector<Entry>& merged = merged_;
  steps_.resize(dimension);
  for (Index step_index = 0; step_index < dimension; ++step_index)
  {
    Index pivot_row = kNoIndex;
    Index pivot_column = kNoIndex;
    double pivot_value = 0.0;
    while (!singletons.empty())
    {
      Index const column = singletons.back();
      singletons.pop_back();
      if (column_active[column] == 0 || column_count[column] != 1)
        continue;
      for (Index const row : column_rows[column])
      {
        if (row_active[row] == 0)
          continue;
        const Entry* const cell = findEntry(rows[row], column);
        if (cell == nullptr)
          continue;
        pivot_row = row;
        pivot_column = column;
        pivot_value = cell->value;
        break;
      }
      if (pivot_row != kNoIndex)
        break;
    }
    if (pivot_row == kNoIndex)
    {
      /* Markowitz over the active remainder: the columns of smallest
       * count, their entries above the stability threshold, the
       * candidate of least (r - 1)(c - 1). */
      Index best_count = kNoIndex;
      for (Index const column : active_columns)
        if (column_count[column] < best_count)
          best_count = column_count[column];
      if (best_count == kNoIndex)
        return refactorFailed(RefactorFailure::NoPivot, step_index);
      double best_cost = 0.0;
      double best_magnitude = 0.0;
      Index columns_examined = 0;
      for (std::size_t slot = 0;
           slot < active_columns.size() && (robust || columns_examined < 4);
           ++slot)
      {
        Index const column = active_columns[slot];
        if (!robust && column_count[column] > best_count + 1)
          continue;
        ++columns_examined;
        double column_max = 0.0;
        for (Index const row : column_rows[column])
        {
          if (row_active[row] == 0)
            continue;
          const Entry* const cell = findEntry(rows[row], column);
          if (cell != nullptr)
            column_max = std::fmax(column_max, std::fabs(cell->value));
        }
        for (Index const row : column_rows[column])
        {
          if (row_active[row] == 0)
            continue;
          const Entry* const cell = findEntry(rows[row], column);
          if (cell == nullptr ||
              std::fabs(cell->value) <
                  (robust ? 0.1 : kPivotThreshold) * column_max)
            continue;
          double const cost =
              static_cast<double>(row_count[row] - 1U) *
              static_cast<double>(column_count[column] - 1U);
          if (pivot_row == kNoIndex ||
              (robust ? std::fabs(cell->value) > best_magnitude
                      : cost < best_cost ||
                            (cost == best_cost &&
                             std::fabs(cell->value) > best_magnitude)))
          {
            pivot_row = row;
            pivot_column = column;
            pivot_value = cell->value;
            best_cost = cost;
            best_magnitude = std::fabs(cell->value);
          }
        }
      }
      if (pivot_row == kNoIndex)
        return refactorFailed(RefactorFailure::NoPivot, step_index);
    }
    if (!(std::fabs(pivot_value) > kSingularPivot) ||
        !std::isfinite(pivot_value))
      return refactorFailed(std::isfinite(pivot_value)
                                ? RefactorFailure::SmallPivot
                                : RefactorFailure::Nonfinite,
                            step_index, pivot_value);
    Step& step = steps_[step_index];
    step.row = pivot_row;
    step.column = pivot_column;
    step.pivot = pivot_value;
    step.rank = step_index;
    step.lower.clear();
    step.upper.clear();
    std::vector<Entry> const& pivot_cells = rows[pivot_row];
    step.upper.reserve(pivot_cells.size());
    for (Entry const& cell : pivot_cells)
      if (cell.index != pivot_column)
        step.upper.push_back(cell);
    /* Eliminate the pivot column from every other active row that holds
     * it: row_i -= (a_iq / a_pq) row_p, a sorted merge with fill-in. */
    for (Index const row : column_rows[pivot_column])
    {
      if (row == pivot_row || row_active[row] == 0)
        continue;
      std::vector<Entry>& cells = rows[row];
      const Entry* const held = findEntry(cells, pivot_column);
      if (held == nullptr)
        continue;
      double const multiplier = held->value / pivot_value;
      if (!std::isfinite(multiplier))
        return refactorFailed(RefactorFailure::Nonfinite, step_index,
                              multiplier);
      step.lower.push_back(Entry{row, multiplier});
      merged.clear();
      merged.reserve(cells.size() + pivot_cells.size());
      std::size_t old_index = 0;
      std::size_t new_index = 0;
      while (old_index < cells.size() || new_index < pivot_cells.size())
      {
        bool const take_old =
            new_index == pivot_cells.size() ||
            (old_index < cells.size() &&
             cells[old_index].index < pivot_cells[new_index].index);
        if (take_old)
        {
          if (cells[old_index].index != pivot_column)
            merged.push_back(cells[old_index]);
          ++old_index;
          continue;
        }
        Entry const& source = pivot_cells[new_index];
        ++new_index;
        if (source.index == pivot_column)
          continue;
        double value = -multiplier * source.value;
        double scale = std::fabs(value);
        if (old_index < cells.size() && cells[old_index].index == source.index)
        {
          value += cells[old_index].value;
          scale = std::fmax(scale, std::fabs(cells[old_index].value));
          ++old_index;
          if (std::fabs(value) <= 1.0e-14 * scale)
          {
            /* Cancelled: the entry leaves the active matrix.  The
             * column's row list keeps a stale row, which lookups skip. */
            --column_count[source.index];
            continue;
          }
        }
        else
        {
          /* Fill-in. */
          column_rows[source.index].push_back(row);
          ++column_count[source.index];
        }
        if (!std::isfinite(value))
          return refactorFailed(RefactorFailure::Nonfinite, step_index, value);
        merged.push_back(Entry{source.index, value});
      }
      cells.swap(merged);
      row_count[row] = static_cast<Index>(cells.size());
    }
    /* Retire the pivot row and column. */
    row_active[pivot_row] = 0;
    column_active[pivot_column] = 0;
    {
      Index const slot = active_slot[pivot_column];
      Index const moved = active_columns.back();
      active_columns[slot] = moved;
      active_slot[moved] = slot;
      active_columns.pop_back();
    }
    for (Entry const& cell : pivot_cells)
    {
      if (cell.index == pivot_column)
        continue;
      if (--column_count[cell.index] == 1)
        singletons.push_back(cell.index);
    }
    factor_nonzeros_ += step.lower.size() + step.upper.size() + 1U;
    upper_nonzeros_ += step.upper.size();
  }
  /* The graph the hyper-sparse solves walk: the upper dependents per
   * column, the lower eliminators as compressed lists (a counting pass,
   * offsets, a filling pass). */
  lower_eliminators_start_.assign(dimension + 1U, 0);
  for (Index index = 0; index < dimension; ++index)
  {
    Step const& step = steps_[index];
    step_of_row_[step.row] = index;
    step_of_column_[step.column] = index;
    for (Entry const& upper : step.upper)
      upper_dependents_[upper.index].push_back(index);
    for (Entry const& lower : step.lower)
      ++lower_eliminators_start_[lower.index + 1U];
  }
  for (Index index = 0; index < dimension; ++index)
    lower_eliminators_start_[index + 1U] += lower_eliminators_start_[index];
  lower_eliminators_.resize(lower_eliminators_start_[dimension]);
  {
    /* Fill from the offsets, advancing each list's cursor in place; the
     * cursors are restored to the offsets by the shift below. */
    std::vector<Index>& cursor = lower_eliminators_start_;
    for (Index index = 0; index < dimension; ++index)
      for (Entry const& lower : steps_[index].lower)
        lower_eliminators_[cursor[lower.index]++] = index;
    for (Index index = dimension; index > 0; --index)
      cursor[index] = cursor[index - 1U];
    cursor[0] = 0;
  }
  step_column_.resize(dimension);
  lower_size_.resize(dimension);
  upper_size_.resize(dimension);
  dependents_size_.resize(dimension);
  eliminators_size_.resize(dimension);
  for (Index index = 0; index < dimension; ++index)
  {
    Step const& step = steps_[index];
    step_column_[index] = step.column;
    lower_size_[index] = static_cast<Index>(step.lower.size());
    upper_size_[index] = static_cast<Index>(step.upper.size());
    dependents_size_[index] =
        static_cast<Index>(upper_dependents_[step.column].size());
    eliminators_size_[index] = lower_eliminators_start_[step.row + 1U] -
                               lower_eliminators_start_[step.row];
  }
  ready_ = true;
  return true;
}

/* The four closures.  Each is an iterative depth-first search over
 * steps that appends a step once every step it feeds has been appended:
 * post-order, so the callers evaluate `out` backwards and every step
 * comes before the steps that read its result.  A step with no edges
 * in the direction searched is finished the moment it is found. */
#define STP_LRA_REACH(NAME, EDGE_COUNT, EDGE_TARGET)                         \
  void FloatBasis::NAME(Index root, std::vector<Index>& out) const         \
  {                                                                        \
    if (mark_[root] != 0)                                                  \
      return;                                                              \
    mark_[root] = 1;                                                       \
    if (EDGE_COUNT[root] == 0)                                             \
    {                                                                      \
      out.push_back(root);                                                 \
      return;                                                              \
    }                                                                      \
    stack_.clear();                                                        \
    stack_edge_.clear();                                                   \
    stack_.push_back(root);                                                \
    stack_edge_.push_back(0);                                              \
    while (!stack_.empty())                                                \
    {                                                                      \
      std::size_t const top = stack_.size() - 1U;                          \
      Index const current = stack_[top];                                   \
      Index const edge_count = EDGE_COUNT[current];                        \
      bool descended = false;                                              \
      while (stack_edge_[top] < edge_count)                                \
      {                                                                    \
        Index const edge = stack_edge_[top]++;                             \
        Index const next = EDGE_TARGET;                                    \
        if (mark_[next] != 0)                                              \
          continue;                                                        \
        mark_[next] = 1;                                                   \
        if (EDGE_COUNT[next] == 0)                                         \
        {                                                                  \
          out.push_back(next);                                             \
          continue;                                                        \
        }                                                                  \
        stack_.push_back(next);                                            \
        stack_edge_.push_back(0);                                          \
        descended = true;                                                  \
        break;                                                             \
      }                                                                    \
      if (descended)                                                       \
        continue;                                                          \
      out.push_back(current);                                              \
      stack_.pop_back();                                                   \
      stack_edge_.pop_back();                                              \
    }                                                                      \
  }

/* Forward through L: a nonzero at the pivot row of a step spreads to the
 * rows its multipliers touch, each pivoted by a later step. */
STP_LRA_REACH(reachLower, lower_size_,
              step_of_row_[steps_[current].lower[edge].index])
/* Back substitution: a nonzero x at the column of a step feeds every
 * earlier step whose upper part lists that column. */
STP_LRA_REACH(reachUpperBackward, dependents_size_,
              upper_dependents_[step_column_[current]][edge])
/* U transposed: a nonzero at the pivot row of a step feeds the later
 * steps that pivot the columns of its upper part. */
STP_LRA_REACH(reachUpperForward, upper_size_,
              step_of_column_[steps_[current].upper[edge].index])
/* L transposed: a nonzero at the pivot row of a step feeds the earlier
 * steps whose multipliers touched that row. */
STP_LRA_REACH(reachLowerTransposed, eliminators_size_,
              lower_eliminators_[lower_eliminators_start_[steps_[current].row] + edge])
#undef STP_LRA_REACH

void FloatBasis::clearMarks(const std::vector<Index>& steps) const
{
  for (Index const step : steps)
    mark_[step] = 0;
}

void FloatBasis::dropSpike() const
{
  for (Index const row : spike_rows_)
    spike_[row] = 0.0;
  spike_rows_.clear();
  spike_valid_ = false;
}

void FloatBasis::fail()
{
  ready_ = false;
  dropSpike();
}

bool FloatBasis::ftran(std::vector<double>& vector,
                       std::vector<Index>& nonzeros) const
{
  if (!ready_ || vector.size() != dimension_)
    return false;
  dropSpike();
  /* L: the steps reachable from the rows the right-hand side occupies,
   * applied in elimination order. */
  reached_.clear();
  for (Index const row : nonzeros)
    if (vector[row] != 0.0)
      reachLower(step_of_row_[row], reached_);
  for (auto it = reached_.rbegin(); it != reached_.rend(); ++it)
  {
    Step const& step = steps_[*it];
    double const pivot_entry = vector[step.row];
    if (pivot_entry == 0.0)
      continue;
    for (Entry const& lower : step.lower)
      vector[lower.index] -= lower.value * pivot_entry;
  }
  /* The row etas in order: each changes one row by what its terms
   * read, and a row that comes alive joins the sources. */
  for (RowEta const& eta : row_etas_)
  {
    double sum = 0.0;
    for (Entry const& term : eta.terms)
      sum += term.value * vector[term.index];
    if (sum == 0.0)
      continue;
    Index const step = step_of_row_[eta.row];
    if (mark_[step] == 0)
    {
      mark_[step] = 1;
      reached_.push_back(step);
    }
    vector[eta.row] -= sum;
  }
  /* The spike: this right-hand side after L and the row etas, kept for
   * an update that makes it a basis column. */
  for (Index const index : reached_)
  {
    Index const row = steps_[index].row;
    spike_[row] = vector[row];
    spike_rows_.push_back(row);
  }
  spike_valid_ = true;
  /* Back substitution, latest first, over the steps a nonzero can
   * reach; the result is indexed by column position and built in
   * work_.  The steps the sources feed directly bound the closure from
   * above: when they already number a good part of the dimension, the
   * whole upper factor is walked in rank order instead. */
  std::vector<Index> const& sources = reached_;
  std::vector<Index>& targets = work_touched_;
  targets.clear();
  clearMarks(sources);
  std::size_t fed = 0;
  for (Index const index : sources)
    if (vector[steps_[index].row] != 0.0)
      fed += upper_dependents_[steps_[index].column].size();
  if (fed > dimension_ / kDenseDivisor)
  {
    for (Index index = order_tail_; index != kNoIndex; index = order_prev_[index])
    {
      Step const& step = steps_[index];
      double sum = vector[step.row];
      for (Entry const& upper : step.upper)
        sum -= upper.value * work_[upper.index];
      if (sum == 0.0)
        continue;
      work_[step.column] = sum / step.pivot;
      targets.push_back(index);
    }
  }
  else
  {
    for (Index const index : sources)
      if (vector[steps_[index].row] != 0.0)
        reachUpperBackward(index, targets);
    for (auto it = targets.rbegin(); it != targets.rend(); ++it)
    {
      Step const& step = steps_[*it];
      double sum = vector[step.row];
      for (Entry const& upper : step.upper)
        sum -= upper.value * work_[upper.index];
      work_[step.column] = sum / step.pivot;
    }
    clearMarks(targets);
  }
  /* Move the result over: clear the rows the right-hand side used, hand
   * back the columns written. */
  for (Index const index : sources)
    vector[steps_[index].row] = 0.0;
  for (Index const row : nonzeros)
    vector[row] = 0.0;
  nonzeros.clear();
  for (Index const index : targets)
  {
    Index const column = steps_[index].column;
    vector[column] = work_[column];
    work_[column] = 0.0;
    nonzeros.push_back(column);
  }
  return true;
}

bool FloatBasis::btran(std::vector<double>& vector,
                       std::vector<Index>& nonzeros) const
{
  if (!ready_ || vector.size() != dimension_)
    return false;
  /* U transposed, in pivot order over the steps reachable from the
   * columns the input occupies: the unknowns are by pivot row, built in
   * work_, with the accumulated upper contributions in `vector` itself
   * (each column is read exactly once, at its own step). */
  reached_.clear();
  for (Index const column : nonzeros)
    if (vector[column] != 0.0)
      reachUpperForward(step_of_column_[column], reached_);
  for (auto it = reached_.rbegin(); it != reached_.rend(); ++it)
  {
    Step const& step = steps_[*it];
    double const value = vector[step.column] / step.pivot;
    vector[step.column] = 0.0;
    work_[step.row] = value;
    if (value == 0.0)
      continue;
    for (Entry const& upper : step.upper)
      vector[upper.index] -= upper.value * value;
  }
  for (Index const column : nonzeros)
    vector[column] = 0.0;
  nonzeros.clear();
  /* The row etas transposed, latest first: the eliminated row's value
   * feeds the rows its terms name, and a row that comes alive joins the
   * sources. */
  for (auto eta = row_etas_.rbegin(); eta != row_etas_.rend(); ++eta)
  {
    double const value = work_[eta->row];
    if (value == 0.0)
      continue;
    for (Entry const& term : eta->terms)
    {
      Index const step = step_of_row_[term.index];
      if (mark_[step] == 0)
      {
        mark_[step] = 1;
        reached_.push_back(step);
      }
      work_[term.index] -= term.value * value;
    }
  }
  /* L transposed, latest first, over the steps a nonzero row reaches. */
  std::vector<Index>& targets = work_touched_;
  targets.clear();
  clearMarks(reached_);
  for (Index const index : reached_)
    if (work_[steps_[index].row] != 0.0)
      reachLowerTransposed(index, targets);
  for (auto it = targets.rbegin(); it != targets.rend(); ++it)
  {
    Step const& step = steps_[*it];
    double sum = 0.0;
    for (Entry const& lower : step.lower)
      sum += lower.value * work_[lower.index];
    work_[step.row] -= sum;
  }
  clearMarks(targets);
  /* Everything with a value is either in reached_ (U^T and the etas
   * wrote it) or in targets (L^T touched it); collect both, once each. */
  for (Index const index : reached_)
    mark_[index] = 1;
  for (Index const index : targets)
    if (mark_[index] == 0)
    {
      mark_[index] = 1;
      reached_.push_back(index);
    }
  for (Index const index : reached_)
  {
    mark_[index] = 0;
    Index const row = steps_[index].row;
    vector[row] = work_[row];
    work_[row] = 0.0;
    nonzeros.push_back(row);
  }
  return true;
}

bool FloatBasis::update(Index position)
{
  if (!ready_ || position >= dimension_ || !spike_valid_)
  {
    fail();
    return false;
  }
  spike_valid_ = false;
  Index const step_index = step_of_column_[position];
  Step& step = steps_[step_index];
  /* The leaving column leaves U: only rows of lower rank held it. */
  for (Index const dependent : upper_dependents_[position])
  {
    std::vector<Entry>& upper = steps_[dependent].upper;
    for (std::size_t i = 0; i < upper.size(); ++i)
    {
      if (upper[i].index != position)
        continue;
      upper[i] = upper.back();
      upper.pop_back();
      --upper_size_[dependent];
      --upper_nonzeros_;
      break;
    }
  }
  upper_dependents_[position].clear();
  dependents_size_[step_index] = 0;
  /* Eliminate the pivot row against the rows of higher rank, in rank
   * order, recording the multipliers as a row eta; the pivot the row
   * keeps is the spike's own entry less what the elimination takes. */
  RowEta eta;
  eta.row = step.row;
  heap_.clear();
  auto const later = [](HeapItem const& lhs, HeapItem const& rhs) noexcept {
    return lhs.rank > rhs.rank;
  };
  for (Entry const& entry : step.upper)
  {
    work_[entry.index] = entry.value;
    listed_[entry.index] = 1;
    heap_.push_back(HeapItem{steps_[step_of_column_[entry.index]].rank,
                             entry.index});
    std::vector<Index>& dependents = upper_dependents_[entry.index];
    for (std::size_t i = 0; i < dependents.size(); ++i)
    {
      if (dependents[i] != step_index)
        continue;
      dependents[i] = dependents.back();
      dependents.pop_back();
      --dependents_size_[step_of_column_[entry.index]];
      break;
    }
  }
  upper_nonzeros_ -= step.upper.size();
  step.upper.clear();
  upper_size_[step_index] = 0;
  std::make_heap(heap_.begin(), heap_.end(), later);
  double pivot = spike_[step.row];
  bool sound = true;
  while (!heap_.empty())
  {
    std::pop_heap(heap_.begin(), heap_.end(), later);
    Index const column = heap_.back().column;
    heap_.pop_back();
    listed_[column] = 0;
    double const value = work_[column];
    work_[column] = 0.0;
    if (value == 0.0 || !sound)
      continue;
    Step const& source = steps_[step_of_column_[column]];
    double const multiplier = value / source.pivot;
    if (!std::isfinite(multiplier))
    {
      sound = false;
      continue;
    }
    eta.terms.push_back(Entry{source.row, multiplier});
    pivot -= multiplier * spike_[source.row];
    for (Entry const& upper : source.upper)
    {
      if (listed_[upper.index] == 0)
      {
        listed_[upper.index] = 1;
        heap_.push_back(HeapItem{steps_[step_of_column_[upper.index]].rank,
                                 upper.index});
        std::push_heap(heap_.begin(), heap_.end(), later);
      }
      work_[upper.index] -= multiplier * upper.value;
    }
  }
  if (!sound || !(std::fabs(pivot) > kSingularPivot) || !std::isfinite(pivot))
  {
    fail();
    return false;
  }
  /* The spike becomes the column: an entry in every other row it
   * occupies, at that row's step, all of lower rank than this one now. */
  for (Index const row : spike_rows_)
  {
    double const value = spike_[row];
    spike_[row] = 0.0;
    if (row == step.row || value == 0.0)
      continue;
    Index const other = step_of_row_[row];
    steps_[other].upper.push_back(Entry{position, value});
    ++upper_size_[other];
    upper_dependents_[position].push_back(other);
    ++upper_nonzeros_;
  }
  dependents_size_[step_index] =
      static_cast<Index>(upper_dependents_[position].size());
  spike_rows_.clear();
  step.pivot = pivot;
  step.rank = next_rank_++;
  /* The step moves to the end of the rank order. */
  if (order_tail_ != step_index)
  {
    Index const previous = order_prev_[step_index];
    Index const next = order_next_[step_index];
    if (previous == kNoIndex)
      order_head_ = next;
    else
      order_next_[previous] = next;
    order_prev_[next] = previous;
    order_prev_[step_index] = order_tail_;
    order_next_[step_index] = kNoIndex;
    order_next_[order_tail_] = step_index;
    order_tail_ = step_index;
  }
  eta_nonzeros_ += eta.terms.size();
  row_etas_.push_back(std::move(eta));
  return true;
}

}  // namespace stp::lra

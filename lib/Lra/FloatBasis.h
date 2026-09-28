#ifndef STP_LRA_FLOAT_BASIS_H
#define STP_LRA_FLOAT_BASIS_H

#include <cstddef>
#include <cstdint>
#include <vector>

namespace stp::lra
{

/* A sparse LU factorisation of a square basis matrix with Forrest--Tomlin
 * updates (Forrest & Tomlin, Math. Programming 2 (1972)) and hyper-sparse
 * solves, for the float tier's factorized representation.
 *
 * The matrix is given column by column as sparse (row, value) entries;
 * the basis of a Dutertre--de Moura tableau is mostly unit columns (the
 * basic row variables) with a sparse kernel of structural columns among
 * them, and the factorisation is built to cost what that structure
 * costs: singleton columns and rows are pivoted first in a worklist
 * pass that creates no fill, and only the remainder sees Markowitz
 * pivot selection (Markowitz, Management Science 3 (1957)) under
 * threshold partial pivoting.
 *
 * A solve costs what it touches.  The caller names the nonzeros of the
 * right-hand side, the elimination steps that can matter are found by
 * reachability through the factor's graph, and the nonzeros of the
 * result are handed back, so a unit right-hand side against a basis
 * with a kernel of ten variables costs a few dozen operations whatever
 * the dimension.  When the closure would cover much of the basis -- an
 * entering column against a strongly coupled kernel moves half the
 * basic variables -- the back substitution walks the whole upper factor
 * in rank order instead, a streaming pass that costs the factor's size
 * rather than a graph search per touched step.
 *
 * A basis change is a column replacement.  It is applied to the upper
 * factor in place: the leaving column's row of U is eliminated against
 * the rows below it into a short row eta, the spike the last FTRAN left
 * (the entering column after the lower factor and the row etas) becomes
 * the new column, and the pivot moves to the end of the elimination
 * order.  The factors stay sparse -- a row eta is as long as the row it
 * eliminated -- where a product-form column eta would carry the whole
 * dense direction and every later solve would scan it.  The caller
 * refactors from the current basis header when the update file grows
 * past its budget.  Nothing here is trusted: the tier's verdicts are
 * advisory and the exact tier judges every certificate and model, so a
 * numerically poor factor costs a rejected certificate, never an
 * answer. */
class FloatBasis final
{
public:
  using Index = std::uint32_t;
  static constexpr Index kNoIndex = 0xffffffffu;

  struct Entry final
  {
    Index index;
    double value;
  };

  /* Factorise the dimension x dimension matrix whose column j is
   * columns[j] (entries by row; a unit column is one entry of value 1).
   * False when the matrix is numerically singular; the previous factor
   * is then gone and ready() is false. */
  bool refactor(Index dimension, const std::vector<std::vector<Entry>>& columns,
                bool robust = false);
  enum class RefactorFailure : std::uint8_t
  {
    None,
    InvalidInput,
    EmptyColumn,
    NoPivot,
    SmallPivot,
    Nonfinite
  };
  RefactorFailure refactorFailure() const noexcept { return refactor_failure_; }
  Index failureStep() const noexcept { return failure_step_; }
  double failurePivot() const noexcept { return failure_pivot_; }
  /* Solve B x = b in place.  `vector` is zero except at `nonzeros`
   * (by row); on return it holds x by column position and `nonzeros`
   * lists every position that may be nonzero, each once.  The caller
   * clears those positions before the next use of the vector.  The
   * solve keeps the spike of this right-hand side for update(). */
  bool ftran(std::vector<double>& vector, std::vector<Index>& nonzeros) const;
  /* Solve B^T y = c in place, the same contract: in by column position,
   * out by row. */
  bool btran(std::vector<double>& vector, std::vector<Index>& nonzeros) const;
  /* The column at `position` is replaced by the column whose FTRAN was
   * the most recent ftran() call.  False when no spike is held or the
   * new pivot is numerically zero; the factor is then unusable and
   * ready() is false until the next refactor. */
  bool update(Index position);

  bool ready() const noexcept { return ready_; }
  Index dimension() const noexcept { return dimension_; }
  /* The caller's refactorisation policy reads this. */
  bool refactorDue() const noexcept;

private:
  bool refactorFailed(RefactorFailure why, Index step = kNoIndex,
                      double pivot = 0.0) noexcept
  {
    refactor_failure_ = why;
    failure_step_ = step;
    failure_pivot_ = pivot;
    return false;
  }
  RefactorFailure refactor_failure_ = RefactorFailure::None;
  Index failure_step_ = kNoIndex;
  double failure_pivot_ = 0.0;
  /* One elimination step: pivot at (row, column), the multipliers that
   * cleared the column below it, and the pivot row over the columns
   * pivoted later.  `rank` orders the steps for the upper factor; it is
   * the step's index after a fresh factorisation and moves to the end
   * when an update makes the step's row the last one eliminated. */
  struct Step final
  {
    Index row;
    Index column;
    double pivot;
    std::uint64_t rank;
    std::vector<Entry> lower;  // (row, multiplier)
    std::vector<Entry> upper;  // (column, value)
  };
  /* An update's elimination of one row of U against the rows of higher
   * rank: applied to a right-hand side after the lower factor, the row
   * loses the named rows' values times the multipliers. */
  struct RowEta final
  {
    Index row;
    std::vector<Entry> terms;  // (row, multiplier)
  };
  struct HeapItem final
  {
    std::uint64_t rank;
    Index column;
  };

  /* Reachability closures over the factor's graph, the four directions
   * the two solves need.  Each is a depth-first search that appends the
   * steps found to `out` in post-order, so reading `out` backwards is a
   * topological order of the closure -- every step before the steps its
   * entries feed -- with no sort.  Marks are left for the caller to
   * clear. */
  void reachLower(Index step, std::vector<Index>& out) const;
  void reachUpperBackward(Index step, std::vector<Index>& out) const;
  void reachUpperForward(Index step, std::vector<Index>& out) const;
  void reachLowerTransposed(Index step, std::vector<Index>& out) const;
  void clearMarks(const std::vector<Index>& steps) const;
  void dropSpike() const;
  void fail();

  /* steps_ keeps `dimension_` entries whose inner vectors retain their
   * capacity across refactorisations. */
  std::vector<Step> steps_;
  std::vector<RowEta> row_etas_;
  Index dimension_ = 0;
  bool ready_ = false;
  std::uint64_t next_rank_ = 0;
  std::size_t factor_nonzeros_ = 0;
  std::size_t upper_nonzeros_ = 0;
  std::size_t eta_nonzeros_ = 0;
  /* The graph: which step pivots each row and column, which steps list
   * a column in their upper part (per column, since updates move
   * entries), which steps eliminate a row (compressed: the lower factor
   * is fixed between refactorisations). */
  std::vector<Index> step_of_row_;
  std::vector<Index> step_of_column_;
  std::vector<std::vector<Index>> upper_dependents_;
  /* Compact per-step copies of what the closures read most: the step's
   * column, and its out-degree in each of the four directions, so a
   * leaf (most steps, for a basis that is mostly unit columns) costs
   * the search a few array reads and no visit to the step itself. */
  std::vector<Index> step_column_;
  std::vector<Index> lower_size_;
  std::vector<Index> upper_size_;
  std::vector<Index> dependents_size_;
  std::vector<Index> eliminators_size_;
  /* The steps in rank order as a doubly linked list, for the solves that
   * walk the whole upper factor instead of a closure. */
  std::vector<Index> order_next_;
  std::vector<Index> order_prev_;
  Index order_head_ = kNoIndex;
  Index order_tail_ = kNoIndex;
  std::vector<Index> lower_eliminators_start_;
  std::vector<Index> lower_eliminators_;
  mutable std::vector<char> mark_;
  mutable std::vector<Index> reached_;
  mutable std::vector<Index> stack_;
  mutable std::vector<Index> stack_edge_;
  mutable std::vector<double> work_;
  mutable std::vector<Index> work_touched_;
  mutable std::vector<char> listed_;
  /* The spike of the last FTRAN, by row. */
  mutable std::vector<double> spike_;
  mutable std::vector<Index> spike_rows_;
  mutable bool spike_valid_ = false;
  std::vector<HeapItem> heap_;
  /* Refactorisation scratch, retained between calls: the active matrix
   * row-wise, the rows each column has held, counts, activity, the
   * singleton worklist, the active columns for Markowitz selection and
   * each column's slot in that list. */
  std::vector<std::vector<Entry>> rows_;
  std::vector<std::vector<Index>> column_rows_;
  std::vector<Index> row_count_;
  std::vector<Index> column_count_;
  std::vector<char> row_active_;
  std::vector<char> column_active_;
  std::vector<Index> singletons_;
  std::vector<Index> active_columns_;
  std::vector<Index> active_slot_;
  std::vector<Entry> merged_;
};

}  // namespace stp::lra

#endif

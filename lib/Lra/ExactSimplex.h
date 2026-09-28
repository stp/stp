#ifndef STP_LRA_EXACT_SIMPLEX_H
#define STP_LRA_EXACT_SIMPLEX_H

#include "ExactLraTypes.h"
#include "DeltaRational.h"
#include "BoundStore.h"
#include "Storage/StorageMetrics.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <map>
#include <vector>

namespace stp::lra
{

/* A broken engine invariant.  The core catches it at its boundary and
 * reports an internal error rather than an answer. */
class EngineInvariantFailure final : public std::runtime_error
{
public:
  explicit EngineInvariantFailure(std::string message)
      : std::runtime_error(std::move(message))
  {}
  explicit EngineInvariantFailure(char const* message)
      : std::runtime_error(message)
  {}
};

struct ExactSimplexStats final
{
  std::uint64_t heuristic_steps = 0;
  std::uint64_t bland_steps = 0;
  std::uint64_t pivots = 0;
  std::uint64_t explanation_generalisations = 0;
  // Dormant rows brought into the tableau and taken out again, and the
  // cells the normalisations on the way in produced.
  std::uint64_t activations = 0;
  std::uint64_t deactivations = 0;
  // Nonbasic moves made to break accidental value coincidences.
  std::uint64_t value_separations = 0;
  std::uint64_t normalised_cells = 0;
  std::uint64_t early_conflicts = 0;
  std::uint64_t soi_steps = 0;
  std::uint64_t soi_bound_flips = 0;
  std::uint64_t soi_fallbacks = 0;
};

class ExactSimplexObserver
{
public:
  virtual ~ExactSimplexObserver() = default;
  virtual StopReason pollBeforePivot() noexcept = 0;
  virtual void accountPivot(bool bland) noexcept = 0;
};

/* The exact simplex of the LRA engine: a Dutertre--de Moura tableau
 * (Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)",
 * CAV 2006) over rationals, the same design as the float tier's
 * substitution engine, in the arithmetic that makes every verdict a
 * certificate.
 *
 * Rows are sorted cell vectors cross-linked with column lists; only the
 * rows whose basic variable carries an active bound are kept current
 * ("active") -- they are the rows that can be violated and the rows a
 * conflict is certified from.  A row whose basic variable has no bound
 * (a row variable between assertions, or a structural variable that
 * entered the basis) is dormant: it keeps its last expression, leaves the
 * column lists, and is normalised on demand when a bound arrives or a
 * model is read.  The entering variable is priced by its active holder
 * rows, the violated one by its row length, Bland's rule after as many
 * pivots as there are variables.  Assignments persist across conflicts,
 * as in the float tier: no rollback.
 *
 * The interface is the one the exact core drives: variables and rows,
 * bound assertion with an immediate explanation for a bound clash,
 * checkpoints, check, values and the model's infinitesimal. */
class ExactSimplex final
{
public:
  struct ExplanationTerm
  {
    BoundRef bound;
    ExactRational coefficient;
  };
  using Explanation = std::vector<ExplanationTerm>;

  enum class ResultStatus : std::uint8_t
  {
    Satisfied,
    Unsatisfied,
    Interrupted,
    ResourceLimit
  };
  struct Result
  {
    ResultStatus status;
    Explanation explanation;
  };
  struct RowTerm
  {
    VariableId variable;
    ExactRational coefficient;
  };
  /* One cell of a row: a nonbasic variable, its slot in that variable's
   * column list, and its coefficient. */
  struct Cell final
  {
    std::uint32_t variable;
    std::uint32_t col_position;
    ExactRational coefficient;
  };

  ExactSimplex(CoreGeneration generation, BoundStore& bound_store);

  void initialize();
  void addVariable(VariableId variable);
  void addRow(VariableId variable, std::vector<RowTerm> terms);

  Checkpoint push();
  void pop(Checkpoint checkpoint);

  Explanation assertBound(BoundRef bound);

  Result check(ExactSimplexObserver& observer);
  void setSoi(bool enabled) noexcept { soi_ = enabled; }
  void setEarlyConflictDetection(bool enabled) noexcept
  {
    early_conflicts_ = enabled;
    movement_initialized_ = false;
  }

  /* Move nonbasic variables inside their feasible slack so that fewer of
   * them hold the same value, and report how many moved.
   *
   * Two variables sharing a value by accident are indistinguishable to
   * anything that reads the model by value. The lazy congruence round is
   * one such reader: it groups applications by the model values of their
   * arguments, so a coincidence there manufactures a pair to constrain and
   * a round to state it, for a query that never asked those arguments to be
   * equal. Separating them first removes the pair rather than explaining
   * it.
   *
   * Every move stays inside what the asserted bounds allow, for this
   * variable and for every basic variable of a row it occurs in, so the
   * result is a different model of the same asserted bounds -- and since
   * each assigned atom is an asserted bound, of the same Boolean
   * assignment. Variables whose bounds pin them are skipped: a query that
   * does force two values equal has no slack to give.
   *
   * A no-op when nothing shares a value, and never called on the path to a
   * verdict: an unsatisfiable answer does not depend on which model would
   * have been produced. */
  std::size_t separateCoincidentValues();

  DeltaRational value(VariableId variable) const;
  // Bounded read-only evaluation, including dormant rows. No normalization,
  // activation, or mutation; decline deep/expensive dependency walks.
  std::optional<DeltaRational> decisionValue(VariableId variable) const;
  void values(std::vector<VariableId> const& variables,
              std::vector<DeltaRational>& out) const;
  ExactRational modelInfinitesimal() const;

  std::vector<BoundRef> const& activeBounds() const noexcept
  {
    return active_bounds_;
  }
  ExactSimplexStats const& statistics() const noexcept { return statistics_; }
  bool pivotInProgress() const noexcept { return pivot_in_progress_; }
  bool invariantHolds() const;
  // Reconstruction by ExactLraCore at an unasserted extension boundary.
  // Registered IDs and the BoundStore stay valid; all variables and original
  // rows must be re-added in their original ordinal order before use.
  void clearUnassertedTableau();

private:
  using Ordinal = std::uint32_t;
  static constexpr Ordinal kNone = 0xffffffffu;

  struct Row final
  {
    Ordinal basic;
    std::vector<Cell> cells;
    std::size_t can_raise = 0;
    std::size_t can_lower = 0;
    bool movement_dirty = true;
    bool conflict_queued = false;
  };
  enum class Status : std::uint8_t
  {
    Nonbasic,
    Basic,    // has an active row, in the column lists
    Dormant   // has a row, out of the column lists
  };
  struct Level final
  {
    Checkpoint checkpoint;
    std::size_t active_size;
  };

  Ordinal ordinalOf(VariableId variable, char const* operation) const;
  void registerVariable(VariableId variable, char const* operation);

  bool hasLower(Ordinal v) const noexcept { return lower_ptr_[v] != nullptr; }
  bool hasUpper(Ordinal v) const noexcept { return upper_ptr_[v] != nullptr; }
  DeltaRational const& lowerValue(Ordinal v) const;
  DeltaRational const& upperValue(Ordinal v) const;
  bool outOfLower(Ordinal v) const;
  bool outOfUpper(Ordinal v) const;

  /* Column bookkeeping for active rows. */
  void linkRow(Ordinal row);
  void unlinkRow(Ordinal row);
  void linkCell(Ordinal row, Cell& cell);
  void unlinkCell(Ordinal row, Cell const& cell);
  Cell* findCell(Ordinal row, Ordinal variable);
  Cell const* findCell(Ordinal row, Ordinal variable) const;

  /* Rows over the current nonbasic variables. */
  void normalise(Ordinal row, std::vector<char>& visiting);
  void activate(Ordinal row);
  void deactivate(Ordinal row);
  void substitute(Ordinal row, ExactRational const& scale,
                  std::vector<Cell> const& expression);

  bool safeAdjustInterval(Ordinal variable, DeltaRational& low, bool& has_low,
                          DeltaRational& high, bool& has_high) const;
  bool chooseSeparatedValue(
      Ordinal variable, DeltaRational const& low, bool has_low,
      DeltaRational const& high, bool has_high,
      std::map<DeltaRational, std::vector<Ordinal>> const& holders,
      DeltaRational& target) const;

  void changeNonbasicValue(Ordinal variable, DeltaRational const& target);
  void markViolation(Ordinal row);
  void pivot(Ordinal row, Ordinal entering, DeltaRational const& target);
  bool soiStep(bool& pivoted);
  bool soi_ = false;

  // A bit per direction of nonbasic movement, and counts of cells able
  // to repair each row. Bound/value changes update only holder rows;
  // changed coefficients invalidate only the rows rewritten by a pivot.
  unsigned char movementMask(Ordinal variable) const;
  void refreshMovement(Ordinal variable);
  void queueConflictRow(Ordinal row, bool dirty = false);
  Ordinal earlyConflict();

  Explanation conflictingBounds(Ordinal basic, bool conflict_on_lower) const;
  DeltaRational explanationResidual(Explanation const& explanation) const;
  void generaliseExplanation(Explanation& explanation) const;

  CoreGeneration generation_;
  BoundStore& bound_store_;
  std::vector<Status> status_;
  std::vector<Ordinal> row_of_;
  std::vector<Row> rows_;
  std::vector<std::vector<Ordinal>> cols_;
  std::vector<DeltaRational> value_;
  std::vector<std::vector<BoundRef>> lower_stack_;
  std::vector<std::vector<BoundRef>> upper_stack_;
  /* The value of each stack's top, read straight from the arena's stable
   * storage: the hot loops compare against bounds far more often than
   * bounds change, and the store's validated lookup is not free. */
  std::vector<DeltaRational const*> lower_ptr_;
  std::vector<DeltaRational const*> upper_ptr_;
  std::vector<std::uint32_t> active_bound_count_;
  std::vector<BoundRef> active_bounds_;
  std::vector<Level> levels_;
  std::uint32_t next_checkpoint_token_ = 1;
  std::vector<char> row_violated_;
  std::vector<char> row_queued_;
  std::vector<Ordinal> violated_rows_;
  std::vector<Cell> merge_scratch_;
  mutable std::vector<char> visiting_scratch_;
  mutable ExactSimplexStats statistics_{};
  bool pivot_in_progress_ = false;
  bool early_conflicts_ = false;
  bool movement_initialized_ = false;
  std::vector<unsigned char> movement_;
  std::vector<Ordinal> conflict_rows_;
};

}  // namespace stp::lra

#endif

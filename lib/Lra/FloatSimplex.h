#ifndef STP_LRA_FLOAT_SIMPLEX_H
#define STP_LRA_FLOAT_SIMPLEX_H

#include "ExactLraCore.h"
#include "FloatBasis.h"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace stp::lra
{

/* A double-precision Dutertre--de Moura simplex (Dutertre & de Moura,
 * CAV 2006), the advisory tier of the LRA engine: a floating-point search
 * whose conflicts and models are certified in exact arithmetic
 * (Monniaux, CAV 2009).
 *
 * It mirrors the exact core's shape -- columns, rows over them, atoms as
 * bounds on row variables, assert/undo, a feasibility check -- but every
 * number is a machine double and every verdict is a candidate: Feasible
 * routes the search onward, InfeasibleCandidate asks the caller to re-derive
 * the conflict exactly, and nothing this class computes is ever a
 * certificate.  That contract is what lets the hot path carry no exact
 * rationals, no allocation and no metering: over forty-eight million
 * word-word comparisons across six benchmark families, a double comparison
 * never disagreed in sign with the exact one, so the advisory tier is
 * expected to route correctly essentially always, and the exact tier judges
 * the rare remainder.
 *
 * Two disciplines follow from being advisory rather than authoritative:
 *
 *  - Bound bookkeeping is exact over the stored doubles (lexicographic on
 *    (value, delta), no tolerance): the trail must restore precisely, and a
 *    bound must never be dropped for being within noise of another, because
 *    the trail is also the caller's complete list of what is asserted --
 *    the exact replay reads it.  Every assertAtom call lands on the trail,
 *    even one that tightened nothing.
 *  - Feasibility tests are tolerant (absolute plus relative epsilon):
 *    disagreements with exact arithmetic here cost a wasted exact check or
 *    a delayed conflict, never an answer.
 *
 * Strict bounds carry the DdM infinitesimal as a separate delta component,
 * (value, delta) with delta in {-1, 0, +1} on bounds and accumulated through
 * the same linear updates on assignments.
 *
 * Arithmetic that leaves the finite range poisons the tableau: check()
 * answers Abandoned from then on, while bounds, trail and undo keep working,
 * so the caller degrades to judging complete assignments exactly -- the
 * full-lazy behaviour -- rather than switching drivers mid-search. */
class FloatSimplex final
{
public:
  using Var = std::uint32_t;
  using Atom = std::uint32_t;
  static constexpr Var kNoVar = 0xffffffffu;
  static constexpr Atom kNoAtom = 0xffffffffu;
  static constexpr std::uint32_t kNoRow = 0xffffffffu;

  struct Term final
  {
    Var variable;
    /* Where this row sits in cols_[variable].  Erasing a cell has to
     * find that entry, and searching for it costs the length of the
     * column -- measured at 449 entries, 227 scanned per call, fourteen
     * million calls on one file, a quarter of the run.  The slot fits
     * in the padding the variable already leaves behind, so the cell
     * stays sixteen bytes and the search becomes a subscript.  Callers
     * outside the engine never set it. */
    std::uint32_t col_position;
    double coefficient;

    Term() noexcept = default;
    Term(Var v, double c) noexcept
        : variable(v), col_position(0), coefficient(c)
    {}
    Term(Var v, std::uint32_t position, double c) noexcept
        : variable(v), col_position(position), coefficient(c)
    {}
  };

  /* value + delta * epsilon, the DdM infinitesimal kept symbolic. */
  struct DVal final
  {
    double value = 0.0;
    double delta = 0.0;
    friend bool operator<(DVal a, DVal b) noexcept
    { return a.value < b.value || (a.value == b.value && a.delta < b.delta); }
    friend bool operator==(DVal a, DVal b) noexcept
    { return a.value == b.value && a.delta == b.delta; }
    friend DVal operator+(DVal a, DVal b) noexcept
    { return {a.value + b.value, a.delta + b.delta}; }
    friend DVal operator-(DVal a, DVal b) noexcept
    { return {a.value - b.value, a.delta - b.delta}; }
    friend DVal operator*(DVal a, double b) noexcept
    { return {a.value * b, a.delta * b}; }
    friend DVal operator/(DVal a, double b) noexcept
    { return {a.value / b, a.delta / b}; }
  };

  static constexpr std::uint8_t kSideNone = 0;
  static constexpr std::uint8_t kSideLower = 1;
  static constexpr std::uint8_t kSideUpper = 2;

  /* One assertAtom call.  restored_side says which bound the entry saved
   * (kSideNone when the assert tightened nothing); atom and positive are
   * the caller's replay list either way.  user_tag carries whatever the
   * caller wants to slice the trail by later -- the adapter stores the
   * SAT decision level -- and means nothing here. */
  struct TrailEntry final
  {
    Atom atom;
    bool positive;
    std::uint8_t restored_side;
    Var variable;
    DVal previous_bound;
    bool previously_bounded;
    std::uint32_t user_tag;
    /* The atom (and its asserted polarity) that held the replaced bound,
     * so undo restores the per-bound atom bookkeeping the certificate
     * extraction reads. */
    Atom previous_atom;
    bool previous_atom_positive;
  };

  enum class AssertOutcome : std::uint8_t
  {
    Ok,
    LocalConflict
  };

  enum class Verdict : std::uint8_t
  {
    Feasible,
    InfeasibleCandidate,
    Abandoned
  };

  /* The certificate behind the latest LocalConflict or
   * InfeasibleCandidate: the support atoms with their asserted polarities
   * and float Farkas weights (the violated bound at weight one, each
   * blocking bound at the magnitude of its tableau coefficient).  Doubles
   * are dyadic rationals, so the caller can hand these to the exact tier
   * verbatim; valid is false when any needed bookkeeping was missing. */
  struct CertificateItem final
  {
    Atom atom;
    bool positive;
    double weight;
  };
  struct Certificate final
  {
    bool valid = false;
    std::vector<CertificateItem> items;
  };
  Certificate const& lastCertificate() const noexcept
  {
    return certificate_;
  }
  /* The caller's exact tier refuted the latest InfeasibleCandidate: mute
   * that row until an assert, pivot or update genuinely touches it again,
   * or every poll re-picks the same phantom, re-certifies it and pays the
   * exact refutation forever. */
  void dismissLastConflict() noexcept;

  // After finalize these append to the warm tableau. Appended rows are
  // stated over structural variables; existing IDs/bases are retained.
  Var addColumn();
  Var addRow(const Term* begin, const Term* end);
  Atom addAtom(Var row_variable, Relation positive_relation,
               double threshold);
  /* Close construction: allocate the assignment, remember whether every
   * input converted to a finite double.  False means the instance is
   * unusable and the caller should not route through it at all. */
  bool finalize();
  bool buildUsable() const noexcept { return finalized_ && finite_inputs_; }
  bool poisoned() const noexcept { return poisoned_; }
  // Heuristic only; abstains near the rational boundary, including purely
  // infinitesimal separations. The caller ensures the assignment is fresh.
  std::optional<bool> preferredPolarity(Atom atom) const noexcept;

  std::size_t mark() const noexcept { return trail_.size(); }
  /* The current assignment of one variable, for model refinement:
   * (value, delta) as maintained doubles. */
  /* In the caller's units: the tableau works on equilibrated variables,
   * each the original times a power of two, and hands values back
   * unscaled.  A dormant row's basic is evaluated from its row on the
   * way out (see setDormantRows); everything else reads the maintained
   * value. */
  DVal assignmentOf(Var variable) const noexcept;
  /* Row dormancy, the exact tier's discipline brought to the substitution
   * tableau: a row whose basic variable carries no asserted bound cannot
   * be violated and is not needed for any certificate, so it is kept out
   * of the column lists -- never rewritten by a pivot, never walked by a
   * nonbasic update -- until its first bound arrives.  Activation
   * normalises the row over the current nonbasics (a dormant row's terms
   * were nonbasic when it was last written; those that have since entered
   * the basis are replaced by their rows) and links it.  Rows stay live
   * once activated: the search re-asserts the same atoms after every
   * backtrack, and re-normalising on each undo was measured to cost more
   * than the index it saved.  Substitution mode only; the factorized
   * representation never rewrites rows, so there is nothing to defer.
   * Must be set before finalize(), or on a tableau with an empty trail. */
  void setDormantRows(bool enabled, std::uint32_t min_cells = 0);
  std::uint32_t dormantMinCells() const noexcept { return dormant_min_cells_; }
  bool dormantRows() const noexcept { return dormant_rows_; }
  /* Rows brought into the tableau by a first bound, rows still dormant
   * now, and evaluations served to callers for dormant basics. */
  std::uint64_t rowActivations() const noexcept { return activations_; }
  std::uint64_t dormantRowCount() const noexcept { return dormant_count_; }
  std::uint64_t dormantEvaluations() const noexcept { return dormant_evaluations_; }
  /* One bound the current assignment sits on, within tolerance: the
   * atom holding it and its asserted polarity.  The exact tier turns
   * the set into the equality system a refined model must satisfy. */
  struct PinnedBound final
  {
    Atom atom;
    bool positive;
  };
  /* The tight set of the current assignment.  Misclassification is
   * harmless -- a spurious equation fails the exact solve or the
   * solved model fails verification, a missed one leaves that
   * coordinate to the caller's reconstruction -- so the tolerance
   * tunes only the success rate. */
  void collectPinnedBounds(std::vector<PinnedBound>& out) const;
  void undoTo(std::size_t mark) noexcept;
  AssertOutcome assertAtom(Atom atom, bool positive,
                           std::uint32_t user_tag = 0);
  const std::vector<TrailEntry>& trail() const noexcept { return trail_; }

  /* full_refresh recomputes every basic assignment from its row before
   * judging: the incremental updates the partial checks trust are exact
   * arithmetic in intent and doubles in fact, and a complete candidate
   * model is worth one pass over the tableau to judge on fresh values. */
  Verdict check(ExactLraResourceObserver& observer, bool full_refresh = false);

  /* Reset to the pristine slack basis: original sparse rows, every row
   * variable basic again, bounds and trail untouched, the whole frontier
   * re-marked, poison cleared.  Densification is a property of the pivot
   * history, not of the instance -- a restarted basis re-checks the same
   * bounds along a fresh path, the way a SAT restart re-descends. */
  void restartBasis();

  /* Start the assignment over: every variable back at the origin, the
   * slack basis, row variables recomputed from their rows.  The bounds
   * and the trail are untouched, so the check re-derives the same
   * feasibility question from a point that can still be added up.
   *
   * The infinitesimal coordinate is what forces this.  A double keeps
   * about sixteen digits, so once a row's delta terms reach 1e16 their
   * sum can no longer see a difference of one, and the recomputation
   * the violated scan trusts -- the one that is supposed to stop drift
   * from manufacturing violations -- starts manufacturing them:
   * observed at 2.2e21, where a row whose true delta was two summed to
   * zero and two row variables swapped places for ten thousand pivots.
   * Restarting the basis alone cannot help, because nonbasic
   * assignments deliberately persist across a restart and these are the
   * values at fault. */
  void rebuildAssignment();
  // Experimental reset between solves, separately counted by the caller.
  // It must not consume the numerical-recovery restart/rebuild budgets.
  void resetSearchState(bool basis_only);

  /* Switch to the factorized representation: original rows immutable, the
   * basis held as a sparse LU (FloatBasis) of the full basis of [I | -C]
   * and updated in place at every pivot.  Structural variables carry no
   * bounds, so fill-in has nowhere to live: substitution never happens
   * again.  Starts from the slack basis; bounds and trail are kept. */
  void switchToFactorized();
  bool factorized() const noexcept { return factorized_; }
  /* An assignment component has tripped the infinitesimal cap after the
   * rebuild budget's first rebuild: the substitution tableau's history
   * is what manufactures the blow-up, and a second rebuild only replays
   * it.  The caller should continue in a fresh factorized tier built
   * from this trail (LraSolveContext::promoteFloatCore); every check
   * here is abandoned until it does. */
  bool wantsPromotion() const noexcept { return wants_promotion_; }

  std::uint64_t pivots() const noexcept { return pivots_; }
  void setDenseRecovery(bool enabled) noexcept;
  bool denseInput() const noexcept
  {
    return pristine_nonzeros_ > 64U * static_cast<std::uint64_t>(rows_.size());
  }
  // The pristine (sparse, as-built) nonzero count and the live one. Their
  // ratio is the tableau's fill: healthy incremental solves stay near it, and
  // the cilled blow-up files climb to tens of times it. The reroute detector
  // reads both. liveNonzeros scans the current rows, so callers sample it
  // periodically rather than every check.
  std::uint64_t pristineNonzeros() const noexcept { return pristine_nonzeros_; }
  std::uint64_t liveNonzeros() const noexcept
  {
    std::uint64_t total = 0;
    for (const Row& row : rows_)
      total += row.cells.size();
    return total;
  }
  bool refactorFailed() const noexcept { return refactor_failed_; }
  std::uint64_t refactorFailures() const noexcept { return refactor_failures_; }
  std::uint64_t robustRefactors() const noexcept { return robust_refactors_; }
  std::uint64_t earlyConflicts() const noexcept { return early_conflicts_count_; }
  void setSoi(bool enabled) noexcept { soi_ = enabled; }
  std::uint64_t soiSteps() const noexcept { return soi_steps_; }
  std::uint64_t soiBoundFlips() const noexcept { return soi_bound_flips_; }
  std::uint64_t soiFallbacks() const noexcept { return soi_fallbacks_; }
  void setEarlyConflictDetection(bool enabled) noexcept
  {
    early_conflicts_ = enabled;
    movement_initialized_ = false;
  }
  std::uint64_t restarts() const noexcept { return restarts_; }
  /* How often the assignment had to be started over -- see
   * rebuildAssignment. */
  std::uint64_t assignmentRebuilds() const noexcept { return rebuilds_; }
  /* Certificate terms restated on a weaker asserted bound. */
  std::uint64_t generalisations() const noexcept { return generalisations_; }

private:
  void updateWorkBudgets() noexcept;
  bool dense_recovery_ = false;
  bool refactor_failed_ = false;
  std::uint64_t pristine_nonzeros_ = 0;
  std::uint64_t refactor_failures_ = 0;
  std::uint64_t robust_refactors_ = 0;
  struct Row final
  {
    Var basic = kNoVar;
    std::vector<Term> cells;
    std::size_t can_raise = 0;
    std::size_t can_lower = 0;
    bool movement_dirty = true;
    bool conflict_queued = false;
  };

  struct AtomInfo final
  {
    Var variable;
    Relation relation;
    double threshold;
  };

  double coefficientOf(const Row& row, Var variable) const noexcept;
  /* row += scale * expression, as one merge of two variable-sorted cell
   * lists -- linear in their combined length, where per-term insertion
   * would rescan the fattening row for every term. */
  void addScaledExpression(std::uint32_t row_index, double scale,
                           const std::vector<Term>& expression);
  /* Remove row_index's entry from cols_[variable], given where that
   * entry sits.  The caller always has the cell, so it always has the
   * position. */
  void eraseColumnEntry(Var variable, std::uint32_t position,
                        std::uint32_t row_index) noexcept;
  void addCell(std::uint32_t row_index, Var variable, double coefficient);
  void removeCell(std::uint32_t row_index, Var variable) noexcept;
  void updateNonbasic(Var variable, DVal target) noexcept;
  void noteInfinitesimal(DVal const& value) noexcept;
  bool rebuildBudgetSpent() const noexcept;
  void pivot(std::uint32_t row_index, Var entering);
  void pivotAndUpdate(std::uint32_t row_index, Var entering, DVal target);
  void noteFinite(double candidate) noexcept;
  Var appendRow(const Term* begin, const Term* end);
  unsigned char movementMask(Var variable) const noexcept;
  void refreshMovement(Var variable) noexcept;
  void queueConflictRow(std::uint32_t row, bool dirty = false) noexcept;
  std::uint32_t earlyConflict();
  bool soiStep(bool& pivoted);
  bool soi_ = false;
  std::uint64_t soi_steps_ = 0;
  std::uint64_t soi_bound_flips_ = 0;
  std::uint64_t soi_fallbacks_ = 0;
  bool early_conflicts_ = false;
  bool movement_initialized_ = false;
  std::uint64_t early_conflicts_count_ = 0;
  std::vector<unsigned char> movement_;
  std::vector<std::uint32_t> conflict_rows_;

  std::vector<Row> rows_;
  std::vector<std::uint32_t> row_of_basic_;
  /* Exact column index: cols_[v] lists precisely the rows whose cells
   * mention v.  Maintained through every cell insertion and removal, so
   * walks need no validation and can never see a row twice. */
  std::vector<std::vector<std::uint32_t>> cols_;
  std::vector<DVal> alpha_;
  /* Row scaling: variable v of the tableau is scale_[v] times the
   * caller's, scale_[v] a power of two (one for a structural), chosen so
   * that every row's largest coefficient sits in [1, 2) whatever the
   * instance's units.  Thresholds are scaled on the way in and
   * certificate weights on the way out; nothing else notices. */
  std::vector<double> scale_;
  void equilibrate();
  double scaleOf(Var variable) const noexcept
  {
    return scale_.empty() ? 1.0 : scale_[variable];
  }
  std::vector<DVal> lower_;
  std::vector<DVal> upper_;
  std::vector<char> has_lower_;
  std::vector<char> has_upper_;
  /* Which atom, at which asserted polarity, holds each current bound --
   * the certificate extraction's source of truth. */
  std::vector<Atom> lower_atom_;
  std::vector<Atom> upper_atom_;
  std::vector<char> lower_positive_;
  std::vector<char> upper_positive_;
  Certificate certificate_;
  /* Every asserted bound per variable and side, in assertion order --
   * not only the tightest.  The certificate is generalised over them:
   * restated on the weakest asserted bound of each support variable
   * that still contradicts, the exact tier's explanation
   * generalisation, so the clause handed back rules out more. */
  struct AssertedBound final
  {
    Atom atom;
    bool positive;
    DVal bound;
  };
  std::vector<std::vector<AssertedBound>> lower_asserted_;
  std::vector<std::vector<AssertedBound>> upper_asserted_;
  struct SupportTerm final
  {
    Atom atom;
    bool positive;
    double weight;
    Var variable;
    bool upper;
    DVal bound;
  };
  std::vector<SupportTerm> support_scratch_;
  /* Weaken each support term to the weakest asserted bound that keeps
   * the Farkas combination negative, then emit the certificate. */
  void emitCertificate();
  std::vector<AtomInfo> atoms_;
  std::vector<TrailEntry> trail_;
  /* The check's incremental frontier: rows whose basic assignment or
   * structure changed since they were last verified in bounds.  check()
   * drains it instead of scanning every row per call, and it persists
   * across checks -- the point of keeping the tableau warm. */
  std::vector<std::uint32_t> touched_rows_;
  std::vector<char> row_touched_;
  std::vector<Term> merge_scratch_;
  /* The violated set, maintained where basic assignments change: every
   * update of a basic variable's value (a nonbasic moving onto a bound,
   * a pivot step) and every bound tightened on a basic variable re-judges
   * that one row, so a check never rescans the tableau -- it reads the
   * set.  row_violated_ is the truth per row; row_queued_ says the row is
   * on the list, which tolerates stale entries and is compacted by the
   * picks.  Substitution mode indexes by tableau row, factorized mode by
   * pristine row (the two share the index space), and a row is
   * recomputed fresh from its cells before it is pivoted on or explained
   * from, so accumulated drift cannot manufacture a conflict. */
  std::vector<std::uint32_t> violated_rows_;
  std::vector<char> row_violated_;
  std::vector<char> row_queued_;
  /* Dormancy: per row, whether it is out of the column lists; per row, a
   * visiting mark for the normalisation's cycle guard (the references
   * form a DAG by construction, so a cycle is a broken invariant, and the
   * advisory tier poisons rather than throws). */
  bool dormant_rows_ = false;
  /* Rows narrower than this stay live: cheap to keep, pointless to defer. */
  std::uint32_t dormant_min_cells_ = 0;
  std::vector<char> row_dormant_;
  std::vector<char> row_visiting_;
  std::uint64_t activations_ = 0;
  std::uint64_t dormant_count_ = 0;
  mutable std::uint64_t dormant_evaluations_ = 0;
  bool boundedVariable(Var variable) const noexcept
  {
    return !lower_asserted_[variable].empty() ||
           !upper_asserted_[variable].empty();
  }
  /* Take every row out of the column lists that has no bounded basic;
   * rows already over nonbasics need no normalisation (finalize and
   * restartBasis both leave them so). */
  void dormantUnboundedRows() noexcept;
  void unlinkRow(std::uint32_t row_index) noexcept;
  void linkRow(std::uint32_t row_index) noexcept;
  /* Rewrite a dormant row over the current nonbasics, recursing into
   * dormant rows it refers to.  Sets poisoned_ on a cycle. */
  void normaliseDormantRow(std::uint32_t row_index);
  /* First bound on a dormant row's basic: normalise, recompute the basic
   * from the row, link, and judge. */
  void activateRow(std::uint32_t row_index);
  /* Read-only, bounded evaluation of a dormant basic from its row, for
   * callers that read the assignment without asserting anything;
   * falls back to the stale maintained value past the budget. */
  DVal evaluateVariable(Var variable, unsigned depth,
                        std::size_t& work) const noexcept;
  /* Basic updates since the last full recomputation.  Incremental
   * updates drift by rounding, and past this budget every basic is
   * recomputed from its row so a stale value cannot hide a violation
   * for a whole solve. */
  std::uint64_t refresh_debt_ = 0;
  void markViolation(std::uint32_t row_index, Var basic) noexcept;
  /* Recompute one basic assignment from its row (tableau or pristine)
   * and re-judge it; false when the sum left the finite range. */
  bool recomputeRow(std::uint32_t row_index, bool pristine) noexcept;
  void refreshAllRows() noexcept;
  bool refreshDue() const noexcept;
  std::uint32_t last_conflict_row_ = kNoRow;
  /* The slack-basis rows as built, for restarts and as the factorized
   * mode's immutable coefficient matrix. */
  std::vector<Row> pristine_rows_;
  std::uint64_t restarts_ = 0;
  bool wants_promotion_ = false;

  /* Factorized-mode state: the basis of [I | -C] as a header (position
   * -> basic variable) and its sparse LU with product-form updates.
   * Every pivot is a column replacement recorded as an eta, and the
   * factor is rebuilt from the header when the eta file is due or an
   * update is refused.  FTRAN of the entering column gives the direction
   * per basic variable; BTRAN of the violated variable's position gives
   * its tableau row, -(rho^T a_q) per nonbasic q. */
  bool factorized_ = false;
  std::vector<char> variable_basic_;
  FloatBasis basis_;
  std::vector<Var> basis_header_;
  std::vector<std::int32_t> basis_position_;
  std::vector<std::vector<FloatBasis::Entry>> basis_columns_;
  /* Dense scratch by position for the solves, zero outside its touched
   * list; the direction by position stays here after factorizedDirection
   * for the eta the pivot records. */
  std::vector<double> basis_scratch_;
  std::vector<FloatBasis::Index> basis_scratch_touched_;
  std::vector<double> basis_row_;
  std::vector<FloatBasis::Index> basis_row_touched_;
  bool basis_stale_ = true;
  std::vector<Term> row_coefficients_;
  /* The shortest-conflict-row search's yield: conflicts examined and
   * conflicts where it found a shorter row, both decayed. */
  std::uint64_t shortest_examined_ = 0;
  std::uint64_t shortest_improved_ = 0;
  /* Pristine column index: structural variable -> (row, coefficient). */
  std::vector<std::vector<Term>> pristine_cols_;
  /* Row index of each row variable; kNoRow for structural variables. */
  std::vector<std::uint32_t> row_index_of_rowvar_;

  bool factorizedRefactor();
  /* FTRAN of `variable`'s column into basis coordinates: fills the dense
   * per-basic direction (value component only; the delta component of a
   * column direction is zero, deltas ride the moved amounts) and leaves
   * the same direction by position in basis_scratch_ for the eta.  False
   * on a refused solve. */
  bool factorizedDirection(Var variable);
  void factorizedUpdateNonbasic(Var variable, DVal target);
  Verdict factorizedCheck(ExactLraResourceObserver& observer);
  /* Dense FTRAN direction, indexed by variable; direction_touched_ lists
   * the nonzero slots for cheap clearing. */
  std::vector<double> direction_;
  std::vector<Var> direction_touched_;
  /* Dense scratch for the BTRAN row's structural coefficients. */
  std::vector<double> gather_;
  std::vector<Var> gather_touched_;
  /* Factorized-mode phantom dismissal: skip this variable in the violated
   * scan while its assignment and bounds are exactly what they were when
   * the exact tier refuted it. */
  Var factorized_dismissed_ = kNoVar;
  DVal dismissed_alpha_{0.0, 0.0};
  DVal dismissed_lower_{0.0, 0.0};
  DVal dismissed_upper_{0.0, 0.0};
  Var factorized_last_violated_ = kNoVar;
  std::uint64_t pivots_ = 0;
  std::uint64_t generalisations_ = 0;
  /* Per-check pivot cap: cycling insurance for tolerant Bland.  Past it
   * the check abandons, and the caller learning nothing is always safe. */
  std::uint64_t check_pivot_cap_ = 0;
  /* Per-check substitution budget, in merged cells.  A family whose
   * tableau densifies under pivoting -- where even fill-in-aware pricing
   * leaves every pivot rewriting thousands of cells -- is not worth the
   * advisory tier's time: past the budget the check abandons and the
   * search degrades to judging complete assignments exactly, instead of
   * drowning in merges. */
  std::uint64_t check_merge_cells_ = 0;
  std::uint64_t check_merge_cap_ = 0;
  bool finalized_ = false;
  bool finite_inputs_ = true;
  bool poisoned_ = false;
  /* Set when an assignment component grows past what a double can add
   * up meaningfully; the next check rebuilds before it looks at
   * anything. */
  bool assignment_unusable_ = false;
  std::uint64_t rebuilds_ = 0;
};

}  // namespace stp::lra

#endif

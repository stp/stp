#ifndef STP_LRA_EXACT_LRA_REGISTRATION_H
#define STP_LRA_EXACT_LRA_REGISTRATION_H

#include "ExactLraVerificationData.h"
#include "Storage/DenseMembership.h"
#include "Storage/LraIds.h"

#include <cstddef>
#include <optional>
#include <vector>

namespace stp::lra {

using RegisteredBoundKind = ExactLraVerificationBoundKind;

struct RegisteredRow
{
  RowId id;
  // For a direct singleton this is its base variable; otherwise a fresh
  // auxiliary. The original row remains in the independent verifier snapshot.
  // Singletons are direct only under --lra-direct-bounds, which asserts a
  // bound on a single variable on that variable rather than on a slack, as
  // in Dutertre & de Moura, CAV 2006; by default a singleton row gets a fresh
  // auxiliary too.
  VariableId auxiliary;
  std::optional<ExactRational> direct_coefficient;
};

using RegisteredAtom = ExactLraVerificationAtom;
using RegisteredBound = ExactLraVerificationBound;

class ExactLraRegistration final
{
 public:
  explicit ExactLraRegistration(CoreGeneration);
  ~ExactLraRegistration() noexcept = default;
  ExactLraRegistration(ExactLraRegistration const&) = delete;
  ExactLraRegistration& operator=(ExactLraRegistration const&) = delete;
  ExactLraRegistration(ExactLraRegistration&&) = delete;
  ExactLraRegistration& operator=(ExactLraRegistration&&) = delete;

  void addBaseVariable(VariableId);
  RowId addRow(VariableId auxiliary, std::vector<LinearTerm> terms,
               bool direct = false);
  AtomId allocateAtom();
  void addAtom(RegisteredAtom atom);
  void addBound(RegisteredBound bound);

  void push(Checkpoint checkpoint);
  void activate(BoundRef reference);
  void setPendingConflictBound(BoundRef reference);
  void clearPendingConflictBound() noexcept;
  void pop(Checkpoint checkpoint);

  bool containsBaseVariable(VariableId) const noexcept;
  bool containsRow(RowId) const noexcept;
  bool containsAtom(AtomId) const noexcept;
  bool containsBound(BoundRef) const noexcept;
  bool containsCheckpoint(Checkpoint) const noexcept;
  bool isActive(BoundRef) const noexcept;
  std::optional<bool> activePolarity(AtomId) const noexcept;

  RegisteredRow const& row(RowId) const;
  RegisteredAtom const& atom(AtomId) const;
  RegisteredBound const& bound(BoundRef) const;

  std::vector<VariableId> const& baseVariables() const noexcept;
  std::vector<RegisteredRow> const& rows() const noexcept;
  std::vector<ExactLraVerificationRow> const& verificationRows() const
      noexcept;
  std::vector<RegisteredAtom> const& atoms() const noexcept;
  std::vector<RegisteredBound> const& bounds() const noexcept;
  std::vector<BoundRef> const& activeBounds() const noexcept;
  std::optional<BoundRef> pendingConflictBound() const noexcept;
  std::size_t levelCount() const noexcept;
  ExactLraVerificationDataView verificationData(
      WitnessTag current_tag) const noexcept;

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  ExactLraVerificationRow& testMutableRow(RowId);
  RegisteredBound& testMutableBound(BoundRef);
#endif

 private:
  struct Level
  {
    Checkpoint checkpoint;
    std::size_t active_size;
  };

  std::vector<Level>::const_iterator findLevel(Checkpoint) const;

  CoreGeneration generation_;
  MonotonicIdAllocator<RowId> row_ids_;
  MonotonicIdAllocator<AtomId> atom_ids_;
  std::vector<VariableId> base_variables_;
  std::vector<RegisteredRow> rows_;
  std::vector<ExactLraVerificationRow> verification_rows_;
  std::vector<RegisteredAtom> atoms_;
  std::vector<RegisteredBound> bounds_;
  std::vector<BoundRef> active_bounds_;
  /* Which bounds are in active_bounds_, by ordinal.  Kept beside the vector
   * rather than derived from it because the duplicate check runs on every
   * assertion, and scanning the vector made asserting a candidate cost the
   * square of its size. Identity is still decided by containsBound; this only
   * answers membership. */
  DenseMembership active_membership_;
  std::vector<Level> levels_;
  std::optional<BoundRef> pending_conflict_bound_;
};

}  // namespace stp::lra

#endif

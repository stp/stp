#include "ExactLraRegistration.h"
#include "Storage/Growth.h"

#include "Storage/CheckedConversions.h"
#include "Storage/StorageFailure.h"

#include <algorithm>
#include <iterator>
#include <new>
#include <stdexcept>
#include <utility>

namespace stp::lra {

namespace {

[[noreturn]] void invalid(char const* operation, char const* detail)
{
  throw StorageFailure(StorageFailureKind::InvariantViolation, operation,
                       detail);
}

}  // namespace

ExactLraRegistration::ExactLraRegistration(CoreGeneration generation)
    : generation_(generation), row_ids_(generation), atom_ids_(generation)
{
  if (!generation.valid())
  {
    throw StorageFailure(StorageFailureKind::InvalidGeneration,
                         "ExactLraRegistration", "invalid generation");
  }
}

void ExactLraRegistration::addBaseVariable(VariableId variable)
{
  if (variable.generation() != generation_ ||
      (!base_variables_.empty() && !(base_variables_.back() < variable)))
  {
    invalid("ExactLraRegistration::addBaseVariable",
            "foreign or nonmonotonic base variable");
  }
  try
  {
    base_variables_.push_back(variable);
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::addBaseVariable",
                         "base-variable snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::addBaseVariable",
                         "base-variable snapshot length limit");
  }
}

RowId ExactLraRegistration::addRow(VariableId auxiliary,
                                   std::vector<LinearTerm> terms, bool direct)
{
  if (auxiliary.generation() != generation_ || terms.empty())
  {
    invalid("ExactLraRegistration::addRow",
            "foreign auxiliary or empty canonical row");
  }
  RowId const id = row_ids_.allocate();
  try
  {
    RegisteredRow row{id, auxiliary, std::nullopt};
    if (direct)
    {
      if (terms.size() != 1 || terms.front().variable != auxiliary ||
          terms.front().coefficient.isZero() || !containsBaseVariable(auxiliary))
        invalid("ExactLraRegistration::addRow", "invalid direct singleton");
      row.direct_coefficient = terms.front().coefficient;
    }
    rows_.push_back(std::move(row));
    verification_rows_.push_back(
        ExactLraVerificationRow{id, std::move(terms)});
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::addRow",
                         "row snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::addRow",
                         "row snapshot length limit");
  }
  return id;
}

AtomId ExactLraRegistration::allocateAtom()
{
  return atom_ids_.allocate();
}

void ExactLraRegistration::addAtom(RegisteredAtom atom_record)
{
  if (atom_record.id.generation() != generation_ ||
      atom_record.id.ordinal() != atoms_.size() ||
      atom_record.row.generation() != generation_ ||
      atom_record.positive_bound.generation() != generation_ ||
      atom_record.negative_bound.generation() != generation_)
  {
    invalid("ExactLraRegistration::addAtom", "noncanonical atom snapshot");
  }
  try
  {
    atoms_.push_back(std::move(atom_record));
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::addAtom",
                         "atom snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::addAtom",
                         "atom snapshot length limit");
  }
}

void ExactLraRegistration::addBound(RegisteredBound bound_record)
{
  if (bound_record.reference.generation() != generation_ ||
      bound_record.reference.ordinal() != bounds_.size() ||
      bound_record.row.generation() != generation_ ||
      bound_record.atom.generation() != generation_)
  {
    invalid("ExactLraRegistration::addBound",
            "noncanonical bound snapshot");
  }
  try
  {
    // Grow the membership first: after this, marking a bound active cannot
    // fail, so activate() cannot leave the two disagreeing.
    active_membership_.ensureSize(bounds_.size() + 1U);
    bounds_.push_back(std::move(bound_record));
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::addBound",
                         "bound snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::addBound",
                         "bound snapshot length limit");
  }
}

void ExactLraRegistration::push(Checkpoint checkpoint)
{
  if (checkpoint.generation != generation_ || checkpoint.depth == 0)
  {
    throw StorageFailure(StorageFailureKind::InvalidCheckpoint,
                         "ExactLraRegistration::push",
                         "foreign or zero checkpoint");
  }
  try
  {
    detail::reserveForOneMore(levels_);
    levels_.push_back(Level{checkpoint, active_bounds_.size()});
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::push",
                         "checkpoint snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::push",
                         "checkpoint snapshot length limit");
  }
}

void ExactLraRegistration::activate(BoundRef reference)
{
  if (!containsBound(reference) || isActive(reference))
  {
    invalid("ExactLraRegistration::activate",
            "unknown or duplicate active bound");
  }
  try
  {
    active_bounds_.push_back(reference);
    active_membership_.setChecked(reference.ordinal(), true);
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "ExactLraRegistration::activate",
                         "active snapshot allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "ExactLraRegistration::activate",
                         "active snapshot length limit");
  }
}

void ExactLraRegistration::setPendingConflictBound(BoundRef reference)
{
  if (!containsBound(reference) || isActive(reference))
  {
    invalid("ExactLraRegistration::setPendingConflictBound",
            "unknown or already-active pending bound");
  }
  pending_conflict_bound_ = reference;
}

void ExactLraRegistration::clearPendingConflictBound() noexcept
{
  pending_conflict_bound_.reset();
}

std::vector<ExactLraRegistration::Level>::const_iterator
ExactLraRegistration::findLevel(Checkpoint checkpoint) const
{
  // From the top: a pop is almost always to the level just below it.
  auto const found = std::find_if(levels_.rbegin(), levels_.rend(),
                                  [checkpoint](Level const& level) {
                                    return level.checkpoint == checkpoint;
                                  });
  return found == levels_.rend() ? levels_.end() : std::next(found).base();
}

void ExactLraRegistration::pop(Checkpoint checkpoint)
{
  auto const found = findLevel(checkpoint);
  if (checkpoint.generation != generation_ || found == levels_.end())
  {
    throw StorageFailure(StorageFailureKind::InvalidCheckpoint,
                         "ExactLraRegistration::pop",
                         "checkpoint is stale or foreign");
  }
  std::size_t const index = checkedDifferenceToSize(
      found - levels_.begin(), "ExactLraRegistration::pop");
  for (std::size_t offset = found->active_size;
       offset != active_bounds_.size(); ++offset)
  {
    active_membership_.setChecked(active_bounds_[offset].ordinal(), false);
  }
  active_bounds_.erase(
      active_bounds_.begin() +
          static_cast<std::ptrdiff_t>(found->active_size),
      active_bounds_.end());
  levels_.resize(index);
  pending_conflict_bound_.reset();
}

bool ExactLraRegistration::containsBaseVariable(VariableId variable) const
    noexcept
{
  return variable.generation() == generation_ &&
         std::binary_search(base_variables_.begin(), base_variables_.end(),
                            variable);
}

bool ExactLraRegistration::containsRow(RowId id) const noexcept
{
  return id.generation() == generation_ && id.ordinal() < rows_.size() &&
         id.ordinal() < verification_rows_.size() &&
         rows_[id.ordinal()].id == id &&
         verification_rows_[id.ordinal()].id == id;
}

bool ExactLraRegistration::containsAtom(AtomId id) const noexcept
{
  return id.generation() == generation_ && id.ordinal() < atoms_.size() &&
         atoms_[id.ordinal()].id == id;
}

bool ExactLraRegistration::containsBound(BoundRef reference) const noexcept
{
  return reference.generation() == generation_ &&
         reference.ordinal() < bounds_.size() &&
         bounds_[reference.ordinal()].reference == reference;
}

bool ExactLraRegistration::containsCheckpoint(Checkpoint checkpoint) const
    noexcept
{
  return checkpoint.generation == generation_ &&
         findLevel(checkpoint) != levels_.end();
}

bool ExactLraRegistration::isActive(BoundRef reference) const noexcept
{
  if (containsBound(reference) &&
      active_membership_.test(reference.ordinal()))
  {
    return true;
  }
  return pending_conflict_bound_ && *pending_conflict_bound_ == reference;
}

std::optional<bool> ExactLraRegistration::activePolarity(AtomId id) const
    noexcept
{
  if (!containsAtom(id))
  {
    return std::nullopt;
  }
  RegisteredAtom const& record = atoms_[id.ordinal()];
  if (isActive(record.positive_bound))
  {
    return true;
  }
  if (isActive(record.negative_bound))
  {
    return false;
  }
  return std::nullopt;
}

RegisteredRow const& ExactLraRegistration::row(RowId id) const
{
  if (!containsRow(id))
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                         "ExactLraRegistration::row", "unknown row");
  }
  return rows_[id.ordinal()];
}

RegisteredAtom const& ExactLraRegistration::atom(AtomId id) const
{
  if (!containsAtom(id))
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                         "ExactLraRegistration::atom", "unknown atom");
  }
  return atoms_[id.ordinal()];
}

RegisteredBound const& ExactLraRegistration::bound(BoundRef reference) const
{
  if (!containsBound(reference))
  {
    throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                         "ExactLraRegistration::bound", "unknown bound");
  }
  return bounds_[reference.ordinal()];
}

std::vector<VariableId> const& ExactLraRegistration::baseVariables() const
    noexcept
{
  return base_variables_;
}

std::vector<RegisteredRow> const& ExactLraRegistration::rows() const noexcept
{
  return rows_;
}

std::vector<ExactLraVerificationRow> const&
ExactLraRegistration::verificationRows() const noexcept
{
  return verification_rows_;
}

std::vector<RegisteredAtom> const& ExactLraRegistration::atoms() const noexcept
{
  return atoms_;
}

std::vector<RegisteredBound> const& ExactLraRegistration::bounds() const
    noexcept
{
  return bounds_;
}

std::vector<BoundRef> const& ExactLraRegistration::activeBounds() const
    noexcept
{
  return active_bounds_;
}

std::optional<BoundRef> ExactLraRegistration::pendingConflictBound() const
    noexcept
{
  return pending_conflict_bound_;
}

std::size_t ExactLraRegistration::levelCount() const noexcept
{
  return levels_.size();
}

ExactLraVerificationDataView ExactLraRegistration::verificationData(
    WitnessTag current_tag) const noexcept
{
  return ExactLraVerificationDataView{
      current_tag, base_variables_, verification_rows_, atoms_, bounds_,
      active_bounds_, pending_conflict_bound_};
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
ExactLraVerificationRow& ExactLraRegistration::testMutableRow(RowId id)
{
  if (!containsRow(id))
  {
    invalid("ExactLraRegistration::testMutableRow", "unknown row");
  }
  return verification_rows_[id.ordinal()];
}

RegisteredBound& ExactLraRegistration::testMutableBound(BoundRef reference)
{
  if (!containsBound(reference))
  {
    invalid("ExactLraRegistration::testMutableBound", "unknown bound");
  }
  return bounds_[reference.ordinal()];
}
#endif

}  // namespace stp::lra

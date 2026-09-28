#include "ExactLraVerificationData.h"
#include "ExactLraActiveBounds.h"

#include "Storage/StorageFailure.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <new>
#include <stdexcept>
#include <utility>
#include <vector>

namespace stp::lra {
namespace {

bool sameTag(WitnessTag const& lhs, WitnessTag const& rhs) noexcept
{
  return lhs.generation == rhs.generation &&
         lhs.state_revision == rhs.state_revision;
}

bool relationValid(Relation relation) noexcept
{
  switch (relation)
  {
    case Relation::Less:
    case Relation::LessEqual:
    case Relation::Greater:
    case Relation::GreaterEqual: return true;
  }
  return false;
}

ExactLraVerificationRow const* findRow(
    ExactLraVerificationDataView const& data,
    RowId id) noexcept
{
  if (id.generation() != data.current_tag.generation ||
      id.ordinal() >= data.rows.size())
  {
    return nullptr;
  }
  ExactLraVerificationRow const& row = data.rows[id.ordinal()];
  return row.id == id ? &row : nullptr;
}

ExactLraVerificationBound const* findBound(
    ExactLraVerificationDataView const& data,
    BoundRef reference) noexcept
{
  if (reference.generation() != data.current_tag.generation ||
      reference.ordinal() >= data.bounds.size())
  {
    return nullptr;
  }
  ExactLraVerificationBound const& bound =
      data.bounds[reference.ordinal()];
  return bound.reference == reference ? &bound : nullptr;
}

ExactLraVerificationAtom const* findAtom(
    ExactLraVerificationDataView const& data,
    AtomId id) noexcept
{
  if (id.generation() != data.current_tag.generation ||
      id.ordinal() >= data.atoms.size())
  {
    return nullptr;
  }
  ExactLraVerificationAtom const& atom = data.atoms[id.ordinal()];
  return atom.id == id ? &atom : nullptr;
}

struct ExpectedPair final
{
  ExactLraVerificationBoundKind positive_kind;
  std::int64_t positive_delta;
  ExactLraVerificationBoundKind negative_kind;
  std::int64_t negative_delta;
};

ExpectedPair expectedPair(Relation relation)
{
  switch (relation)
  {
    case Relation::Less:
      return ExpectedPair{ExactLraVerificationBoundKind::Upper, -1,
                          ExactLraVerificationBoundKind::Lower, 0};
    case Relation::LessEqual:
      return ExpectedPair{ExactLraVerificationBoundKind::Upper, 0,
                          ExactLraVerificationBoundKind::Lower, 1};
    case Relation::Greater:
      return ExpectedPair{ExactLraVerificationBoundKind::Lower, 1,
                          ExactLraVerificationBoundKind::Upper, 0};
    case Relation::GreaterEqual:
      return ExpectedPair{ExactLraVerificationBoundKind::Lower, 0,
                          ExactLraVerificationBoundKind::Upper, -1};
  }
  throw std::logic_error("invalid verification relation");
}

bool boundDescriptorMatches(ExactLraVerificationBound const& bound,
                            ExactLraVerificationAtom const& atom,
                            bool positive,
                            ExactLraVerificationBoundKind kind,
                            std::int64_t delta)
{
  ExactRational const expected_delta(delta);
  OriginId const expected_origin =
      positive ? atom.positive_origin : atom.negative_origin;
  BoundRef const expected_reference =
      positive ? atom.positive_bound : atom.negative_bound;
  return bound.reference == expected_reference && bound.row == atom.row &&
         bound.kind == kind && bound.threshold == atom.threshold &&
         bound.infinitesimal == expected_delta &&
         bound.origin == expected_origin && bound.atom == atom.id &&
         bound.positive_component == positive;
}

bool snapshotValid(ExactLraVerificationDataView const& data,
                    ExactLraActiveBounds& active)
{
  if (!data.current_tag.generation.valid() ||
      data.current_tag.state_revision == 0)
  {
    return false;
  }

  for (std::size_t index = 0; index != data.base_variables.size(); ++index)
  {
    VariableId const variable = data.base_variables[index];
    if (variable.generation() != data.current_tag.generation ||
        (index != 0 && !(data.base_variables[index - 1U] < variable)))
    {
      return false;
    }
  }

  for (std::size_t index = 0; index != data.rows.size(); ++index)
  {
    ExactLraVerificationRow const& row = data.rows[index];
    if (row.id.generation() != data.current_tag.generation ||
        row.id.ordinal() != index || row.terms.empty())
    {
      return false;
    }
    for (std::size_t term_index = 0; term_index != row.terms.size();
         ++term_index)
    {
      LinearTerm const& term = row.terms[term_index];
      if (!term.coefficient.invariantHolds() || term.coefficient.isZero() ||
          !std::binary_search(data.base_variables.begin(),
                              data.base_variables.end(), term.variable) ||
          (term_index != 0 &&
           !(row.terms[term_index - 1U].variable < term.variable)))
      {
        return false;
      }
    }
  }

  for (std::size_t index = 0; index != data.bounds.size(); ++index)
  {
    ExactLraVerificationBound const& bound = data.bounds[index];
    if (bound.reference.generation() != data.current_tag.generation ||
        bound.reference.ordinal() != index || findRow(data, bound.row) == nullptr ||
        !bound.threshold.invariantHolds() ||
        !bound.infinitesimal.invariantHolds())
    {
      return false;
    }
    switch (bound.kind)
    {
      case ExactLraVerificationBoundKind::Lower:
      case ExactLraVerificationBoundKind::Upper: break;
      default: return false;
    }
  }

  for (std::size_t index = 0; index != data.atoms.size(); ++index)
  {
    ExactLraVerificationAtom const& atom = data.atoms[index];
    if (atom.id.generation() != data.current_tag.generation ||
        atom.id.ordinal() != index || findRow(data, atom.row) == nullptr ||
        !relationValid(atom.positive_relation) ||
        !atom.threshold.invariantHolds() ||
        atom.positive_bound == atom.negative_bound)
    {
      return false;
    }
    ExactLraVerificationBound const* const positive =
        findBound(data, atom.positive_bound);
    ExactLraVerificationBound const* const negative =
        findBound(data, atom.negative_bound);
    if (positive == nullptr || negative == nullptr)
    {
      return false;
    }
    ExpectedPair const expected = expectedPair(atom.positive_relation);
    if (!boundDescriptorMatches(*positive, atom, true,
                                expected.positive_kind,
                                expected.positive_delta) ||
        !boundDescriptorMatches(*negative, atom, false,
                                expected.negative_kind,
                                expected.negative_delta))
    {
      return false;
    }
  }

  for (ExactLraVerificationBound const& bound : data.bounds)
  {
    ExactLraVerificationAtom const* const atom = findAtom(data, bound.atom);
    if (atom == nullptr)
    {
      return false;
    }
    ExpectedPair const expected = expectedPair(atom->positive_relation);
    bool const positive = bound.positive_component;
    if (!boundDescriptorMatches(
            bound, *atom, positive,
            positive ? expected.positive_kind : expected.negative_kind,
            positive ? expected.positive_delta : expected.negative_delta))
    {
      return false;
    }
  }

  return active.build(data);
}

std::size_t baseIndex(ExactLraVerificationDataView const& data,
                      VariableId variable)
{
  auto const found = std::lower_bound(data.base_variables.begin(),
                                      data.base_variables.end(), variable);
  if (found == data.base_variables.end() || *found != variable)
  {
    throw std::logic_error("verification row references an unknown base");
  }
  return static_cast<std::size_t>(found - data.base_variables.begin());
}

VerificationResult mappedFailure(NumberFailure const& failure) noexcept
{
  return VerificationResult{
      failure.kind() == NumberFailureKind::ResourceLimit
          ? VerificationError::ResourceLimit
          : VerificationError::InternalError};
}

VerificationResult mappedFailure(StorageFailure const& failure) noexcept
{
  return VerificationResult{
      failure.kind() == StorageFailureKind::ResourceLimit
          ? VerificationError::ResourceLimit
          : VerificationError::InternalError};
}

}  // namespace

static VerificationResult verifyExactLraConflictImpl(
    ExactLraVerificationDataView const& data,
    Conflict const& conflict, bool require_active, bool audit_snapshot)
{
  if (!sameTag(conflict.tag, data.current_tag))
  {
    return VerificationResult{VerificationError::StaleId};
  }
  try
  {
    ExactLraActiveBounds active;
    if (audit_snapshot && !snapshotValid(data, active))
    {
      return VerificationResult{VerificationError::InternalError};
    }
    if (conflict.terms.empty())
    {
      return VerificationResult{VerificationError::NotContradictory};
    }

    std::vector<ExactRational> coefficients;
    coefficients.reserve(data.base_variables.size());
    for (std::size_t index = 0; index != data.base_variables.size(); ++index)
    {
      coefficients.emplace_back(std::int64_t{0});
    }
    /* Cancellation can only fail where the combination reached; the
     * final scan walks the touched slots instead of every base
     * variable. */
    std::vector<char> touched_flags(data.base_variables.size(), 0);
    std::vector<std::size_t> touched;
    ExactRational right_main(std::int64_t{0});
    ExactRational right_infinitesimal(std::int64_t{0});

    for (std::size_t index = 0; index != conflict.terms.size(); ++index)
    {
      ConflictTerm const& term = conflict.terms[index];
      if (index != 0 && !(conflict.terms[index - 1U].bound < term.bound))
      {
        return VerificationResult{VerificationError::DuplicateEntry};
      }
      ExactLraVerificationBound const* const bound =
          findBound(data, term.bound);
      if (bound == nullptr)
      {
        return VerificationResult{VerificationError::StaleId};
      }
      if (!(term.origin == bound->origin))
      {
        return VerificationResult{VerificationError::OriginMismatch};
      }
      if (require_active && !active.contains(term.bound))
      {
        return VerificationResult{VerificationError::InactiveSupport};
      }
      if (!term.weight.invariantHolds() || term.weight.sign() <= 0)
      {
        return VerificationResult{VerificationError::InvalidWeight};
      }

      ExactLraVerificationRow const* const row = findRow(data, bound->row);
      if (row == nullptr)
      {
        return VerificationResult{VerificationError::InternalError};
      }
      bool const lower =
          bound->kind == ExactLraVerificationBoundKind::Lower;
      for (LinearTerm const& row_term : row->terms)
      {
        ExactRational contribution = row_term.coefficient * term.weight;
        if (lower)
        {
          contribution.negate();
        }
        std::size_t const base_position =
            baseIndex(data, row_term.variable);
        if (touched_flags[base_position] == 0)
        {
          touched_flags[base_position] = 1;
          touched.push_back(base_position);
        }
        coefficients[base_position] += contribution;
      }
      ExactRational main_contribution = bound->threshold * term.weight;
      ExactRational infinitesimal_contribution =
          bound->infinitesimal * term.weight;
      if (lower)
      {
        main_contribution.negate();
        infinitesimal_contribution.negate();
      }
      right_main += main_contribution;
      right_infinitesimal += infinitesimal_contribution;
    }

    for (std::size_t const base_position : touched)
    {
      if (!coefficients[base_position].isZero())
      {
        return VerificationResult{VerificationError::NotContradictory};
      }
    }
    bool const negative = right_main.sign() < 0 ||
                          (right_main.isZero() &&
                           right_infinitesimal.sign() < 0);
    return VerificationResult{negative ? VerificationError::None
                                       : VerificationError::NotContradictory};
  }
  catch (NumberFailure const& failure)
  {
    return mappedFailure(failure);
  }
  catch (StorageFailure const& failure)
  {
    return mappedFailure(failure);
  }
  catch (...)
  {
    return VerificationResult{VerificationError::InternalError};
  }
}

VerificationResult verifyExactLraConflict(
    ExactLraVerificationDataView const& data,
    Conflict const& conflict)
{
  return verifyExactLraConflictImpl(data, conflict,
                                    /*require_active=*/true,
                                    /*audit_snapshot=*/true);
}

VerificationResult verifyExactLraConflictCandidate(
    ExactLraVerificationDataView const& data,
    Conflict const& conflict, bool audit_snapshot)
{
  /* The full snapshot audit is linear in the whole registration; a
   * certificate-heavy search asks per conflict, so the caller amortizes
   * the audit to once per core revision and skips it in between -- the
   * data cannot have changed without a revision. */
  return verifyExactLraConflictImpl(data, conflict,
                                    /*require_active=*/false,
                                    audit_snapshot);
}

bool exactLraCheckResultShapeValid(CheckResult const& result) noexcept
{
  switch (result.status)
  {
    case CheckStatus::Ready:
    case CheckStatus::Interrupted:
    case CheckStatus::ResourceLimit:
    case CheckStatus::InternalError:
      return !result.conflict && !result.model;
    case CheckStatus::Consistent:
      return !result.conflict && result.model.has_value();
    case CheckStatus::Conflict:
      return result.conflict.has_value() && !result.model;
  }
  return false;
}

bool exactLraAssertResultShapeValid(AssertResult const& result) noexcept
{
  return !result.immediate_conflict || result.status == InputStatus::Accepted;
}

}  // namespace stp::lra

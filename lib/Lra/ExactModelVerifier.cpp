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

bool snapshotValid(ExactLraVerificationDataView const& data)
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
  ExactLraActiveBounds active;
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

bool deltaLess(ExactRational const& left_main,
               ExactRational const& left_infinitesimal,
               ExactRational const& right_main,
               ExactRational const& right_infinitesimal)
{
  int const main_order = left_main.compare(right_main);
  return main_order < 0 ||
         (main_order == 0 &&
          left_infinitesimal.compare(right_infinitesimal) < 0);
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

static VerificationResult verifyExactLraModelImpl(
    ExactLraVerificationDataView const& data, Model const& model,
    BoundRef const* bounds_begin, BoundRef const* bounds_end,
    bool audit_snapshot)
{
  if (!sameTag(model.tag, data.current_tag))
  {
    return VerificationResult{VerificationError::StaleId};
  }
  try
  {
    if (audit_snapshot && !snapshotValid(data))
    {
      return VerificationResult{VerificationError::InternalError};
    }

    for (std::size_t index = 0; index != model.values.size(); ++index)
    {
      ModelValue const& value = model.values[index];
      if (value.variable.generation() != data.current_tag.generation ||
          !std::binary_search(data.base_variables.begin(),
                              data.base_variables.end(), value.variable))
      {
        return VerificationResult{VerificationError::StaleId};
      }
      if (index != 0 &&
          !(model.values[index - 1U].variable < value.variable))
      {
        return VerificationResult{VerificationError::DuplicateEntry};
      }
      if (!value.value.invariantHolds())
      {
        return VerificationResult{VerificationError::InternalError};
      }
    }
    if (model.values.size() != data.base_variables.size())
    {
      return VerificationResult{VerificationError::IncompleteModel};
    }
    for (std::size_t index = 0; index != model.values.size(); ++index)
    {
      if (model.values[index].variable != data.base_variables[index])
      {
        return VerificationResult{VerificationError::IncompleteModel};
      }
    }

    std::vector<ExactRational> row_values;
    row_values.reserve(data.rows.size());
    for (ExactLraVerificationRow const& row : data.rows)
    {
      ExactRational value(std::int64_t{0});
      for (LinearTerm const& term : row.terms)
      {
        std::size_t const index = baseIndex(data, term.variable);
        value += term.coefficient * model.values[index].value;
      }
      row_values.push_back(std::move(value));
    }

    ExactRational const zero(std::int64_t{0});
    auto check_bound = [&](BoundRef reference) {
      ExactLraVerificationBound const* const bound =
          findBound(data, reference);
      if (bound == nullptr || bound->row.ordinal() >= row_values.size())
      {
        return VerificationError::InternalError;
      }
      ExactRational const& row_value = row_values[bound->row.ordinal()];
      if (bound->kind == ExactLraVerificationBoundKind::Upper)
      {
        return deltaLess(bound->threshold, bound->infinitesimal,
                         row_value, zero)
                   ? VerificationError::BoundViolation
                   : VerificationError::None;
      }
      if (bound->kind == ExactLraVerificationBoundKind::Lower)
      {
        return deltaLess(row_value, zero, bound->threshold,
                         bound->infinitesimal)
                   ? VerificationError::BoundViolation
                   : VerificationError::None;
      }
      return VerificationError::InternalError;
    };

    if (bounds_begin != nullptr)
    {
      /* Candidate mode: the caller names the asserted bounds. */
      for (BoundRef const* reference = bounds_begin;
           reference != bounds_end; ++reference)
      {
        VerificationError const error = check_bound(*reference);
        if (error != VerificationError::None)
        {
          return VerificationResult{error};
        }
      }
      return VerificationResult{VerificationError::None};
    }
    for (BoundRef reference : data.active_bounds)
    {
      VerificationError const error = check_bound(reference);
      if (error != VerificationError::None)
      {
        return VerificationResult{error};
      }
    }
    if (data.pending_conflict_bound)
    {
      VerificationError const error = check_bound(*data.pending_conflict_bound);
      if (error != VerificationError::None)
      {
        return VerificationResult{error};
      }
    }
    return VerificationResult{VerificationError::None};
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

VerificationResult verifyExactLraModel(
    ExactLraVerificationDataView const& data,
    Model const& model)
{
  return verifyExactLraModelImpl(data, model, nullptr, nullptr,
                                 /*audit_snapshot=*/true);
}

VerificationResult verifyExactLraModelCandidate(
    ExactLraVerificationDataView const& data, Model const& model,
    BoundRef const* bounds_begin, BoundRef const* bounds_end,
    bool audit_snapshot)
{
  return verifyExactLraModelImpl(data, model, bounds_begin, bounds_end,
                                 audit_snapshot);
}

}  // namespace stp::lra

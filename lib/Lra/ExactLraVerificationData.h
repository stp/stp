#ifndef STP_LRA_EXACT_LRA_VERIFICATION_DATA_H
#define STP_LRA_EXACT_LRA_VERIFICATION_DATA_H

#include "ExactLraTypes.h"

#include <optional>
#include <vector>

namespace stp::lra {

enum class ExactLraVerificationBoundKind : std::uint8_t
{
  Lower,
  Upper
};

struct ExactLraVerificationRow
{
  RowId id;
  std::vector<LinearTerm> terms;
};

struct ExactLraVerificationAtom
{
  AtomId id;
  RowId row;
  Relation positive_relation;
  ExactRational threshold;
  OriginId positive_origin;
  OriginId negative_origin;
  BoundRef positive_bound;
  BoundRef negative_bound;
};

struct ExactLraVerificationBound
{
  BoundRef reference;
  RowId row;
  ExactLraVerificationBoundKind kind;
  ExactRational threshold;
  ExactRational infinitesimal;
  OriginId origin;
  AtomId atom;
  bool positive_component;
};

struct ExactLraVerificationDataView
{
  WitnessTag current_tag;
  std::vector<VariableId> const& base_variables;
  std::vector<ExactLraVerificationRow> const& rows;
  std::vector<ExactLraVerificationAtom> const& atoms;
  std::vector<ExactLraVerificationBound> const& bounds;
  std::vector<BoundRef> const& active_bounds;
  std::optional<BoundRef> pending_conflict_bound;
};

VerificationResult verifyExactLraConflict(
    ExactLraVerificationDataView const& data,
    Conflict const& conflict);
/* The same exact Farkas judgement without requiring the cited bounds to
 * be active in this core: a candidate certificate's support is asserted
 * in the outer search (the caller vouches for that, and the resulting
 * clause is theory-valid regardless), while this core may not have the
 * bounds asserted at all -- that is the point of certifying without
 * re-deriving. */
VerificationResult verifyExactLraConflictCandidate(
    ExactLraVerificationDataView const& data,
    Conflict const& conflict, bool audit_snapshot);
VerificationResult verifyExactLraModel(
    ExactLraVerificationDataView const& data,
    Model const& model);
/* The same exact judgement against an explicit bound list instead of the
 * active set: a candidate model's asserted bounds live in the outer
 * search, not in this core.  The caller amortizes the snapshot audit. */
VerificationResult verifyExactLraModelCandidate(
    ExactLraVerificationDataView const& data, Model const& model,
    BoundRef const* bounds_begin, BoundRef const* bounds_end,
    bool audit_snapshot);

bool exactLraCheckResultShapeValid(CheckResult const&) noexcept;
bool exactLraAssertResultShapeValid(AssertResult const&) noexcept;

}  // namespace stp::lra

#endif

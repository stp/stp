#ifndef STP_LRA_EXACT_LRA_TYPES_H
#define STP_LRA_EXACT_LRA_TYPES_H

#include "ExactRational.h"
#include "NumberBudget.h"
#include "Storage/LraIds.h"
#include "Storage/StorageMetrics.h"

#include <cstdint>
#include <optional>
#include <vector>

namespace stp::lra {

enum class Relation : std::uint8_t
{
  Less,
  LessEqual,
  Greater,
  GreaterEqual
};

enum class DirectBoundsMode : std::uint8_t
{
  Disabled,
  Identity,
  Singleton
};

enum class CheckStatus : std::uint8_t
{
  Ready,
  Consistent,
  Conflict,
  Interrupted,
  ResourceLimit,
  InternalError
};

enum class InputStatus : std::uint8_t
{
  Accepted,
  Duplicate,
  InvalidId,
  InvalidState,
  Unsupported,
  ResourceLimit,
  InternalError
};

enum class StopReason : std::uint8_t
{
  Continue,
  Interrupted,
  ResourceLimit
};

enum class VerificationError : std::uint8_t
{
  None,
  StaleId,
  InactiveSupport,
  DuplicateEntry,
  InvalidWeight,
  OriginMismatch,
  RowViolation,
  BoundViolation,
  IncompleteModel,
  NotContradictory,
  ResourceLimit,
  InternalError
};

struct LinearTerm
{
  VariableId variable;
  ExactRational coefficient;
};

struct WitnessTag
{
  CoreGeneration generation;
  std::uint64_t state_revision;
};

struct ConflictTerm
{
  OriginId origin;
  BoundRef bound;
  ExactRational weight;
};

struct Conflict
{
  WitnessTag tag;
  std::vector<ConflictTerm> terms;
};

/* One support entry of a conflict certificate proposed from outside the
 * core -- the advisory float tier names the atom, the asserted polarity
 * and a positive Farkas weight; the core resolves the bound and judges
 * the combination exactly. */
struct ConflictCandidateTerm
{
  AtomId atom;
  bool positive;
  ExactRational weight;
};

/* One asserted atom of a model certificate proposed from outside the
 * core: the model must satisfy the bound this atom's polarity installs. */
struct CandidateBound
{
  AtomId atom;
  bool positive;
};

/* One base variable of a proposed model, before the infinitesimal is
 * substituted: value + delta * epsilon in the DdM sense.  The core picks
 * a concrete epsilon against the certificate's bounds, substitutes, and
 * verifies the result exactly. */
struct ModelCandidateValue
{
  VariableId variable;
  ExactRational value;
  ExactRational delta;
};

struct ModelValue
{
  VariableId variable;
  ExactRational value;
};

struct Model
{
  WitnessTag tag;
  std::vector<ModelValue> values;
};

template <class T>
struct InputResult
{
  InputStatus status;
  std::optional<T> value;
};

struct AssertResult
{
  InputStatus status;
  std::optional<Conflict> immediate_conflict;
};

struct VerificationResult
{
  VerificationError error;

  bool verified() const noexcept
  {
    return error == VerificationError::None;
  }
};

struct CoreStatistics
{
  std::uint64_t variables;
  std::uint64_t rows;
  std::uint64_t atoms;
  std::uint64_t bounds;
  // Current registration coverage, independent of whether the experiment
  // is enabled. Direct rows retain semantic IDs but have no tableau row.
  std::uint64_t identity_rows = 0;
  std::uint64_t singleton_rows = 0;
  std::uint64_t direct_rows = 0;
  std::uint64_t assertions;
  std::uint64_t pushes;
  std::uint64_t pops;
  std::uint64_t checks;
  std::uint64_t pivots;
  std::uint64_t bland_pivots;
  // The engine's own view: pivots by pricing, dormant rows brought in
  // and taken out, and the cells their normalisations produced.
  std::uint64_t engine_pivots = 0;
  std::uint64_t engine_bland_steps = 0;
  std::uint64_t engine_activations = 0;
  std::uint64_t engine_deactivations = 0;
  std::uint64_t engine_normalised_cells = 0;
  std::uint64_t engine_early_conflicts = 0;
  std::uint64_t engine_soi_steps = 0;
  std::uint64_t engine_soi_bound_flips = 0;
  std::uint64_t engine_soi_fallbacks = 0;
  std::uint64_t immediate_conflicts;
  std::uint64_t tableau_conflicts;
  std::uint64_t models_produced;
  std::uint64_t conflicts_produced;
  std::uint64_t model_verifications;
  /* Candidate models re-derived by the exact solve over their pinned
   * bounds after the proposed coordinates failed verification. */
  std::uint64_t model_repairs = 0;
  std::uint64_t conflict_recovery_attempts = 0;
  std::uint64_t conflict_recoveries = 0;
  std::uint64_t conflict_recovery_nanoseconds = 0;
  std::uint64_t conflict_verifications;
  std::uint64_t verification_failures;
  std::uint64_t interruptions;
  std::uint64_t resource_stops;
  std::uint64_t internal_errors;
  std::uint64_t resets;
  std::uint64_t witness_invalidations;
  NumberMetrics numbers;
  StorageMetrics storage;
};

struct CheckResult
{
  CheckStatus status;
  std::optional<Conflict> conflict;
  std::optional<Model> model;
};

}  // namespace stp::lra

#endif

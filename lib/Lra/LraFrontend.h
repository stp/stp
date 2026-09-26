#ifndef STP_LRA_FRONTEND_H
#define STP_LRA_FRONTEND_H

#include "ExactRational.h"
#include "stp/AST/AST.h"

#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

namespace stp {
class STPMgr;

namespace lra {


struct LraSymbolId final
{
  std::uint64_t value = 0;

  friend bool operator==(LraSymbolId lhs, LraSymbolId rhs)
  {
    return lhs.value == rhs.value;
  }
  friend bool operator!=(LraSymbolId lhs, LraSymbolId rhs)
  {
    return !(lhs == rhs);
  }
  friend bool operator<(LraSymbolId lhs, LraSymbolId rhs)
  {
    return lhs.value < rhs.value;
  }
};

struct LinearMonomial final
{
  LraSymbolId symbol;
  ExactRational coefficient;
};

struct LinearPolynomial final
{
  std::vector<LinearMonomial> terms;
  ExactRational constant;
};

enum class FrontendRelation : std::uint8_t
{
  Less,
  LessEqual,
  Greater,
  GreaterEqual,
  Equal
};

struct CanonicalLraPredicate final
{
  FrontendRelation relation = FrontendRelation::Equal;
  LinearPolynomial lhs_minus_rhs;
  ASTNode source;
};

struct NormalizedPredicate final
{
  CanonicalLraPredicate canonical;
  bool is_constant = false;
  bool constant_value = false;
};

enum class FrontendFailureKind : std::uint8_t
{
  Unsupported,
  WrongSort,
  Malformed,
  ResourceLimit,
  AllocationFailure,
  InternalError
};

class FrontendFailure final : public std::runtime_error
{
public:
  FrontendFailure(FrontendFailureKind kind, std::string detail);
  FrontendFailureKind kind() const noexcept { return kind_; }

private:
  FrontendFailureKind kind_;
};

enum class EqualityComponent : std::uint8_t
{
  None,
  LessEqual,
  GreaterEqual,
  DisequalityLess,
  DisequalityGreater
};

struct PredicateRegistration final
{
  std::uint64_t predicate_id = 0;
  ASTNode opaque_atom;
  CanonicalLraPredicate payload;
  std::uint64_t equality_group_id = 0;
  EqualityComponent equality_component = EqualityComponent::None;
};

struct EqualityRegistration final
{
  std::uint64_t equality_group_id = 0;
  ASTNode source_equality;
  ASTNode equality_atom;
  ASTNode less_equal_atom;
  ASTNode greater_equal_atom;
};

struct FrontendMetrics final
{
  std::uint64_t symbols = 0;
  std::uint64_t normalization_calls = 0;
  std::uint64_t normalization_nodes = 0;
  std::uint64_t predicates = 0;
  std::uint64_t equality_groups = 0;
  std::uint64_t opaque_atoms = 0;
  // Real-sorted term ites replaced by a named value and its two branch
  // equalities.
  std::uint64_t lifted_term_ites = 0;
  std::uint64_t constant_predicates = 0;
  std::uint64_t maximum_coefficient_bits = 0;
};

struct PreregisteredFormula final
{
  ASTNode boolean_formula;
  std::vector<PredicateRegistration> predicates;
  std::vector<EqualityRegistration> equalities;
  std::uint64_t registry_generation = 0;
  FrontendMetrics metrics;
};

// Private, SAT-neutral first-fragment frontend.  Its header is never
// installed.  It owns no solver/core object and its only output formula is
// ordinary Boolean STP syntax plus immutable exact payloads kept out of band.
class Frontend final
{
public:
  explicit Frontend(STPMgr& manager);

  LinearPolynomial normalize(const ASTNode& term);
  NormalizedPredicate normalizePredicate(const ASTNode& predicate);
  PreregisteredFormula preregister(const ASTNode& formula);

  std::string exportPolynomial(const LinearPolynomial& polynomial) const;
  // Row interning deliberately excludes the polynomial constant: the
  // constant becomes the exact predicate threshold, while one coefficient
  // vector is registered with the core only once.  This private exporter uses
  // the same canonical number scope and byte representation as
  // exportPolynomial().
  std::string exportCoefficientVector(
      const LinearPolynomial& polynomial) const;
  std::string exportPredicate(const CanonicalLraPredicate& predicate) const;
  std::uint64_t stableHash(const LinearPolynomial& polynomial) const;

  // Resolve an already assigned stable frontend ID without allocating a new
  // ID or advancing the registry generation.  The atom registry uses
  // the returned manager-owned node only as immutable symbol metadata.
  ASTNode symbolNode(LraSymbolId symbol) const;
  bool ownsNode(const ASTNode& node) const noexcept;

  // Neutral exact-number resource controls.  The frontend uses them for focused
  // strong-commit gates; later solve contexts may only tighten these limits.
  void configureNumberLimits(NumberLimits limits);
  NumberLimits numberLimits() const noexcept;
  NumberMetrics numberMetrics() const noexcept;
  void resetNumberAccounting() noexcept;
  bool numberStopped() const noexcept;
  std::uint64_t registryGeneration() const noexcept;

  static bool containsRealSyntax(const ASTNode& formula);
  static void validateCanonical(const LinearPolynomial& polynomial);

private:
  STPMgr& manager_;
};

} // namespace lra
} // namespace stp

#endif

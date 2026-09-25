#ifndef STP_LRA_ATOM_REGISTRY_H
#define STP_LRA_ATOM_REGISTRY_H

#include "LraFrontend.h"

#include <cstdint>
#include <stdexcept>
#include <string>
#include <vector>

namespace stp {
class STPMgr;
class PreparationControl;

namespace lra {

// Registry identities are value types in a manager-unique domain.  They are
// deliberately unrelated to storage and core generation IDs and to packed SAT
// variables.  Serial zero is reserved in every domain.
struct LraRegistryTag final
{
  std::uint64_t domain = 0;
  std::uint64_t generation = 0;

  bool valid() const noexcept { return domain != 0 && generation != 0; }
  friend bool operator==(LraRegistryTag lhs, LraRegistryTag rhs) noexcept
  {
    return lhs.domain == rhs.domain && lhs.generation == rhs.generation;
  }
  friend bool operator!=(LraRegistryTag lhs, LraRegistryTag rhs) noexcept
  {
    return !(lhs == rhs);
  }
};

#define STP_LRA_REGISTRY_ID(NAME)                                           \
  struct NAME final                                                        \
  {                                                                        \
    std::uint64_t domain = 0;                                              \
    std::uint64_t serial = 0;                                              \
    bool valid() const noexcept { return domain != 0 && serial != 0; }      \
    friend bool operator==(NAME lhs, NAME rhs) noexcept                     \
    {                                                                      \
      return lhs.domain == rhs.domain && lhs.serial == rhs.serial;          \
    }                                                                      \
    friend bool operator!=(NAME lhs, NAME rhs) noexcept                     \
    {                                                                      \
      return !(lhs == rhs);                                                 \
    }                                                                      \
    friend bool operator<(NAME lhs, NAME rhs) noexcept                      \
    {                                                                      \
      return lhs.domain < rhs.domain ||                                    \
             (lhs.domain == rhs.domain && lhs.serial < rhs.serial);         \
    }                                                                      \
  }

STP_LRA_REGISTRY_ID(LraRegistrySymbolId);
STP_LRA_REGISTRY_ID(LraCanonicalRowId);
STP_LRA_REGISTRY_ID(LraComponentId);
STP_LRA_REGISTRY_ID(LraEqualityGroupId);
STP_LRA_REGISTRY_ID(LraAssertionFrameId);

#undef STP_LRA_REGISTRY_ID

/* As SolveContextFailureKind: a budget that ran out, or a state that is
 * wrong.  The throw site's message says which state; nothing reads more. */
enum class RegistryFailureKind : std::uint8_t
{
  ResourceLimit,
  Invalid
};

class RegistryFailure final : public std::runtime_error
{
public:
  RegistryFailure(RegistryFailureKind kind, std::string detail);
  RegistryFailureKind kind() const noexcept { return kind_; }

private:
  RegistryFailureKind kind_;
};

struct RegistryMonomial final
{
  LraRegistrySymbolId symbol;
  ExactRational coefficient;
};

struct RegistrySymbol final
{
  LraRegistrySymbolId id;
  LraSymbolId frontend_id;
  ASTNode symbol;
};

struct RegistryRow final
{
  LraCanonicalRowId id;
  std::vector<RegistryMonomial> terms;
  std::string canonical_key;
};

struct RegistrySourceOwnership final
{
  LraAssertionFrameId frame;
  ASTNode source;
  LraEqualityGroupId equality_group;
  EqualityComponent equality_component = EqualityComponent::None;
};

struct RegistryComponent final
{
  LraComponentId id;
  LraCanonicalRowId row;
  FrontendRelation relation = FrontendRelation::Less;
  ExactRational threshold;
  ASTNode opaque_atom;
  std::string canonical_key;
  std::vector<RegistrySourceOwnership> sources;
};

struct RegistryEqualityGroup final
{
  LraEqualityGroupId id;
  LraAssertionFrameId frame;
  ASTNode source_equality;
  ASTNode equality_atom;
  LraComponentId less_equal_component;
  LraComponentId greater_equal_component;
};

struct LraRegistrySnapshot final
{
  LraRegistryTag tag;
  std::vector<RegistrySymbol> symbols;
  std::vector<RegistryRow> rows;
  std::vector<RegistryComponent> components;
  std::vector<RegistryEqualityGroup> equalities;
};

struct RegisteredLraFormula final
{
  ASTNode boolean_formula;
  LraRegistryTag tag;
  LraAssertionFrameId frame;
  std::vector<LraComponentId> component_occurrences;
  std::vector<LraEqualityGroupId> equality_groups;
};

struct LraRegistryMetrics final
{
  std::uint64_t active_frames = 0;
  std::uint64_t active_symbols = 0;
  std::uint64_t active_rows = 0;
  std::uint64_t active_components = 0;
  std::uint64_t active_equality_groups = 0;
  std::uint64_t row_deduplications = 0;
  std::uint64_t component_deduplications = 0;
  std::uint64_t formulas_registered = 0;
  std::uint64_t frames_popped = 0;
  std::uint64_t destructive_resets = 0;
  std::uint64_t solve_epochs_allocated = 0;
};

class LraAtomRegistryState;

// STPMgr owns the concrete state through its private LraAstState.  This
// lightweight facade can be recreated without resetting IDs or losing frame
// ownership.  Nothing declared here is installed.
class LraAtomRegistry final
{
public:
  explicit LraAtomRegistry(STPMgr& manager);

  LraAssertionFrameId pushAssertionFrame();
  void popAssertionFrame(LraAssertionFrameId frame);

  RegisteredLraFormula registerFormula(
      const PreregisteredFormula& formula, LraAssertionFrameId frame);

  /* One frame member's interned opaque atom, without copying the frame.
   *
   * Hash-consing can replace a component a formula has just preregistered
   * with the stable representative an older frame already holds, so a caller
   * that has just registered a formula has to ask which atom it actually
   * got. Taking a whole frame snapshot to answer that is what these replace:
   * the snapshot is O(frame), and an extension only ever asks about the
   * handful of ids the new formula produced.
   *
   * Returns a null node when the id is not a member of that frame, which the
   * caller should treat as the registry having lost the occurrence. */
  ASTNode componentOpaqueAtom(LraComponentId id,
                              LraAssertionFrameId frame) const noexcept;
  ASTNode equalityOpaqueAtom(LraEqualityGroupId id,
                             LraAssertionFrameId frame) const noexcept;

  LraRegistrySnapshot activeSnapshot(
      const PreparationControl* preparation = nullptr) const;
  // Snapshot only the closure owned by one assertion frame.  The coordinator uses this
  // for its solve-local preregistration frame so persistent public-context
  // ownership does not require dormant opaque atoms to have SAT bindings.
  LraRegistrySnapshot frameSnapshot(LraAssertionFrameId frame,
      const PreparationControl* preparation = nullptr) const;
  bool validateSnapshot(const LraRegistrySnapshot& snapshot) const noexcept;

  /* The constant-cost half of the checks below: the registry tag, the frame,
   * and the snapshot's sizes.  Every mutation of the registry advances the
   * generation and so changes the tag, which is what makes a solve context
   * built against an older registry detectable -- so this is what a caller
   * needs to re-check often.  The full walks compare every symbol, row,
   * component and equality, and are for taking a snapshot, not for using one. */
  bool validateSnapshotIdentity(
      const LraRegistrySnapshot& snapshot) const noexcept;
  bool validateFrameSnapshotIdentity(
      const LraRegistrySnapshot& snapshot,
      LraAssertionFrameId frame_id) const noexcept;
  bool validateFrameSnapshot(const LraRegistrySnapshot& snapshot,
                             LraAssertionFrameId frame) const noexcept;
  LraRegistryTag tag() const noexcept;
  std::uint64_t allocateSolveEpoch();
  void destructiveReset();
  LraRegistryMetrics metrics() const noexcept;
  STPMgr& manager() const noexcept { return manager_; }

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  void testSetNextSolveEpoch(std::uint64_t next);
  void testSetNextFrameSerial(std::uint64_t next);
#endif

private:
  LraAtomRegistryState& state();
  const LraAtomRegistryState& state() const;
  STPMgr& manager_;
};

// LraAstState's destructor is compiled in LraFrontend.cpp, where the concrete
// registry state is intentionally incomplete.  Keep deletion in its owning
// translation unit while preserving the required manager destruction order.
void destroyLraAtomRegistryState(LraAtomRegistryState* state) noexcept;

} // namespace lra
} // namespace stp

#endif

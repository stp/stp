#ifndef STP_LRA_AST_REAL_CONST_H
#define STP_LRA_AST_REAL_CONST_H

#include "ASTRealConstAccess.h"
#include "ExactRational.h"
#include "stp/AST/ASTInternal.h"

#include <cstddef>
#include <cstdint>
#include <unordered_set>
#include <utility>
#include <vector>

namespace stp {

namespace lra {
class Frontend;
class LraAtomRegistryState;
class RealModel;
}

class ASTRealConst final : public ASTInternal
{
  friend class ASTNode;
  friend class STPMgr;
  friend struct ASTRealConstHash;
  friend struct ASTRealConstEqual;
  friend class lra::Frontend;
  friend std::string lra::detail::realCanonical(const ASTInternal* node);
  friend std::string lra::detail::realNumerator(const ASTInternal* node);
  friend std::string lra::detail::realDenominator(const ASTInternal* node);

  lra::ExactRational value_;
  std::uint64_t stable_hash_;
  static const ASTVec empty_children_;

  ASTRealConst(STPMgr* manager, const lra::ExactRational& value);
  ASTRealConst(const ASTRealConst& other);

  void CleanUp() override;
  void nodeprint(ostream& os, bool c_friendly = false) override;

  void setIndexWidth(uint32_t) override;
  uint32_t getIndexWidth() const override { return 0; }
  void setValueWidth(uint32_t) override;
  uint32_t getValueWidth() const override { return 0; }
  void setExpWidth(uint32_t) override;
  uint32_t getExpWidth() const override { return 0; }
  void setSigWidth(uint32_t) override;
  uint32_t getSigWidth() const override { return 0; }
  std::string canonicalText() const;
  std::string numeratorText() const;
  std::string denominatorText() const;
  SourceSort getDeclaredSourceSort() const override
  {
    return SourceSort::real();
  }

public:
  ASTChildren GetChildren() const override { return empty_children_; }
  ~ASTRealConst() override = default;
};

class LraFrontendRegistryState;

struct ASTRealConstHash
{
  std::size_t operator()(const ASTRealConst* value) const;
};

struct ASTRealConstEqual
{
  bool operator()(const ASTRealConst* lhs, const ASTRealConst* rhs) const;
};

// NumberBudget is declared before the value table, and therefore destroyed
// after it. ExactRational's budget-outlives-values contract is structural.
class LraAstState final
{
public:
  LraAstState();
  ~LraAstState();

  lra::NumberBudget number_budget;
  std::unordered_set<ASTRealConst*, ASTRealConstHash, ASTRealConstEqual>
      real_constants;
  // Manager-lifetime owning references to every public Real symbol.  A
  // committed model gives even an unconstrained declared symbol a
  // deterministic exact value; SMT-LIB frame filtering decides which of
  // these symbols is currently visible.
  ASTVec real_symbols;
  // Membership only; real_symbols owns the nodes and preserves first-seen
  // order for registration and model completion. Its references keep these
  // identities alive until both containers are cleared together.
  std::unordered_set<std::uint64_t> real_symbol_ids;
  // Opaque value copies of manager-owned registry assertion frames.  The
  // stack enters lockstep with STPMgr's public assertion levels when the
  // first Real assertion becomes active.
  std::vector<std::pair<std::uint64_t, std::uint64_t>> assertion_frames;
  LraFrontendRegistryState* frontend_registry = nullptr;
  lra::LraAtomRegistryState* atom_registry = nullptr;
  lra::RealModel* real_model = nullptr;
};

} // namespace stp

#endif

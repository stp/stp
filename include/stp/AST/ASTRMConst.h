/********************************************************************
 * A source-language RoundingMode literal over STP's 5-bit carrier.
 ********************************************************************/
#ifndef ASTRMCONST_H
#define ASTRMCONST_H

#include "ASTBVConst.h"

namespace stp
{
class STPMgr;

// Kept as kind BVCONST so every post-lowering bit-vector pass can consume it,
// but interned separately from a plain five-bit constant through SourceSort.
class ASTRMConst final : public ASTBVConst
{
  friend class STPMgr;

  ASTRMConst(STPMgr* mgr, CBV bv);
  ASTRMConst(const ASTRMConst& other);

  SourceSort getDeclaredSourceSort() const override
  {
    return SourceSort::roundingMode();
  }

public:
  ~ASTRMConst() override = default;
};

} // namespace stp
#endif

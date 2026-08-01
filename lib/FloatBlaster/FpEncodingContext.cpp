/********************************************************************
 * Solve-local floating-point lowering and model-lifting context.
 ********************************************************************/
#include "stp/FloatBlaster/FpEncodingContext.h"

namespace stp
{

FpEncodingContext::FpEncodingContext(STPMgr* bm_)
    : bm(bm_), node_factory(bm_->defaultNodeFactory), totalise(bm_), blast(bm_)
{
}

FpEncodingContext::~FpEncodingContext() = default;

void FpEncodingContext::requireOriginalNodeFactory() const
{
  if (bm->defaultNodeFactory != node_factory)
    FatalError("floating-point encoding context reused after the node factory "
               "changed");
}

ASTNode FpEncodingContext::prepare(const ASTNode& source)
{
  requireOriginalNodeFactory();
  return totalise.topLevel(source);
}

void FpEncodingContext::copyArrayEqualityRewrites(ASTNodeMap& out) const
{
  requireOriginalNodeFactory();
  totalise.copyArrayEqualityRewrites(out);
}

ASTNode FpEncodingContext::lowerPrepared(const ASTNode& prepared)
{
  requireOriginalNodeFactory();
  return blast.topLevel(prepared);
}

ASTNode FpEncodingContext::encodeForModel(const ASTNode& source)
{
  requireOriginalNodeFactory();
  return lowerPrepared(prepare(source));
}

} // namespace stp

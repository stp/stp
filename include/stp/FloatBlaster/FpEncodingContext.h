/********************************************************************
 * Solve-local floating-point lowering and model-lifting context.
 ********************************************************************/
#ifndef FPENCODINGCONTEXT_H
#define FPENCODINGCONTEXT_H

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FpDomainSimplify.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{

// Owns every mapping created while one solver invocation lowers source FP
// expressions to their bit-vector encoding. The context deliberately lives
// past the SAT call: get-value and counterexample checking must use the same
// totalisation arrays and the same lowering map as the solved formula.
class FpEncodingContext final
{
public:
  explicit FpEncodingContext(STPMgr* bm_);
  DLL_PUBLIC ~FpEncodingContext();

  FpEncodingContext(const FpEncodingContext&) = delete;
  FpEncodingContext& operator=(const FpEncodingContext&) = delete;

  // Totalise partial operations, canonicalise rich array indices, and add
  // formula-level source-sort side conditions.
  ASTNode prepare(const ASTNode& source);

  // Copy opaque array-equality aliases produced by the most recent prepare()
  // call for the solve-boundary extensionality lowering pass.
  void copyArrayEqualityRewrites(ASTNodeMap& out) const;

  // Lower a prepared expression to its packed bit-vector circuit. Kept
  // separate because the word-level simplifiers run between these two steps.
  ASTNode lowerPrepared(const ASTNode& prepared);

  // Lazily obtain the target-language encoding of a source expression for
  // model evaluation, reusing the solve's preparation and lowering caches.
  ASTNode encodeForModel(const ASTNode& source);

private:
  void requireOriginalNodeFactory() const;

  STPMgr* bm;
  NodeFactory* node_factory;
  FpTotalise totalise;
  FpDomainSimplify domain;
  FloatBlast blast;
};

} // namespace stp

#endif

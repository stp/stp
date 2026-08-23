/********************************************************************
 * Solve-local floating-point lowering and model-lifting context.
 ********************************************************************/
#include "stp/FloatBlaster/FpEncodingContext.h"

#include <iostream>

namespace stp
{

FpEncodingContext::FpEncodingContext(STPMgr* bm_)
    : bm(bm_), node_factory(bm_->defaultNodeFactory), totalise(bm_),
      domain(bm_), blast(bm_)
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
  ASTNode out = totalise.topLevel(source);
  if (bm->UserFlags.fp_domain_simplify ||
      bm->UserFlags.fp_domain_sound_zero_facts ||
      bm->UserFlags.fp_domain_row_bounds)
  {
    out = domain.topLevel(out);
    if (bm->UserFlags.stats_flag)
    {
      const FpDomainSimplify::Statistics& s = domain.statistics();
      std::cerr << "FpDomainSimplify: " << s.boxed_symbols
                << " boxed symbols, " << s.interval_true
                << " interval-true, " << s.interval_false
                << " interval-false, " << s.classifier_false
                << " classifier-false, " << s.difference_zero_equalities
                << " diff-zero-eq, " << s.nonnegative_zero_sums
                << " nonnegative-zero-sum, " << s.sound_zero_rows
                << " sound-zero-rows, " << s.sound_zero_facts
                << " sound-zero-facts, " << s.row_bound_rows
                << " row-bound-rows, " << s.row_bound_false
                << " row-bound-false" << std::endl;
    }
  }
  return out;
}

void FpEncodingContext::copyArrayEqualityRewrites(ASTNodeMap& out) const
{
  requireOriginalNodeFactory();
  totalise.copyArrayEqualityRewrites(out);
}

ASTNode FpEncodingContext::lowerPrepared(const ASTNode& prepared)
{
  requireOriginalNodeFactory();
  const ASTNode out = blast.topLevel(prepared);
  if (bm->UserFlags.stats_flag)
  {
    // All-zero counters mean no SymFPU circuit was built: every
    // floating-point node passed through to the bit-blaster's native
    // encodings and this lowering was an identity.
    const FloatBlast::Statistics& s = blast.statistics();
    const bool noop =
        s.unpacked_operation_builds + s.unpack_builds + s.pack_builds == 0;
    std::cerr << "FloatBlast: " << s.unpacked_operation_builds
              << " SymFPU operations, " << s.unpack_builds << " unpacks, "
              << s.pack_builds << " packs"
              << (noop ? " (no-op: everything passed through natively)" : "")
              << std::endl;
  }
  return out;
}

ASTNode FpEncodingContext::encodeForModel(const ASTNode& source)
{
  requireOriginalNodeFactory();
  return lowerPrepared(prepare(source));
}

} // namespace stp

/********************************************************************
 * Experimental floating-point domain simplification.
 ********************************************************************/
#ifndef FPDOMAINSIMPLIFY_H
#define FPDOMAINSIMPLIFY_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <cstddef>

namespace stp
{

class FpDomainSimplify final
{
public:
  struct Statistics
  {
    size_t boxed_symbols = 0;
    size_t interval_true = 0;
    size_t interval_false = 0;
    size_t classifier_false = 0;
    size_t difference_zero_equalities = 0;
    size_t nonnegative_zero_sums = 0;
    size_t sound_zero_rows = 0;
    size_t sound_zero_facts = 0;
    size_t row_bound_rows = 0;
    size_t row_bound_false = 0;
  };

  explicit FpDomainSimplify(STPMgr* bm_);

  ASTNode topLevel(const ASTNode& source);

  const Statistics& statistics() const noexcept { return stats; }

private:
  STPMgr* bm;
  NodeFactory* node_factory;
  Statistics stats;
};

} // namespace stp

#endif

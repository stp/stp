#ifndef STP_LRA_PRESOLVE_H
#define STP_LRA_PRESOLVE_H

#include "stp/AST/AST.h"

namespace stp {
class STPMgr;
class SATSolver;
namespace lra {
struct LraReconstruction;

/* Presolve a Real query before the coordinator registers it: the
 * cross-predicate simplifications the bit-vector pipeline gets from its
 * preprocessing passes and the Real path bypasses. Every
 * transformation either keeps its witness conjoined or records exact model
 * reconstruction, checked against the original input before publication.
 * Monotone elimination requires a reconstruction destination. Which stages
 * run is decided by the
 * lra_presolve_* flags; with every stage off the input is returned as is.
 * highs_enabled is the query eligibility decision made before reconstruction
 * setup; the MIP flag alone does not enable preprocessing everywhere.
 */
ASTNode presolveForSolve(STPMgr& manager, const ASTNode& input,
                         SATSolver* solver = nullptr,
                         LraReconstruction* reconstruction = nullptr,
                         bool highs_enabled = false);

} // namespace lra
} // namespace stp

#endif

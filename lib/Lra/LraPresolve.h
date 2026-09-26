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
 * transformation is model-preserving on the transformed formula itself --
 * solved definitions stay conjoined, so the model and the exact verifier
 * read the same query the solve used. Which stages run is decided by the
 * lra_presolve_* flags; with every stage off the input is returned as is.
 */
ASTNode presolveForSolve(STPMgr& manager, const ASTNode& input,
                         SATSolver* solver = nullptr,
                         LraReconstruction* reconstruction = nullptr);

} // namespace lra
} // namespace stp

#endif

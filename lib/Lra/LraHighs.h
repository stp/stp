#ifndef STP_LRA_HIGHS_H
#define STP_LRA_HIGHS_H
#include "stp/AST/AST.h"
namespace stp
{
class STPMgr;
class SATSolver;
namespace lra
{
struct LraReconstruction;
class NumberBudget;
// MIP, when enabled, applies only to recognized unconditional binary domains.
// Explicit general LP/cut/replay requests retain their broader proposal path.
bool highsEnabledForQuery(STPMgr&, const ASTNode&, SATSolver*);
// Query-local numerical proposals over unconditional original constraints.
// A verdict is returned only after exact certification, including the complete
// source formula for SAT. Refusal leaves ordinary solving available.
ASTNode presolveHighs(STPMgr&, const ASTNode&, SATSolver*, LraReconstruction*,
                      NumberBudget&);
} // namespace lra
} // namespace stp
#endif

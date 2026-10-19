// Optional Satsuma preprocessing of STP's complete CNF.
#ifndef STP_SAT_SATSUMA_H
#define STP_SAT_SATSUMA_H

#include <vector>

namespace stp
{
class CNF;
class SATSolver;
class STPMgr;

// Returns false only when the size guard chooses ordinary clause loading.
// Preserves STP's variable numbers and models; includes extra encoded clauses
// in symmetry detection rather than inserting them after symmetry breaking.
bool addSatsumaCnfToSolver(STPMgr& manager, SATSolver& solver, const CNF& cnf,
                         const std::vector<std::vector<int>>& extraClauses);
}

#endif

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef INCREMENTALCNFENCODER_H_
#define INCREMENTALCNFENCODER_H_

// The incremental driver's AIG-to-CNF encoder: plain per-AND-gate
// Tseitin over live ABC AIG nodes, extending a solver that already holds
// variables and clauses from earlier check-sats while keeping every
// previously assigned variable id stable. That last property is the
// whole reason this exists instead of ABC's CNF derivation: Cnf_Derive
// and friends are whole-manager, one-shot, and renumber every object,
// and root literals, activation literals and refinement lemmas over old
// variables all depend on the numbering not moving. The cost of the
// trade is encoding quality -- incremental cones always get the
// three-clause Tseitin shape, never --cnf-generation-effort's technology mapping.
//
// Everything emitted is a conservative extension (fresh variables and
// definitional clauses), so nothing is ever retracted.

#include "stp/Sat/SATSolver.h"

#include "aig/aig/aig.h"

#include <cassert>
#include <cstdint>
#include <vector>

namespace stp
{

class IncrementalCnfEncoder
{
  SATSolver* solver;

  // AIG object Id -> CNF variable; -1 = not encoded yet. AIG Ids are
  // dense and only grow within one resettable encoding epoch.
  std::vector<int> aigIdToVar;

  // The variable standing for the AIG's constant-1 node, unit-asserted
  // at creation; -1 until first needed.
  int trueVar = -1;

  // Bumped on every new AIG-to-variable binding and on reset: a consumer
  // deriving anything from the bindings (the refinement adapter's symbol
  // map) caches against this rather than watching individual writes.
  uint64_t generation_ = 0;

  void setVarOf(Aig_Obj_t* regular, int var)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      aigIdToVar.resize(id + 1, -1);
    aigIdToVar[id] = var;
    generation_++;
  }

public:
  explicit IncrementalCnfEncoder(SATSolver* solver_) : solver(solver_) {}

  uint64_t generation() const { return generation_; }

  // A fresh backend: every binding is void, ids restart.
  void reset(SATSolver* solver_)
  {
    solver = solver_;
    aigIdToVar.clear();
    trueVar = -1;
    generation_++;
  }

  // Additionally return the table's storage (a relief rotation
  // reclaims allocations, not just contents).
  void releaseStorage()
  {
    std::vector<int> empty;
    aigIdToVar.swap(empty);
  }

  int varOf(Aig_Obj_t* regular) const
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      return -1;
    return aigIdToVar[id];
  }

  // The one funnel every driver clause goes through, so clause
  // accounting (SATSolver::submittedClauses) cannot be bypassed.
  void addClause(SATSolver::vec_literals& c) { solver->addClause(c); }

  void addBinary(int lit_a, int lit_b)
  {
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(lit_a >> 1, lit_a & 1));
    c.push(SATSolver::mkLit(lit_b >> 1, lit_b & 1));
    addClause(c);
  }

  int ensureTrueVar()
  {
    if (trueVar == -1)
    {
      trueVar = solver->newVar();
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(trueVar, false));
      addClause(unit);
    }
    return trueVar;
  }

  // Tseitin-encode the cone of `regular` (an uncomplemented AIG node)
  // into the solver, allocating variables and definitional clauses for
  // the nodes not encoded yet.
  void ensureEncoded(Aig_Obj_t* regular)
  {
    std::vector<Aig_Obj_t*> work;
    work.push_back(regular);

    while (!work.empty())
    {
      Aig_Obj_t* r = work.back();
      assert(!Aig_IsComplement(r));

      if (varOf(r) != -1)
      {
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsConst1(r))
      {
        setVarOf(r, ensureTrueVar());
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsCi(r))
      {
        setVarOf(r, solver->newVar());
        work.pop_back();
        continue;
      }

      assert(Aig_ObjIsAnd(r));
      Aig_Obj_t* f0 = Aig_ObjFanin0(r);
      Aig_Obj_t* f1 = Aig_ObjFanin1(r);

      const int v0 = varOf(f0);
      const int v1 = varOf(f1);
      if (v0 == -1)
      {
        work.push_back(f0);
        continue;
      }
      if (v1 == -1)
      {
        work.push_back(f1);
        continue;
      }

      // v <-> (l0 & l1)
      const int v = solver->newVar();
      const int l0 = 2 * v0 + (Aig_ObjFaninC0(r) ? 1 : 0);
      const int l1 = 2 * v1 + (Aig_ObjFaninC1(r) ? 1 : 0);

      addBinary(2 * v + 1, l0);
      addBinary(2 * v + 1, l1);

      SATSolver::vec_literals c;
      c.push(SATSolver::mkLit(v, false));
      c.push(SATSolver::mkLit(l0 >> 1, !(l0 & 1)));
      c.push(SATSolver::mkLit(l1 >> 1, !(l1 & 1)));
      addClause(c);

      setVarOf(r, v);
      work.pop_back();
    }
  }
};

} // namespace stp

#endif

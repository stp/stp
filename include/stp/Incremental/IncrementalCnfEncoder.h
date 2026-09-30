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

// The incremental driver's AIG-to-CNF encoder over live ABC AIG nodes,
// extending a solver that already holds
// variables and clauses from earlier check-sats while keeping every
// previously assigned variable id stable. That last property is the
// whole reason this exists instead of ABC's CNF derivation: Cnf_Derive
// and friends are whole-manager, one-shot, and renumber every object,
// and root literals, activation literals and refinement lemmas over old
// variables all depend on the numbering not moving. The cost of the
// trade is encoding quality: whole-manager technology mapping cannot be
// reused here. Recovering XOR and if-then-else cells locally still avoids
// their intermediate variables and per-AND clauses without renumbering.
//
// Everything emitted is a conservative extension (fresh variables and
// definitional clauses), so nothing is ever retracted.

#include "stp/Sat/SATSolver.h"

#include "aig/aig/aig.h"

#include <cassert>
#include <cstdint>
#include <initializer_list>
#include <vector>

namespace stp
{

class IncrementalCnfEncoder
{
  SATSolver* solver;

  // AIG object Id -> CNF variable; -1 = not encoded yet. AIG Ids are
  // dense and only grow within one resettable encoding epoch.
  std::vector<int> aigIdToVar;

  enum class Gate : uint8_t
  {
    And,
    Xor,
    Mux
  };
  // Two bits per AIG id, allocated only for recovered cells. Plain cones
  // need no extra table. A cone can arrive under a different recovery policy
  // later; accounting must still follow the definition actually emitted.
  std::vector<uint8_t> recoveredGates;
  bool recoverCells = true;
  bool recoverXors = true;

  // The variable standing for the AIG's constant-1 node, unit-asserted
  // at creation; -1 until first needed.
  int trueVar = -1;

  // Bumped on every new AIG-to-variable binding and on reset: a consumer
  // deriving anything from the bindings (the refinement adapter's symbol
  // map) caches against this rather than watching individual writes.
  uint64_t generation_ = 0;

  // Reuse the short clause buffer rather than allocating it for every gate.
  SATSolver::vec_literals clause;

  static void inputsOf(Aig_Obj_t* node, Gate gate, Aig_Obj_t* (&inputs)[3])
  {
    if (gate == Gate::Xor)
    {
      const bool found = Aig_ObjRecognizeExor(node, &inputs[0], &inputs[1]);
      assert(found);
      (void)found;
    }
    else if (gate == Gate::Mux)
    {
      inputs[0] = Aig_ObjRecognizeMux(node, &inputs[1], &inputs[2]);
    }
    else
    {
      inputs[0] = Aig_ObjChild0(node);
      inputs[1] = Aig_ObjChild1(node);
    }
  }

  int literalOf(Aig_Obj_t* node) const
  {
    const int var = varOf(Aig_Regular(node));
    assert(var != -1);
    return 2 * var + (Aig_IsComplement(node) ? 1 : 0);
  }

  void emit(std::initializer_list<int> literals)
  {
    clause.clear();
    for (int literal : literals)
      clause.push(SATSolver::mkLit(literal >> 1, literal & 1));
    addClause(clause);
  }

  void setVarOf(Aig_Obj_t* regular, int var, Gate gate = Gate::And)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      aigIdToVar.resize(id + 1, -1);
    aigIdToVar[id] = var;
    if (gate != Gate::And)
    {
      const unsigned byte = id / 4;
      if (byte >= recoveredGates.size())
        recoveredGates.resize(byte + 1, 0);
      recoveredGates[byte] |= static_cast<uint8_t>(gate) << (2 * (id % 4));
    }
    generation_++;
  }

public:
  explicit IncrementalCnfEncoder(SATSolver* solver_) : solver(solver_) {}

  uint64_t generation() const { return generation_; }

  // Only affects new definitions. Existing bindings and their gates survive
  // policy changes, just as they survive assertion retraction.
  void setRecoverCells(bool enabled, bool xorCells = true)
  {
    recoverCells = enabled;
    recoverXors = xorCells;
  }

  // A fresh backend: every binding is void, ids restart.
  void reset(SATSolver* solver_)
  {
    solver = solver_;
    aigIdToVar.clear();
    recoveredGates.clear();
    trueVar = -1;
    generation_++;
  }

  // Additionally return the table's storage (a relief rotation
  // reclaims allocations, not just contents).
  void releaseStorage()
  {
    std::vector<int> empty;
    aigIdToVar.swap(empty);
    std::vector<uint8_t> emptyGates;
    recoveredGates.swap(emptyGates);
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

  void addBinary(int lit_a, int lit_b) { emit({lit_a, lit_b}); }

  int ensureTrueVar()
  {
    if (trueVar == -1)
    {
      trueVar = solver->newVar();
      emit({2 * trueVar});
    }
    return trueVar;
  }

  // Return the actual structural clause count and dependencies of an encoded
  // gate. Live-cone accounting must follow these dependencies rather than
  // the original AND fanins: a recovered cell need not encode its two
  // intermediate ANDs. Either intermediate may still be encoded later as
  // another root, in which case its independent definition remains sound.
  unsigned appendEncodedInputs(Aig_Obj_t* regular,
                               std::vector<Aig_Obj_t*>& pending) const
  {
    assert(varOf(regular) != -1);
    if (Aig_ObjIsConst1(regular))
      return 1;
    if (Aig_ObjIsCi(regular))
      return 0;
    Aig_Obj_t* inputs[3];
    const unsigned id = Aig_ObjId(regular);
    const Gate gate =
        id / 4 < recoveredGates.size()
            ? static_cast<Gate>((recoveredGates[id / 4] >> (2 * (id % 4))) & 3)
            : Gate::And;
    inputsOf(regular, gate, inputs);
    for (unsigned i = 0; i < (gate == Gate::Mux ? 3u : 2u); ++i)
      pending.push_back(Aig_Regular(inputs[i]));
    return gate == Gate::And ? 3u : gate == Gate::Xor ? 4u : 6u;
  }

  // Encode the cone of `regular` (an uncomplemented AIG node)
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
      Aig_Obj_t* inputs[3];
      Gate gate = Gate::And;
      if (recoverCells)
      {
        if (Aig_ObjRecognizeExor(r, &inputs[0], &inputs[1]))
        {
          if (recoverXors)
            gate = Gate::Xor;
        }
        else if (Aig_ObjIsMuxType(r))
          gate = Gate::Mux;
      }
      inputsOf(r, gate, inputs);
      bool ready = true;
      for (unsigned i = 0; i < (gate == Gate::Mux ? 3u : 2u); ++i)
      {
        if (varOf(Aig_Regular(inputs[i])) == -1)
        {
          work.push_back(Aig_Regular(inputs[i]));
          ready = false;
          break;
        }
      }
      if (!ready)
        continue;

      const int v = solver->newVar();
      const int out = 2 * v;
      const int a = literalOf(inputs[0]), b = literalOf(inputs[1]);
      if (gate == Gate::And)
      {
        emit({out ^ 1, a});
        emit({out ^ 1, b});
        emit({out, a ^ 1, b ^ 1});
      }
      else if (gate == Gate::Xor)
      {
        emit({a, b, out ^ 1});
        emit({a ^ 1, b ^ 1, out ^ 1});
        emit({a, b ^ 1, out});
        emit({a ^ 1, b, out});
      }
      else
      {
        const int c = literalOf(inputs[2]);
        // out <-> (a ? b : c), including the two consensus clauses:
        // agreeing arms determine out before the condition is assigned.
        emit({a ^ 1, b ^ 1, out});
        emit({a ^ 1, b, out ^ 1});
        emit({a, c ^ 1, out});
        emit({a, c, out ^ 1});
        emit({b ^ 1, c ^ 1, out});
        emit({b, c, out ^ 1});
      }

      setVarOf(r, v, gate);
      work.pop_back();
    }
  }
};

} // namespace stp

#endif

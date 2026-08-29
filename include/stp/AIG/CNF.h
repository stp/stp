/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

#ifndef STP_AIG_CNF_H
#define STP_AIG_CNF_H

#include <cassert>
#include <cstdint>
#include <iosfwd>
#include <vector>

namespace stp
{

// A CNF formula and the projection back to the circuit it came from.
//
// Clauses live in one flat literal arena with an offsets array beside it, so
// clause i is [lits_[offsets_[i]], lits_[offsets_[i+1]]) -- the layout
// Cnf_Dat_t uses, kept because add_cnf_to_solver() walks it a clause at a
// time and nothing is gained by a different one.
//
// A literal is `2*variable + negated`, again as in Cnf_Dat_t, so `^1` negates
// and `>>1` recovers the variable.
//
// Variables number from 1. Variable 0 does not exist, and that is not a
// convention worth trading away: SATSolver::newVar() hands out 0 first and
// `add(0)` is CaDiCaL's clause terminator, so a literal naming variable 0
// truncates a clause rather than failing. varCount() is one past the highest
// variable used, which is the number of solver variables a consumer has to
// allocate before adding these clauses.
//
// What the class does *not* carry is a map from circuit node to variable.
// Cnf_Dat_t's pVarNums is one int per AIG object and it outlives the
// derivation, held for the whole solve so that a handful of CIs can be looked
// up. Only the inputs and outputs are ever asked about, so only those are
// kept.
class CNF
{
public:
  uint32_t varCount() const { return nVars_; }
  uint64_t clauseCount() const
  {
    return offsets_.empty() ? 0 : offsets_.size() - 1;
  }
  uint64_t literalCount() const { return lits_.size(); }

  const int* clauseBegin(uint64_t i) const { return lits_.data() + offsets_[i]; }
  const int* clauseEnd(uint64_t i) const
  {
    return lits_.data() + offsets_[i + 1];
  }

  // The variable holding the value of combinational input `ordinal`, or of
  // combinational output `ordinal`. Zero means "no variable": an output that
  // was asserted rather than named has none. Zero rather than some positive
  // sentinel because a caller that forgets to check writes out of bounds on a
  // sentinel that is a plausible index, and does not on this one.
  uint32_t ciCount() const { return static_cast<uint32_t>(ciVar_.size()); }
  uint32_t coCount() const { return static_cast<uint32_t>(coVar_.size()); }
  uint32_t varOfCi(uint32_t ordinal) const { return ciVar_[ordinal]; }
  uint32_t varOfCo(uint32_t ordinal) const { return coVar_[ordinal]; }

  // Set when an empty clause was emitted, which is the only way this class
  // says "unsatisfiable before the solver has seen it".
  bool hasEmptyClause() const { return emptyClause_; }

  void writeDimacs(std::ostream& out) const;

  // ---- the sink the AIG's Tseitin writer emits into ----
  //
  // Ordinary member functions rather than an interface: the writer is a
  // template over its sink, so a DIMACS or straight-to-solver sink is a
  // different type with these same names and costs no indirection.

  // Exact counts, not estimates -- the writer's first pass produces them and
  // end() checks that the second pass emitted precisely that many.
  void begin(uint32_t nVars, uint64_t nClauses, uint64_t nLiterals,
             uint32_t nCi, uint32_t nCo);
  void mapCi(uint32_t ordinal, uint32_t var) { ciVar_[ordinal] = var; }
  void mapCo(uint32_t ordinal, uint32_t var) { coVar_[ordinal] = var; }

  void clause(int a)
  {
    lits_.push_back(a);
    offsets_.push_back(lits_.size());
  }
  void clause(int a, int b)
  {
    lits_.push_back(a);
    lits_.push_back(b);
    offsets_.push_back(lits_.size());
  }
  void clause(int a, int b, int c)
  {
    lits_.push_back(a);
    lits_.push_back(b);
    lits_.push_back(c);
    offsets_.push_back(lits_.size());
  }
  void emptyClause()
  {
    emptyClause_ = true;
    offsets_.push_back(lits_.size());
  }
  void end();

private:
  std::vector<int> lits_;
  std::vector<uint64_t> offsets_;
  std::vector<uint32_t> ciVar_;
  std::vector<uint32_t> coVar_;
  uint32_t nVars_ = 1;
  uint64_t expectedClauses_ = 0;
  uint64_t expectedLiterals_ = 0;
  bool emptyClause_ = false;
};

} // namespace stp

#endif

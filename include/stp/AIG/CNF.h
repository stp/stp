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
#include <cstddef>
#include <iosfwd>
#include <utility>
#include <vector>

namespace stp
{

// A CNF formula and the projection back to the circuit it came from. The one
// currency the CNF generators hand back, whichever of them ran.
//
// Clauses live in one flat literal arena, walked a clause at a time. A
// literal is `2*variable + negated`, so `^1` negates and `>>1` recovers the
// variable. That is Cnf_Dat_t's layout and encoding, and keeping it is what
// lets an ABC-generated formula be adopted rather than copied -- see adopt()
// below.
//
// The index into the arena is one *byte* per clause, not an offset. An
// offsets array costs eight bytes a clause and on a 13M-clause formula that
// was 100 MB of a 233 MB CNF -- more than the literals it indexed. Lengths
// fit in a byte for every clause the Tseitin writer emits except the n-ary
// ANDs, and those escape through longLens_. What that costs is random
// access: a clause can only be reached by walking to it. Every consumer
// already walked in order, so the API is a forward cursor -- see clauses().
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
// kept -- varOfCi()/varOfCo() below, filled by whoever built the formula.
//
// Move-only. It owns either its own arena or somebody else's, and neither is
// worth duplicating by accident.
class CNF
{
public:
  CNF() = default;
  ~CNF() { discard(); }
  CNF(CNF&& o) noexcept { steal(o); }
  CNF& operator=(CNF&& o) noexcept
  {
    if (this != &o)
    {
      discard();
      steal(o);
    }
    return *this;
  }
  CNF(const CNF&) = delete;
  CNF& operator=(const CNF&) = delete;

  uint32_t varCount() const { return nVars_; }
  uint64_t clauseCount() const { return nClauses_; }
  uint64_t literalCount() const { return nLiterals_; }

  // One pass over the clauses, in the order they were emitted:
  //
  //   for (CNF::ClauseCursor c = cnf.clauses(); c.next(); )
  //     for (const int* p = c.begin(); p < c.end(); p++) ...
  //
  // begin() and end() are the current clause and are only meaningful after
  // next() has returned true. The cursor holds pointers into the CNF, so it
  // does not outlive it, and it does not survive a further clause() either.
  class ClauseCursor
  {
  public:
    bool next()
    {
      if (left_ == 0)
        return false;
      left_--;

      if (adopted_ != nullptr)
      {
        // nClauses+1 pointers, so the next one is this clause's end.
        begin_ = adopted_[0];
        end_ = adopted_[1];
        adopted_++;
        return true;
      }

      begin_ = end_;
      uint64_t len = *lens_++;
      if (len == longMarker)
        len = *longLens_++;
      end_ = begin_ + len;
      return true;
    }

    const int* begin() const { return begin_; }
    const int* end() const { return end_; }
    size_t size() const { return static_cast<size_t>(end_ - begin_); }

  private:
    friend class CNF;

    const int* const* adopted_ = nullptr;
    const uint8_t* lens_ = nullptr;
    const uint64_t* longLens_ = nullptr;
    const int* begin_ = nullptr;
    const int* end_ = nullptr;
    uint64_t left_ = 0;
  };

  ClauseCursor clauses() const
  {
    ClauseCursor c;
    c.left_ = nClauses_;
    if (adopted_ != nullptr)
      c.adopted_ = adopted_;
    else
    {
      c.lens_ = lens_.data();
      c.longLens_ = longLens_.data();
      c.begin_ = c.end_ = lits_.data();
    }
    return c;
  }

  // The variable holding the value of combinational input `ordinal`, or of
  // combinational output `ordinal`. Zero means "no variable": an input the
  // formula never mentions has none, and neither does an output that was
  // asserted rather than named. Zero rather than some positive sentinel
  // because a caller that forgets to check writes out of bounds on a sentinel
  // that is a plausible index, and does not on this one.
  uint32_t ciCount() const { return static_cast<uint32_t>(ciVar_.size()); }
  uint32_t coCount() const { return static_cast<uint32_t>(coVar_.size()); }
  uint32_t varOfCi(uint32_t ordinal) const
  {
    assert(ordinal < ciVar_.size());
    return ciVar_[ordinal];
  }
  uint32_t varOfCo(uint32_t ordinal) const
  {
    assert(ordinal < coVar_.size());
    return coVar_[ordinal];
  }

  // Set when an empty clause was emitted, which is the only way this class
  // says "unsatisfiable before the solver has seen it".
  bool hasEmptyClause() const { return emptyClause_; }

  void writeDimacs(std::ostream& out) const;

  // Give the formula back now rather than at the end of the scope. Worth
  // saying explicitly where the next thing to run is the SAT search, which
  // wants the memory this is holding.
  void clear() { discard(); }

  // ---- the sink a generator that builds its own arena emits into ----
  //
  // Ordinary member functions rather than an interface: the AIG's Tseitin
  // writer is a template over its sink, so a DIMACS or straight-to-solver
  // sink is a different type with these same names and costs no indirection.

  // Exact counts, not estimates -- the writer's first pass produces them and
  // end() checks that the second pass emitted precisely that many.
  void begin(uint32_t nVars, uint64_t nClauses, uint64_t nLiterals,
             uint32_t nCi, uint32_t nCo);
  void mapCi(uint32_t ordinal, uint32_t var) { ciVar_[ordinal] = var; }
  void mapCo(uint32_t ordinal, uint32_t var) { coVar_[ordinal] = var; }

  void clause(int a)
  {
    lits_.push_back(a);
    closeClause();
  }
  void clause(int a, int b)
  {
    lits_.push_back(a);
    lits_.push_back(b);
    closeClause();
  }
  void clause(int a, int b, int c)
  {
    lits_.push_back(a);
    lits_.push_back(b);
    lits_.push_back(c);
    closeClause();
  }
  // A clause of any length, for the n-ary ANDs: a query's top-level
  // conjunction reaches a thousand leaves, so this one cannot be an overload
  // set over fixed arities like the three above.
  void clause(const int* lits, size_t n)
  {
    lits_.insert(lits_.end(), lits, lits + n);
    closeClause();
  }
  void emptyClause()
  {
    emptyClause_ = true;
    closeClause();
  }
  void end();

  // ---- taking over a formula built elsewhere ----

  // Adopt a clause store this class did not build, without copying it. The
  // ABC generators already produce exactly this layout -- an arena of
  // literals with an array of nClauses+1 pointers indexing it -- so the whole
  // seam between them and here is the projection of the CI and CO variables,
  // filled with mapCi()/mapCo() afterwards.
  //
  // `release(owner)` is called when this CNF dies. It is a function pointer
  // rather than a std::function so that this header stays free of the type it
  // is adopting: the AIG package must not learn what a Cnf_Dat_t is.
  void adopt(void* owner, void (*release)(void*), const int* const* clauses,
             uint64_t nClauses, uint64_t nLiterals, uint32_t nVars,
             uint32_t nCi, uint32_t nCo);

private:
  // A lens_ entry of this value says the length is the next unread entry of
  // longLens_ instead. 255 rather than 0, because 0 is a length a clause
  // really has: the empty clause is the one that says "unsatisfiable".
  //
  // constexpr, not const: the cursor compares against it, which odr-uses a
  // const member and then wants an out-of-line definition. A constexpr
  // static member is implicitly inline in C++17.
  static constexpr uint8_t longMarker = 255;

  void closeClause()
  {
    const uint64_t len = lits_.size() - nLiterals_;
    if (len < longMarker)
      lens_.push_back(static_cast<uint8_t>(len));
    else
    {
      lens_.push_back(longMarker);
      longLens_.push_back(len);
    }
    ++nClauses_;
    nLiterals_ = lits_.size();
  }
  void discard();
  void steal(CNF& o);

  // Ours, when we built it. One lens_ byte per clause; longLens_ holds, in
  // clause order, the lengths of the clauses too long to fit in one.
  std::vector<int> lits_;
  std::vector<uint8_t> lens_;
  std::vector<uint64_t> longLens_;

  // Somebody else's, when we adopted it. Non-null selects it over the
  // vectors above; the two stores are never both populated.
  const int* const* adopted_ = nullptr;
  void* owner_ = nullptr;
  void (*release_)(void*) = nullptr;

  std::vector<uint32_t> ciVar_;
  std::vector<uint32_t> coVar_;
  uint64_t nClauses_ = 0;
  uint64_t nLiterals_ = 0;
  uint64_t expectedClauses_ = 0;
  uint64_t expectedLiterals_ = 0;
  uint32_t nVars_ = 1;
  bool emptyClause_ = false;
};

} // namespace stp

#endif

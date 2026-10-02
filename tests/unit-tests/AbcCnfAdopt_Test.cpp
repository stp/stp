// SPDX-License-Identifier: MIT
//
// abcCnfVariablesAllocated() is what stands between a generator that named a
// variable it never allocated and a SAT backend that would index its arrays
// with it. The condition it rejects arises inside ABC and only on inputs
// large enough to wrap a 16-bit counter, so it cannot be reached from a query
// file deterministically -- see the report for the one that does reach it.
// Build the arenas here instead, in the exact layout Cnf_Dat_t uses.
#include "stp/ToSat/AbcCnfAdopt.h"

#include <gtest/gtest.h>

#include <vector>

namespace
{

// A Cnf_Dat_t over a literal arena the caller owns. Only the four fields the
// predicate reads are filled; nothing here is freed through Cnf_DataFree,
// which would expect ABC's own allocations.
class Arena
{
  std::vector<int> lits;
  std::vector<int*> clauses;
  Cnf_Dat_t data;

public:
  Arena(std::vector<int> literals, int nVars) : lits(std::move(literals))
  {
    clauses.push_back(lits.data());
    // Zero the rest: the predicate reads four fields, and a later reader of
    // a fifth should not get whatever was on the stack.
    data = Cnf_Dat_t{};
    data.nVars = nVars;
    data.nLiterals = (int)lits.size();
    data.nClauses = 1;
    data.pClauses = clauses.data();
  }
  const Cnf_Dat_t* cnf() const { return &data; }
};

// ABC's literal encoding, so the test says what it means rather than
// spelling out the arithmetic.
int lit(int var, int negated)
{
  return Abc_Var2Lit(var, negated);
}

TEST(AbcCnfVariablesAllocated, AcceptsEveryVariableBelowTheCount)
{
  // Variables number from 1 and nVars is one past the highest, so the
  // largest statable variable is nVars - 1. Both polarities of it.
  Arena a({lit(1, 0), lit(3, 1), lit(4, 0), lit(4, 1)}, 5);
  EXPECT_TRUE(stp::abcCnfVariablesAllocated(a.cnf()));
}

TEST(AbcCnfVariablesAllocated, AcceptsAnEmptyArena)
{
  Arena a({}, 1);
  EXPECT_TRUE(stp::abcCnfVariablesAllocated(a.cnf()));
}

// What Abc_Var2Lit(-1, c) evaluates to, spelled out rather than called.
// ABC marks an object its mapping gave no variable with -1, and in a build
// with assertions off -- which is how the archive STP links is built --
// Abc_Var2Lit happily shifts it, giving -2 for a positive literal and -1 for
// a negated one. Calling it here would instead trip its own
// `assert(Var >= 0)`, and writing the shift out in STP's own code would be
// the left shift of a negative value that UBSan reports.
const int kNoVariablePositive = -2;
const int kNoVariableNegated = -1;

TEST(AbcCnfVariablesAllocated, RejectsAbcsNoVariableMarker)
{
  // This is the real failure: `(*pLit) >> 1` on either of these gives
  // 0xFFFFFFFF, which is what the assertion in add_cnf_to_solver reported.
  EXPECT_FALSE(stp::abcCnfVariablesAllocated(
      Arena({lit(2, 0), kNoVariablePositive}, 5).cnf()));
  EXPECT_FALSE(stp::abcCnfVariablesAllocated(
      Arena({lit(2, 0), kNoVariableNegated}, 5).cnf()));
}

TEST(AbcCnfVariablesAllocated, RejectsAVariableAtOrAboveTheCount)
{
  // Not a shape ABC has been seen to produce, but the predicate's job is the
  // range rather than the marker: nVars is one past the highest variable, so
  // nVars itself is already out.
  EXPECT_FALSE(
      stp::abcCnfVariablesAllocated(Arena({lit(1, 0), lit(5, 0)}, 5).cnf()));
  EXPECT_FALSE(
      stp::abcCnfVariablesAllocated(Arena({lit(1, 0), lit(99, 1)}, 5).cnf()));
}

TEST(AbcCnfVariablesAllocated, LooksPastTheFirstClause)
{
  // The arena is flat and the predicate walks nLiterals, not clauses, so a
  // marker in the last clause of a long formula is caught like any other.
  std::vector<int> lits;
  for (int i = 0; i < 4096; i++)
    lits.push_back(lit(1 + (i % 4), i & 1));
  EXPECT_TRUE(stp::abcCnfVariablesAllocated(Arena(lits, 5).cnf()));
  lits.push_back(kNoVariableNegated);
  EXPECT_FALSE(stp::abcCnfVariablesAllocated(Arena(lits, 5).cnf()));
}

} // namespace

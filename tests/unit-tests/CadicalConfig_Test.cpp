// Guards the --cadical-config plumbing: a configuration profile must never
// change the (un)satisfiability verdict. Only built when USE_CADICAL is on.
#include <gtest/gtest.h>
#include "stp/Sat/Cadical.h"
#include <cstdlib>

using stp::Cadical;
using vec = stp::SATSolver::vec_literals;

namespace {
void addClause2(Cadical& s, int a, int b)
{
  vec c;
  c.push(stp::SATSolver::mkLit(abs(a), a < 0));
  c.push(stp::SATSolver::mkLit(abs(b), b < 0));
  s.addClause(c);
}
void addUnit(Cadical& s, int a)
{
  vec c;
  c.push(stp::SATSolver::mkLit(abs(a), a < 0));
  s.addClause(c);
}
} // namespace

// (x) & (~x) is UNSAT under every configuration profile.
TEST(CadicalConfig, UnsatVerdictStableAcrossConfigs)
{
  for (const char* cfg : {"", "unsat", "sat", "default"})
  {
    Cadical s(cfg);
    const uint32_t x = s.newVar();
    addUnit(s, x);
    addUnit(s, -(int)x);
    bool to = false;
    EXPECT_FALSE(s.solve(to)) << "cfg=" << cfg;
    EXPECT_FALSE(to) << "cfg=" << cfg;
  }
}

// (x | y) & (~x) is SAT (y must be true) under every configuration profile.
TEST(CadicalConfig, SatVerdictStableAcrossConfigs)
{
  for (const char* cfg : {"", "unsat", "sat", "default"})
  {
    Cadical s(cfg);
    const uint32_t x = s.newVar();
    const uint32_t y = s.newVar();
    addClause2(s, x, y);
    addUnit(s, -(int)x);
    bool to = false;
    ASSERT_TRUE(s.solve(to)) << "cfg=" << cfg;
    EXPECT_EQ(s.modelValue(y), s.true_literal()) << "cfg=" << cfg;
  }
}

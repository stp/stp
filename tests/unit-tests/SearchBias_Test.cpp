// Guards --search-bias. A bias only selects heuristics, so whichever one is
// asked for, the sat/unsat verdict has to come out the same: that is the only
// way this feature could do damage. Every backend compiled into this build is
// checked, including one that doesn't implement the bias at all, since
// reporting that honestly is what drives the warning STP prints.
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SearchBias.h"
#include <cstdlib>
#include <functional>
#include <gtest/gtest.h>
#include <memory>

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif
#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif

using stp::SATSolver;
using stp::SearchBias;

namespace
{

using SolverFactory = std::function<std::unique_ptr<SATSolver>()>;

const SearchBias all_biases[] = {SearchBias::NONE, SearchBias::SAT,
                                 SearchBias::UNSAT};

void addUnit(SATSolver& s, uint32_t var, bool negated)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(var, negated));
  s.addClause(c);
}

void addBinary(SATSolver& s, uint32_t a, bool a_neg, uint32_t b, bool b_neg)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(a, a_neg));
  c.push(SATSolver::mkLit(b, b_neg));
  s.addClause(c);
}

// (x) & (~x) is unsatisfiable under every bias.
void checkUnsatVerdict(const SolverFactory& make, const char* name)
{
  for (const SearchBias bias : all_biases)
  {
    std::unique_ptr<SATSolver> s = make();
    s->setSearchBias(bias);

    const uint32_t x = s->newVar();
    addUnit(*s, x, false);
    addUnit(*s, x, true);

    bool timed_out = false;
    EXPECT_FALSE(s->solve(timed_out))
        << name << " bias=" << stp::searchBiasName(bias);
    EXPECT_FALSE(timed_out) << name << " bias=" << stp::searchBiasName(bias);
  }
}

// (x | y) & (~x) is satisfiable under every bias, and only with y true.
void checkSatVerdict(const SolverFactory& make, const char* name)
{
  for (const SearchBias bias : all_biases)
  {
    std::unique_ptr<SATSolver> s = make();
    s->setSearchBias(bias);

    const uint32_t x = s->newVar();
    const uint32_t y = s->newVar();
    addBinary(*s, x, false, y, false);
    addUnit(*s, x, true);

    bool timed_out = false;
    ASSERT_TRUE(s->solve(timed_out))
        << name << " bias=" << stp::searchBiasName(bias);
    EXPECT_EQ(s->modelValue(y), s->true_literal())
        << name << " bias=" << stp::searchBiasName(bias);
  }
}

} // namespace

#ifdef USE_MINISAT
TEST(SearchBias, MinisatVerdictsAreStable)
{
  const SolverFactory make = [] {
    return std::unique_ptr<SATSolver>(new stp::MinisatCore);
  };
  checkUnsatVerdict(make, "minisat");
  checkSatVerdict(make, "minisat");
}

// Minisat has nothing to bias, and has to say so rather than silently drop
// the request: STP warns on the back of this.
TEST(SearchBias, MinisatReportsNoSupport)
{
  stp::MinisatCore s;
  EXPECT_FALSE(s.setSearchBias(SearchBias::SAT));
  EXPECT_FALSE(s.setSearchBias(SearchBias::UNSAT));
}
#endif

#ifdef USE_CADICAL
TEST(SearchBias, CadicalVerdictsAreStable)
{
  const SolverFactory make = [] {
    return std::unique_ptr<SATSolver>(new stp::Cadical);
  };
  checkUnsatVerdict(make, "cadical");
  checkSatVerdict(make, "cadical");
}

// Cadical has a named configuration for each direction.
TEST(SearchBias, CadicalAcceptsBothDirections)
{
  {
    stp::Cadical s;
    EXPECT_TRUE(s.setSearchBias(SearchBias::SAT));
  }
  {
    stp::Cadical s;
    EXPECT_TRUE(s.setSearchBias(SearchBias::UNSAT));
  }
}
#endif

#ifdef USE_CRYPTOMINISAT
TEST(SearchBias, CryptoMiniSatVerdictsAreStable)
{
  const SolverFactory make = [] {
    return std::unique_ptr<SATSolver>(new stp::CryptoMiniSat5(1));
  };
  checkUnsatVerdict(make, "cryptominisat");
  checkSatVerdict(make, "cryptominisat");
}

// CryptoMiniSat can be pushed towards unsatisfiable instances, but its
// defaults are already the satisfiable-leaning end of what it offers.
TEST(SearchBias, CryptoMiniSatOnlyBiasesTowardsUnsat)
{
  {
    stp::CryptoMiniSat5 s(1);
    EXPECT_TRUE(s.setSearchBias(SearchBias::UNSAT));
  }
  {
    stp::CryptoMiniSat5 s(1);
    EXPECT_FALSE(s.setSearchBias(SearchBias::SAT));
  }
}
#endif

#include "LraHighsCuts.h"
#include "NumberBudget.h"
#include <iostream>
#include <random>
#include <stdexcept>
using namespace stp::lra;
namespace
{
void require(bool ok, const char* message)
{
  if (!ok)
    throw std::runtime_error(message);
}
ExactRational q(std::int64_t n)
{
  return ExactRational(n);
}
ExactRational value(const HighsProofRow& row,
                    const std::vector<ExactRational>& point)
{
  auto result = q(0);
  for (const auto& t : row.terms)
    result += t.coefficient * point[t.col];
  return result;
}
void test()
{
  NumberBudget budget({100000, 200000, 100000000, 1000000});
  NumberOperationScope scope(budget);
  std::vector<HighsProofRow> rows{{{{0, q(2)}}, q(1)}};
  auto cut = certifyHighsCgCut(rows, {true}, {{0, q(1) / q(2)}});
  require(cut && cut->terms[0].coefficient == q(1) && cut->rhs == q(0),
          "binary rounding missing");
  require(!certifyHighsCgCut(rows, {false}, {{0, q(1) / q(2)}}),
          "unbounded continuous residual accepted");
  require(!certifyHighsCgCut(rows, {true}, {{0, q(-1)}}),
          "negative inequality weight accepted");
  require(!certifyHighsCgCut(rows, {true}, {{1, q(1)}}),
          "unregistered source accepted");
  require(!certifyHighsCgCut(rows, {true}, {{0, q(1)}}, false,
                             [] { return false; }),
          "expired derivation accepted");
  rows = {{{{0, q(1)}}, q(1), false, true}};
  cut = certifyHighsCgCut(rows, {true}, {{0, q(1)}});
  require(cut && cut->rhs == q(0), "strict integer endpoint lost");
  rows = {{{{0, q(2)}, {1, q(1)}}, q(3)}, {{{1, q(-1)}}, q(-2)}};
  cut = certifyHighsCgCut(rows, {true, false}, {{0, q(1) / q(2)}});
  require(cut && cut->rhs == q(0), "bounded continuous projection failed");
  // The floating proposal cannot cancel this tiny residual exactly. Without
  // an endpoint for that continuous variable the proof must be rejected.
  rows = {{{{0, q(1)}, {1, q(1) / q(1000000000000000000LL)}}, q(0)}};
  require(!certifyHighsCgCut(rows, {true, false}, {{0, q(1)}}),
          "tiny residual dropped");
  rows = {{{{0, q(2)}}, q(1)}};
  cut = certifyHighsSplitCut(rows, {true}, {{0, q(1)}}, 0, {false});
  require(cut && cut->rhs == q(0) && cut->terms[0].coefficient.sign() > 0,
          "split cut for a binary upper bound missing");
  require(!certifyHighsSplitCut(rows, {false}, {{0, q(1)}}, 0, {false}),
          "split used an unproved integer domain");
  require(!certifyHighsSplitCut(rows, {true}, {{1, q(1)}}, 0, {false}),
          "split used an unregistered row");
  require(!certifyHighsSplitCut(rows, {true}, {{0, q(1)}}, 0, {false},
                                [] { return false; }),
          "split ignored its deadline");
  // Exhaustive independent point oracle checks negative coefficients,
  // complementation, strict inequalities and arbitrary rational weights.
  std::mt19937 rng(716921);
  for (unsigned trial = 0; trial < 160; ++trial)
  {
    rows.clear();
    for (unsigned r = 0; r < 4; ++r)
    {
      HighsProofRow row;
      row.rhs = q(static_cast<int>(rng() % 15) - 7) / q(3);
      row.strict = (trial % 3) == 0;
      for (std::size_t c = 0; c < 3; ++c)
        row.terms.push_back({c, q(static_cast<int>(rng() % 11) - 5) / q(2)});
      rows.push_back(std::move(row));
    }
    // Bound the one continuous variable for projection; binary coordinates
    // are enumerated, not rounded by the test oracle.
    rows.push_back({{{2, q(1)}}, q(2)});
    rows.push_back({{{2, q(-1)}}, q(2)});
    std::vector<std::pair<std::size_t, ExactRational>> weights;
    for (std::size_t r = 0; r < 4; ++r)
      weights.emplace_back(r, q(static_cast<int>(rng() % 7)) / q(3));
    for (bool complement : {false, true})
    {
      cut = certifyHighsCgCut(rows, {true, true, false}, weights, complement);
      require(cut.has_value(), "valid projected derivation refused");
      const auto split =
          certifyHighsSplitCut(rows, {true, true, false}, weights, 0,
                               {complement, complement, complement});
      for (int x = 0; x <= 1; ++x)
        for (int y = 0; y <= 1; ++y)
          for (int z = -8; z <= 8; ++z)
          {
            std::vector<ExactRational> point{q(x), q(y), q(z) / q(4)};
            bool feasible = true;
            for (const auto& row : rows)
              feasible =
                  feasible && (row.strict ? value(row, point) < row.rhs
                                          : value(row, point) <= row.rhs);
            if (feasible)
            {
              require(value(*cut, point) <= cut->rhs,
                      "cut excludes a feasible exact point");
              if (split)
                require(value(*split, point) <= split->rhs,
                        "split excludes a feasible exact point");
            }
          }
    }
  }
}
} // namespace
int main()
{
  try
  {
    test();
    std::cout << "exact root cut reconstruction passed\n";
  }
  catch (const std::exception& e)
  {
    std::cerr << e.what() << '\n';
    return 1;
  }
}

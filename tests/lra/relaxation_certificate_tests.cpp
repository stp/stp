#include "LraRelaxation.h"
#include <cmath>
#include <iostream>
#include <limits>
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
void tests()
{
  NumberBudget budget({100000, 200000, 100000000, 1000000});
  NumberOperationScope scope(budget);
  const auto nil = q(0), one = q(1), two = q(2);
  const auto epsilon = one / ExactRational(std::uint64_t{1} << 54);
  std::vector<RelaxationBox> box{{nil, two}};
  // The rounded LP sees x=1. The exact equation has x<1. A bound of 1
  // obtained by assuming floating cancellation would be unsound.
  std::vector<RelaxationRow> rows{{{{0, one + epsilon}}, one, true}};
  auto bound = certifyRelaxationLower(rows, box, {{0, one}}, {1.0});
  require(bound && *bound < one && *bound <= one / (one + epsilon),
          "rounded cancellation was trusted");
  require(!certifyRelaxationLower(rows, box, {{0, one}}, {}),
          "accepted wrong dimension");
  require(!certifyRelaxationLower(rows, box, {{0, one}},
                                  {std::numeric_limits<double>::infinity()}),
          "accepted infinity");
  require(!certifyRelaxationLower(rows, box, {{0, one}},
                                  {std::numeric_limits<double>::quiet_NaN()}),
          "accepted NaN");
  box[0].upper.reset();
  require(!certifyRelaxationLower(rows, box, {{0, one}}, {1.0}),
          "accepted an unbounded residual");
  box[0].upper = two;
  rows[0] = {{{0, one}}, one, false};
  bound = certifyRelaxationLower(rows, box, {{0, one}}, {1.0});
  require(bound && *bound == nil, "positive inequality dual was used");
  bound = certifyRelaxationLower(rows, box, {{0, -one}}, {-1.0});
  require(bound && *bound == -one, "negative inequality dual rejected");
  require(exactDyadic(std::numeric_limits<double>::denorm_min()).sign() > 0,
          "lost subnormal weight");
  require(exactDyadic(-0.0).isZero(), "negative zero conversion");

  // Independent feasible-point oracle: arbitrary proposals (including wrong
  // signs and noncancelling dyadics) must never bound above any feasible point.
  std::mt19937 random(63729);
  box = {{-two, two}, {-two, two}};
  for (unsigned trial = 0; trial < 200; ++trial)
  {
    auto coefficient = [&]()
    { return q(static_cast<int>(random() % 15) - 7) / q(11); };
    rows.clear();
    std::vector<double> weights;
    for (unsigned row = 0; row < 4; ++row)
    {
      rows.push_back({{{0, coefficient()}, {1, coefficient()}},
                      q(static_cast<int>(random() % 4)),
                      false});
      weights.push_back(std::ldexp(
          static_cast<double>(static_cast<int>(random() % 31) - 15), -3));
    }
    const std::vector<RelaxationTerm> objective{{0, coefficient()},
                                                {1, coefficient()}};
    bound = certifyRelaxationLower(rows, box, objective, weights);
    require(bound.has_value(), "bounded proposal refused");
    for (int x = -4; x <= 4; ++x)
      for (int y = -4; y <= 4; ++y)
      {
        const std::vector<ExactRational> point{q(x) / two, q(y) / two};
        bool feasible = true;
        for (const auto& row : rows)
        {
          auto lhs = nil;
          for (const auto& term : row.terms)
            lhs += term.coefficient * point[term.var];
          feasible = feasible && lhs <= row.rhs;
        }
        if (!feasible)
          continue;
        auto value = nil;
        for (const auto& term : objective)
          value += term.coefficient * point[term.var];
        require(*bound <= value, "certificate excludes a feasible exact point");
      }
  }
#ifdef STP_HAVE_HIGHS
  rows = {{{{0, one}}, nil, false}, {{{0, -one}}, -one, false}};
  box = {{nil, two}};
  require(probeRelaxation(rows, box, 1.0).refuted,
          "infeasible slack LP not certified");
  rows.pop_back();
  require(!probeRelaxation(rows, box, 1.0).refuted,
          "feasible slack LP refuted");
  require(!probeRelaxation(rows, box, 0.0).refuted,
          "expired LP produced refutation");
  {
    RelaxationLp lp(rows, box);
    require(!lp.minimize({{0, one}}, 1.0, 1.0) && lp.screened == 1,
            "unhelpful objective was not screened");
    require(lp.values().size() == box.size(),
            "screening discarded primal advice");
    require(lp.minimize({{0, one}}, 1.0).has_value(),
            "unscreened certificate missing");
  }
  // Force a non-optimal run through an iteration budget, without depending
  // on a machine's wall-clock speed. The all-zero point is independently
  // feasible; every returned partial certificate must respect it.
  box.assign(40, {-one, one});
  rows.clear();
  for (unsigned i = 0; i < 60; ++i)
  {
    RelaxationRow row;
    row.rhs = q(1);
    for (unsigned j = 0; j < box.size(); ++j)
      row.terms.push_back({j, q(static_cast<int>(random() % 15) - 7)});
    rows.push_back(std::move(row));
  }
  std::vector<RelaxationTerm> cost;
  for (unsigned i = 0; i < box.size(); ++i)
    cost.push_back({i, one});
  RelaxationLp partial_lp(rows, box, {true, 0U});
  const auto partial_bound = partial_lp.minimize(cost, 1.0);
  require(partial_bound && *partial_bound <= nil &&
              partial_lp.partial_certificates == 1,
          "unfinished LP did not yield an exactly valid partial certificate");
  RelaxationLp complete_only(rows, box, {false, 0U});
  require(!complete_only.minimize(cost, 1.0),
          "complete-only policy accepted unfinished LP");
  require(complete_only.search_seconds > 0,
          "abandoned search time was omitted");
  RelaxationLp screened_partial(rows, box, {true, 0U});
  require(!screened_partial.minimize(cost, 1.0, 1000.0) &&
              screened_partial.screened == 1,
          "unhelpful partial residual was not screened");
#endif
}
} // namespace
int main()
{
  try
  {
    tests();
    std::cout << "Exact relaxation certificate checks passed\n";
  }
  catch (const std::exception& e)
  {
    std::cerr << e.what() << '\n';
    return 1;
  }
}

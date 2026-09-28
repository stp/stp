#include "LraRelaxation.h"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdlib>
#include <limits>
#ifdef STP_HAVE_HIGHS
#include <interfaces/highs_c_api.h>
#endif

namespace stp::lra
{
ExactRational exactDyadic(double value)
{
  if (value == 0.0)
    return ExactRational();
  if (!std::isfinite(value))
    throw NumberFailure(NumberFailureKind::RangeError, "nonfinite LP weight");
  int exponent = 0;
  const double fraction = std::frexp(value, &exponent);
  auto result =
      ExactRational(static_cast<std::int64_t>(std::ldexp(fraction, 53)));
  exponent -= 53;
  while (exponent != 0)
  {
    const int shift = std::min(62, std::abs(exponent));
    const ExactRational power(std::uint64_t{1} << static_cast<unsigned>(shift));
    if (exponent > 0)
    {
      result *= power;
      exponent -= shift;
    }
    else
    {
      result /= power;
      exponent += shift;
    }
  }
  return result;
}

double approximate(const ExactRational& value)
{
  if (const auto small = value.trySmall())
    return static_cast<double>(static_cast<long double>(small->numerator) /
                               static_cast<long double>(small->denominator));
  const auto n = value.numeratorDecimal(), d = value.denominatorDecimal();
  return static_cast<double>(std::strtold(n.c_str(), nullptr) /
                             std::strtold(d.c_str(), nullptr));
}

std::optional<ExactRational>
certifyRelaxationLower(const std::vector<RelaxationRow>& rows,
                       const std::vector<RelaxationBox>& box,
                       const std::vector<RelaxationTerm>& objective,
                       const std::vector<double>& weights)
{
  if (weights.size() != rows.size())
    return std::nullopt;
  std::vector<ExactRational> residual(box.size());
  for (const auto& term : objective)
  {
    if (term.var >= box.size())
      return std::nullopt;
    residual[term.var] += term.coefficient;
  }
  ExactRational bound;
  for (std::size_t i = 0; i < rows.size(); ++i)
  {
    if (!std::isfinite(weights[i]))
      return std::nullopt;
    // z <= 0, A*x <= b implies z*A*x >= z*b. Equalities allow either sign.
    const auto weight =
        exactDyadic(rows[i].equality ? weights[i] : std::min(0.0, weights[i]));
    if (weight.isZero())
      continue;
    bound += weight * rows[i].rhs;
    for (const auto& term : rows[i].terms)
    {
      if (term.var >= box.size())
        return std::nullopt;
      residual[term.var] -= weight * term.coefficient;
    }
  }
  for (std::size_t v = 0; v < box.size(); ++v)
  {
    if (residual[v].isZero())
      continue;
    const auto& endpoint = residual[v].sign() > 0 ? box[v].lower : box[v].upper;
    if (!endpoint)
      return std::nullopt;
    bound += residual[v] * *endpoint;
  }
  return bound;
}

RelaxationLp::RelaxationLp(const std::vector<RelaxationRow>& rows,
                           const std::vector<RelaxationBox>& box,
                           RelaxationOptions options)
    : rows_(rows), box_(box), partial_(options.partial)
{
#ifdef STP_HAVE_HIGHS
  if (box.empty() || box.size() > 100000 || rows.size() > 200000)
    return;
  std::vector<double> lower, upper, rl, ru, value;
  std::vector<HighsInt> start{0}, index;
  auto finite = [](const ExactRational& q)
  {
    const double d = approximate(q);
    return std::isfinite(d) && std::abs(d) < 1e19;
  };
  for (const auto& b : box)
  {
    if (!b.lower || !b.upper || *b.lower > *b.upper || !finite(*b.lower) ||
        !finite(*b.upper))
      return;
    lower.push_back(approximate(*b.lower));
    upper.push_back(approximate(*b.upper));
  }
  for (const auto& row : rows)
  {
    if (!finite(row.rhs))
      return;
    ru.push_back(approximate(row.rhs));
    rl.push_back(row.equality ? ru.back()
                              : -std::numeric_limits<double>::infinity());
    for (const auto& term : row.terms)
    {
      if (term.var >= box.size() || !finite(term.coefficient))
        return;
      index.push_back(static_cast<HighsInt>(term.var));
      value.push_back(approximate(term.coefficient));
    }
    if (value.size() > 4000000)
      return;
    start.push_back(static_cast<HighsInt>(value.size()));
  }
  engine_ = Highs_create();
  if (!engine_)
    return;
  Highs_setBoolOptionValue(engine_, "output_flag", 0);
  Highs_setIntOptionValue(engine_, "threads", 1);
  Highs_setStringOptionValue(engine_, "solver", "simplex");
  if (options.iteration_limit)
    Highs_setIntOptionValue(
        engine_, "simplex_iteration_limit",
        static_cast<HighsInt>(std::min(*options.iteration_limit, 2147483647U)));
  std::vector<double> cost(box.size(), 0.0);
  usable_ = Highs_passLp(engine_, static_cast<HighsInt>(box.size()),
                         static_cast<HighsInt>(rows.size()),
                         static_cast<HighsInt>(value.size()),
                         kHighsMatrixFormatRowwise, kHighsObjSenseMinimize, 0.0,
                         cost.data(), lower.data(), upper.data(), rl.data(),
                         ru.data(), start.data(), index.data(),
                         value.data()) != kHighsStatusError;
#endif
}

RelaxationLp::~RelaxationLp()
{
#ifdef STP_HAVE_HIGHS
  if (engine_)
    Highs_destroy(engine_);
#endif
}

std::optional<ExactRational>
RelaxationLp::minimize(const std::vector<RelaxationTerm>& objective,
                       double seconds, std::optional<double> minimum_useful)
{
  values_.clear();
#ifdef STP_HAVE_HIGHS
  if (!usable_ || seconds <= 0)
    return std::nullopt;
  struct SearchTimer
  {
    double& total;
    std::chrono::steady_clock::time_point start =
        std::chrono::steady_clock::now();
    bool active = true;
    void stop()
    {
      if (active)
        total += std::chrono::duration<double>(
                     std::chrono::steady_clock::now() - start)
                     .count();
      active = false;
    }
    ~SearchTimer() { stop(); }
  } timer{search_seconds};
  std::vector<double> cost(box_.size(), 0.0);
  for (const auto& term : objective)
  {
    if (term.var >= cost.size())
      return std::nullopt;
    cost[term.var] += approximate(term.coefficient);
    if (!std::isfinite(cost[term.var]))
      return std::nullopt;
  }
  // HiGHS measures time cumulatively over repeated runs of this model.
  Highs_setDoubleOptionValue(engine_, "time_limit",
                             Highs_getRunTime(engine_) + seconds);
  if (Highs_changeColsCostByRange(engine_, 0,
                                  static_cast<HighsInt>(cost.size() - 1),
                                  cost.data()) == kHighsStatusError ||
      Highs_run(engine_) == kHighsStatusError)
    return std::nullopt;
  const bool optimal =
      Highs_getModelStatus(engine_) == kHighsModelStatusOptimal;
  if (!optimal && !partial_)
    return std::nullopt;
  values_.resize(box_.size());
  std::vector<double> weights(rows_.size());
  if (Highs_getSolution(engine_, values_.data(), nullptr, nullptr,
                        weights.data()) == kHighsStatusError)
  {
    values_.clear();
    return std::nullopt;
  }
  // This is only a scheduling heuristic. A rounded objective may cause us
  // to miss an improvement, but cannot establish a bound or an answer.
  // Keep the primal proposal available for independently checked witnesses.
  if (minimum_useful && std::isfinite(*minimum_useful))
  {
    double proposed = Highs_getObjectiveValue(engine_);
    if (!optimal)
    {
      // The primal objective of an unfinished solve says little about its
      // dual proposal. Estimate the same residual formula the exact checker
      // will use instead. This can only decline work, never certify a fact.
      auto residual = cost;
      proposed = 0;
      for (std::size_t i = 0; i < rows_.size(); ++i)
      {
        const double weight =
            rows_[i].equality ? weights[i] : std::min(0.0, weights[i]);
        if (weight == 0)
          continue;
        proposed += weight * approximate(rows_[i].rhs);
        for (const auto& term : rows_[i].terms)
          residual[term.var] -= weight * approximate(term.coefficient);
      }
      for (std::size_t v = 0; v < box_.size(); ++v)
        if (residual[v] != 0)
          proposed +=
              residual[v] *
              approximate(residual[v] > 0 ? *box_[v].lower : *box_[v].upper);
    }
    const double margin = 1e-9 * (1.0 + std::abs(*minimum_useful));
    if (std::isfinite(proposed) && proposed < *minimum_useful - margin)
    {
      ++screened;
      return std::nullopt;
    }
  }
  timer.stop();
  const auto cert_start = std::chrono::steady_clock::now();
  // Any finite weights of the right dimension can be checked: neither dual
  // feasibility nor LP optimality is assumed by the exact residual proof.
  auto result = certifyRelaxationLower(rows_, box_, objective, weights);
  if (result && !optimal)
    ++partial_certificates;
  certificate_seconds += std::chrono::duration<double>(
                             std::chrono::steady_clock::now() - cert_start)
                             .count();
  return result;
#else
  (void)objective;
  (void)seconds;
  (void)minimum_useful;
  return std::nullopt;
#endif
}

RelaxationProbe probeRelaxation(const std::vector<RelaxationRow>& rows,
                                const std::vector<RelaxationBox>& box,
                                double seconds, bool partial)
{
  RelaxationProbe result;
  if (seconds <= 0)
    return result;
  const ExactRational one(std::int64_t{1});
  ExactRational maximum = one;
  std::vector<RelaxationRow> relaxed;
  for (const auto& row : rows)
    for (unsigned direction = 0; direction < (row.equality ? 2U : 1U);
         ++direction)
    {
      RelaxationRow side = row;
      side.equality = false;
      if (direction)
      {
        side.rhs.negate();
        for (auto& term : side.terms)
          term.coefficient.negate();
      }
      ExactRational violation = -side.rhs;
      for (const auto& term : side.terms)
      {
        if (term.var >= box.size())
          return result;
        const auto& endpoint = term.coefficient.sign() > 0
                                   ? box[term.var].upper
                                   : box[term.var].lower;
        if (!endpoint)
          return result;
        violation += term.coefficient * *endpoint;
      }
      maximum = std::max(maximum, violation);
      side.terms.push_back({box.size(), -one});
      relaxed.push_back(std::move(side));
    }
  auto extended = box;
  extended.push_back({ExactRational(), maximum});
  RelaxationLp lp(relaxed, extended, {partial, std::nullopt});
  const auto lower = lp.minimize({{box.size(), one}}, seconds);
  result.refuted = lower && lower->sign() > 0;
  result.values = lp.values();
  if (result.values.size() > box.size())
    result.values.resize(box.size());
  return result;
}
} // namespace stp::lra

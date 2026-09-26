#include "LraHighsCuts.h"
#include <map>

namespace stp::lra
{
std::optional<HighsProofRow> certifyHighsCgCut(
    const std::vector<HighsProofRow>& rows, const std::vector<bool>& binary,
    const std::vector<std::pair<std::size_t, ExactRational>>& weights,
    bool complementNegative, const std::function<bool()>& keepGoing)
{
  if (weights.empty() || weights.size() > 4096 || rows.size() > 200000 ||
      binary.size() > 100000)
    return std::nullopt;
  std::map<std::size_t, ExactRational> coefficients;
  ExactRational rhs;
  bool strict = false;
  for (const auto& [r, weight] : weights)
  {
    if (r >= rows.size() || (keepGoing && !keepGoing()))
      return std::nullopt;
    if (weight.isZero())
      continue;
    const auto& row = rows[r];
    if (!row.equality && weight.sign() < 0)
      return std::nullopt;
    if (row.equality && row.strict)
      return std::nullopt;
    rhs += weight * row.rhs;
    strict = strict || row.strict;
    for (const auto& t : row.terms)
    {
      if (t.col >= binary.size())
        return std::nullopt;
      coefficients[t.col] += weight * t.coefficient;
    }
  }
  struct Bounds
  {
    std::optional<ExactRational> lower, upper;
  };
  std::vector<Bounds> bounds(binary.size());
  for (std::size_t r = 0; r < rows.size(); ++r)
  {
    if (r % 256 == 0 && keepGoing && !keepGoing())
      return std::nullopt;
    const auto& row = rows[r];
    if (row.terms.size() != 1)
      continue;
    const auto& t = row.terms[0];
    if (t.col >= binary.size())
      return std::nullopt;
    if (t.coefficient.isZero())
      continue;
    const auto endpoint = row.rhs / t.coefficient;
    auto& b = bounds[t.col];
    if (row.equality || t.coefficient.sign() < 0)
      if (!b.lower || *b.lower < endpoint)
        b.lower = endpoint;
    if (row.equality || t.coefficient.sign() > 0)
      if (!b.upper || endpoint < *b.upper)
        b.upper = endpoint;
  }
  HighsProofRow cut;
  ExactRational shift;
  for (const auto& [c, a] : coefficients)
  {
    if (a.isZero())
      continue;
    if (!binary[c])
    {
      const auto& endpoint = a.sign() > 0 ? bounds[c].lower : bounds[c].upper;
      if (!endpoint)
        return std::nullopt;
      rhs -= a * *endpoint;
      continue;
    }
    auto rounded = a.floor();
    if (complementNegative && a.sign() < 0)
    {
      // b' = 1-b is also a nonnegative integer. Undo its integer constant
      // after rounding; the 0/1 domain justifies both substitutions.
      rhs -= a;
      rounded = -(-a).floor();
      shift -= rounded;
    }
    if (!rounded.isZero())
      cut.terms.push_back({c, std::move(rounded)});
  }
  cut.rhs = rhs.floor();
  if (strict && cut.rhs == rhs)
    cut.rhs -= ExactRational(std::int64_t{1});
  cut.rhs -= shift;
  return cut;
}
std::optional<HighsProofRow> certifyHighsSplitCut(
    const std::vector<HighsProofRow>& rows, const std::vector<bool>& binary,
    const std::vector<std::pair<std::size_t, ExactRational>>& weights,
    std::size_t target, const std::vector<bool>& preferUpper,
    const std::function<bool()>& keepGoing)
{
  if (weights.empty() || weights.size() > 4096 || rows.size() > 200000 ||
      binary.size() > 100000 || target >= binary.size() || !binary[target] ||
      preferUpper.size() != binary.size())
    return std::nullopt;
  std::map<std::size_t, ExactRational> aggregate;
  for (const auto& [r, w] : weights)
  {
    if (r >= rows.size() || (keepGoing && !keepGoing()))
      return std::nullopt;
    for (const auto& t : rows[r].terms)
    {
      if (t.col >= binary.size())
        return std::nullopt;
      aggregate[t.col] += w * t.coefficient;
    }
  }
  const auto found = aggregate.find(target);
  if (found == aggregate.end() || found->second.isZero())
    return std::nullopt;
  const auto divisor = found->second;
  struct Bounds
  {
    std::optional<ExactRational> lower, upper;
  };
  std::vector<Bounds> bounds(binary.size());
  const ExactRational zero, one(std::int64_t{1});
  for (std::size_t c = 0; c < binary.size(); ++c)
    if (binary[c])
    {
      bounds[c].lower = zero;
      bounds[c].upper = one;
    }
  for (std::size_t r = 0; r < rows.size(); ++r)
  {
    if (r % 256 == 0 && keepGoing && !keepGoing())
      return std::nullopt;
    const auto& row = rows[r];
    if (row.terms.size() != 1)
      continue;
    const auto& t = row.terms[0];
    if (t.col >= binary.size())
      return std::nullopt;
    if (t.coefficient.isZero())
      continue;
    const auto endpoint = row.rhs / t.coefficient;
    auto& b = bounds[t.col];
    if (row.equality || t.coefficient.sign() < 0)
      if (!b.lower || *b.lower < endpoint)
        b.lower = endpoint;
    if (row.equality || t.coefficient.sign() > 0)
      if (!b.upper || endpoint < *b.upper)
        b.upper = endpoint;
  }
  struct Deviation
  {
    ExactRational coefficient, constant;
    std::vector<HighsProofTerm> terms;
  };
  std::vector<Deviation> deviations;
  ExactRational beta;
  // Weighted row identities: s_r = A_r*x, with s_r = rhs_r-y_r for
  // inequalities (y_r >= 0), and s_r = rhs_r for asserted equalities.
  for (const auto& [r, w] : weights)
  {
    const auto& row = rows[r];
    if (row.equality && row.strict)
      return std::nullopt;
    const auto weight = w / divisor;
    beta += weight * row.rhs;
    if (row.equality || weight.isZero())
      continue;
    Deviation deviation{-weight, row.rhs, {}};
    for (const auto& t : row.terms)
      deviation.terms.push_back({t.col, -t.coefficient});
    deviations.push_back(std::move(deviation));
  }
  for (const auto& [c, a] : aggregate)
  {
    if (c == target || a.isZero())
      continue;
    const auto& b = bounds[c];
    const bool upper = b.upper && (preferUpper[c] || !b.lower);
    const auto& endpoint = upper ? b.upper : b.lower;
    if (!endpoint)
      return std::nullopt;
    const auto coefficient = a / divisor;
    beta -= coefficient * *endpoint;
    deviations.push_back({upper ? coefficient : -coefficient,
                          upper ? *endpoint : -*endpoint,
                          {{c, upper ? -one : one}}});
  }
  const auto fraction = beta - beta.floor();
  if (fraction.isZero())
    return std::nullopt;
  HighsProofRow cut;
  cut.rhs = -one;
  std::map<std::size_t, ExactRational> terms;
  // b = beta + sum d_i*y_i, y_i >= 0. Integrality of b requires
  // sum d_i*y_i <= -f or >= 1-f. Either case implies the intersection cut.
  for (const auto& d : deviations)
  {
    if (keepGoing && !keepGoing())
      return std::nullopt;
    const auto multiplier = d.coefficient.sign() > 0
                                ? d.coefficient / (one - fraction)
                                : -d.coefficient / fraction;
    cut.rhs += multiplier * d.constant;
    for (const auto& t : d.terms)
      terms[t.col] -= multiplier * t.coefficient;
  }
  for (auto& [c, a] : terms)
    if (!a.isZero())
      cut.terms.push_back({c, std::move(a)});
  return cut;
}

} // namespace stp::lra

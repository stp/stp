#include "FloatBasis.h"

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <limits>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

namespace
{

using stp::lra::FloatBasis;
using Index = FloatBasis::Index;
using Entry = FloatBasis::Entry;

int instances_exercised = 0;
int replacements_exercised = 0;

void require(bool condition, const std::string& what)
{
  if (!condition)
    throw std::runtime_error(what);
}

/* Dense reference: Gaussian elimination with partial pivoting.  Returns
 * false when the matrix is singular within tolerance. */
bool denseSolve(std::vector<double> matrix, Index n, std::vector<double> rhs,
                std::vector<double>& out)
{
  for (Index column = 0; column < n; ++column)
  {
    Index best = column;
    for (Index row = column + 1; row < n; ++row)
      if (std::fabs(matrix[row * n + column]) >
          std::fabs(matrix[best * n + column]))
        best = row;
    if (std::fabs(matrix[best * n + column]) < 1.0e-9)
      return false;
    if (best != column)
    {
      for (Index j = 0; j < n; ++j)
        std::swap(matrix[best * n + j], matrix[column * n + j]);
      std::swap(rhs[best], rhs[column]);
    }
    for (Index row = column + 1; row < n; ++row)
    {
      double const factor = matrix[row * n + column] / matrix[column * n + column];
      if (factor == 0.0)
        continue;
      for (Index j = column; j < n; ++j)
        matrix[row * n + j] -= factor * matrix[column * n + j];
      rhs[row] -= factor * rhs[column];
    }
  }
  out.assign(n, 0.0);
  for (Index i = n; i-- > 0;)
  {
    double sum = rhs[i];
    for (Index j = i + 1; j < n; ++j)
      sum -= matrix[i * n + j] * out[j];
    out[i] = sum / matrix[i * n + i];
  }
  return true;
}

std::vector<double> dense(const std::vector<std::vector<Entry>>& columns,
                          Index n)
{
  std::vector<double> matrix(static_cast<std::size_t>(n) * n, 0.0);
  for (Index column = 0; column < n; ++column)
    for (Entry const& entry : columns[column])
      matrix[entry.index * n + column] += entry.value;
  return matrix;
}

std::vector<double> transposed(const std::vector<double>& matrix, Index n)
{
  std::vector<double> result(matrix.size());
  for (Index i = 0; i < n; ++i)
    for (Index j = 0; j < n; ++j)
      result[j * n + i] = matrix[i * n + j];
  return result;
}

double maxAbsDifference(const std::vector<double>& a,
                        const std::vector<double>& b)
{
  double worst = 0.0;
  for (std::size_t i = 0; i < a.size(); ++i)
    worst = std::fmax(worst, std::fabs(a[i] - b[i]));
  return worst;
}

double maxAbs(const std::vector<double>& a)
{
  double worst = 0.0;
  for (double const value : a)
    worst = std::fmax(worst, std::fabs(value));
  return worst;
}

std::vector<Entry> randomColumn(std::mt19937& rng, Index n, Index nonzeros)
{
  std::vector<Entry> column;
  std::uniform_int_distribution<Index> rows(0, n - 1);
  std::uniform_real_distribution<double> values(-3.0, 3.0);
  while (column.size() < nonzeros)
  {
    Index const row = rows(rng);
    bool duplicate = false;
    for (Entry const& entry : column)
      duplicate = duplicate || entry.index == row;
    if (duplicate)
      continue;
    double value = values(rng);
    if (std::fabs(value) < 0.05)
      value = 1.0;
    column.push_back(Entry{row, value});
  }
  return column;
}

/* A basis the float tier would build: unit columns for basic row
 * variables and sparse structural columns among them. */
std::vector<std::vector<Entry>> randomBasis(std::mt19937& rng, Index n,
                                            Index structural)
{
  std::vector<std::vector<Entry>> columns(n);
  std::vector<Index> order(n);
  for (Index i = 0; i < n; ++i)
    order[i] = i;
  std::shuffle(order.begin(), order.end(), rng);
  std::uniform_int_distribution<Index> width(0, 5);
  std::uniform_real_distribution<double> diagonal(1.0, 3.0);
  std::uniform_int_distribution<int> sign(0, 1);
  for (Index column = 0; column < n; ++column)
  {
    if (column < structural)
    {
      /* A structural column owns one row no other column owns, with a
       * dominant entry there, plus random fill: nonsingular by
       * construction, sparse and unsymmetric like the real thing. */
      std::vector<Entry> cells = randomColumn(rng, n, std::min<Index>(width(rng), n - 1));
      cells.erase(std::remove_if(cells.begin(), cells.end(),
                                 [&](Entry const& e) { return e.index == order[column]; }),
                  cells.end());
      for (Entry& cell : cells)
        cell.value *= 0.1;
      cells.push_back(Entry{order[column], (sign(rng) ? 1.0 : -1.0) * diagonal(rng)});
      columns[column] = cells;
    }
    else
      columns[column] = {Entry{order[column], 1.0}};
  }
  std::shuffle(columns.begin(), columns.end(), rng);
  return columns;
}

void checkAgainstDense(const FloatBasis& basis,
                       const std::vector<std::vector<Entry>>& columns,
                       Index n, std::mt19937& rng, const char* what)
{
  std::vector<double> const matrix = dense(columns, n);
  std::uniform_real_distribution<double> values(-5.0, 5.0);
  std::vector<double> rhs(n, 0.0);
  std::uniform_int_distribution<int> coin(0, 1);
  if (coin(rng))
    for (double& value : rhs)
      value = values(rng);
  else
    rhs[std::uniform_int_distribution<Index>(0, n - 1)(rng)] = 1.0;
  std::vector<double> expected;
  require(denseSolve(matrix, n, rhs, expected), std::string(what) + ": dense singular");
  std::vector<double> got = rhs;
  std::vector<Index> nonzeros;
  for (Index i = 0; i < n; ++i)
    if (got[i] != 0.0)
      nonzeros.push_back(i);
  require(basis.ftran(got, nonzeros), std::string(what) + ": ftran refused");
  for (Index i = 0; i < n; ++i)
    if (got[i] != 0.0 && std::find(nonzeros.begin(), nonzeros.end(), i) == nonzeros.end())
      throw std::runtime_error(std::string(what) + ": ftran left a nonzero unreported");
  double const tolerance = 1.0e-7 * std::fmax(1.0, maxAbs(expected));
  if (maxAbsDifference(got, expected) > tolerance)
    throw std::runtime_error(std::string(what) + ": ftran differs by " +
                             std::to_string(maxAbsDifference(got, expected)));
  std::vector<double> expected_t;
  require(denseSolve(transposed(matrix, n), n, rhs, expected_t),
          std::string(what) + ": dense transpose singular");
  std::vector<double> got_t = rhs;
  std::vector<Index> nonzeros_t;
  for (Index i = 0; i < n; ++i)
    if (got_t[i] != 0.0)
      nonzeros_t.push_back(i);
  require(basis.btran(got_t, nonzeros_t), std::string(what) + ": btran refused");
  for (Index i = 0; i < n; ++i)
    if (got_t[i] != 0.0 && std::find(nonzeros_t.begin(), nonzeros_t.end(), i) == nonzeros_t.end())
      throw std::runtime_error(std::string(what) + ": btran left a nonzero unreported");
  double const tolerance_t = 1.0e-7 * std::fmax(1.0, maxAbs(expected_t));
  if (maxAbsDifference(got_t, expected_t) > tolerance_t)
    throw std::runtime_error(std::string(what) + ": btran differs by " +
                             std::to_string(maxAbsDifference(got_t, expected_t)));
}

void exercise(std::mt19937& rng, Index n, Index structural, int replacements)
{
  std::vector<std::vector<Entry>> columns = randomBasis(rng, n, structural);
  std::vector<double> probe;
  require(denseSolve(dense(columns, n), n, std::vector<double>(n, 1.0), probe),
          "the generator produced a singular basis");
  ++instances_exercised;
  FloatBasis basis;
  require(basis.refactor(n, columns), "refactor refused a nonsingular basis");
  checkAgainstDense(basis, columns, n, rng, "fresh factor");
  std::uniform_int_distribution<Index> positions(0, n - 1);
  std::uniform_int_distribution<Index> width(1, 6);
  int done = 0;
  for (int attempt = 0; attempt < replacements * 4 && done < replacements;
       ++attempt)
  {
    std::vector<Entry> const entering = randomColumn(rng, n, std::min<Index>(width(rng) + 1U, n));
    std::vector<double> direction(n, 0.0);
    std::vector<Index> direction_nonzeros;
    for (Entry const& entry : entering)
    {
      if (direction[entry.index] == 0.0)
        direction_nonzeros.push_back(entry.index);
      direction[entry.index] += entry.value;
    }
    require(basis.ftran(direction, direction_nonzeros),
            "ftran of the entering column refused");
    /* The leaving position is where the direction is largest, as a ratio
     * test would choose among the rows the entering column moves; a
     * random position would usually make the new basis singular. */
    Index position = 0;
    for (Index i = 1; i < n; ++i)
      if (std::fabs(direction[i]) > std::fabs(direction[position]))
        position = i;
    if (std::fabs(direction[position]) < 1.0e-3)
      continue;
    (void)positions;
    std::vector<std::vector<Entry>> replaced = columns;
    replaced[position] = entering;
    std::vector<double> probe2;
    if (!denseSolve(dense(replaced, n), n, std::vector<double>(n, 1.0), probe2))
      continue;
    require(basis.update(position), "update refused");
    columns = replaced;
    ++done;
    ++replacements_exercised;
    checkAgainstDense(basis, columns, n, rng, "after update");
    if (basis.refactorDue() || done % 7 == 0)
    {
      require(basis.refactor(n, columns), "refactor refused after updates");
      checkAgainstDense(basis, columns, n, rng, "refactored");
    }
  }
  require(replacements == 0 || done > 0, "no replacement was exercised");
}

}  // namespace

int main()
{
  try
  {
    std::mt19937 rng(20260902);
    {
      using Failure = FloatBasis::RefactorFailure;
      FloatBasis basis;
      require(!basis.refactor(1, {{{0, 1e-14}}}) &&
                  basis.refactorFailure() == Failure::SmallPivot &&
                  basis.failureStep() == 0 && basis.failurePivot() == 1e-14,
              "tiny pivot diagnosis");
      require(!basis.refactor(
                  1, {{{0, std::numeric_limits<double>::infinity()}}}) &&
                  basis.refactorFailure() == Failure::InvalidInput,
              "nonfinite input diagnosis");
      require(!basis.refactor(1, {{{1, 1.0}}}) &&
                  basis.refactorFailure() == Failure::InvalidInput,
              "out-of-range input diagnosis");
      require(!basis.refactor(1, {{}}) &&
                  basis.refactorFailure() == Failure::EmptyColumn,
              "empty column diagnosis");
      require(basis.refactor(1, {{{0, 1.0}}}, true) &&
                  basis.refactorFailure() == Failure::None,
              "cold refactor clears failed state");
      // Stability-first refactoring must solve both orientations, with the
      // same independent dense oracle used for the ordinary factorization.
      for (Index n : {5U, 20U, 80U})
      {
        const auto columns = randomBasis(rng, n, n);
        require(basis.refactor(n, columns, true), "robust refactor refused");
        checkAgainstDense(basis, columns, n, rng, "robust refactor");
      }
    }
    exercise(rng, 1, 0, 0);
    exercise(rng, 5, 2, 10);
    exercise(rng, 20, 8, 40);
    exercise(rng, 60, 25, 60);
    exercise(rng, 150, 40, 60);
    exercise(rng, 200, 10, 30);   // unit-heavy: the singleton path
    exercise(rng, 300, 120, 40);
    /* A singular matrix is refused, not factored into nonsense. */
    {
      std::vector<std::vector<Entry>> columns(3);
      columns[0] = {Entry{0, 1.0}};
      columns[1] = {Entry{0, 2.0}};
      columns[2] = {Entry{2, 1.0}};
      FloatBasis basis;
      require(!basis.refactor(3, columns), "a singular basis was accepted");
      require(!basis.ready(), "a refused factor reported ready");
    }
    require(instances_exercised == 7, "not every instance was exercised");
    require(replacements_exercised >= 200,
            "too few replacements exercised: " + std::to_string(replacements_exercised));
    std::printf("float basis tests passed: %d bases, %d replacements\n",
                instances_exercised, replacements_exercised);
    return 0;
  }
  catch (std::exception const& failure)
  {
    std::fprintf(stderr, "float basis tests failed: %s\n", failure.what());
    return 1;
  }
}

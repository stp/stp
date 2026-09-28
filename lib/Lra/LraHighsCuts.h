#ifndef STP_LRA_HIGHS_CUTS_H
#define STP_LRA_HIGHS_CUTS_H
#include "ExactRational.h"
#include <functional>
#include <optional>
#include <vector>
namespace stp::lra
{
struct HighsProofTerm
{
  std::size_t col;
  ExactRational coefficient;
};
struct HighsProofRow
{
  std::vector<HighsProofTerm> terms;
  ExactRational rhs;
  bool equality = false, strict = false;
};
// The caller supplies asserted rows and independently proved 0/1 domains.
// Rebuild the weighted inequality exactly, eliminate continuous residuals
// using explicit one-variable bounds, then apply Chvatal-Gomory rounding.
// The proposed weights/indices carry no authority. Unsupported premises or
// missing residual endpoints cause refusal. No floating cut is accepted.
std::optional<HighsProofRow> certifyHighsCgCut(
    const std::vector<HighsProofRow>& rows, const std::vector<bool>& binary,
    const std::vector<std::pair<std::size_t, ExactRational>>& weights,
    bool complementNegative = false,
    const std::function<bool()>& keepGoing = {});
// Intersection cut for the split b <= floor(beta) or b >= ceil(beta), where
// b has a proved binary domain. Row slacks and endpoint deviations are
// nonnegative; exact substitution eliminates them from the returned cut.
std::optional<HighsProofRow> certifyHighsSplitCut(
    const std::vector<HighsProofRow>& rows, const std::vector<bool>& binary,
    const std::vector<std::pair<std::size_t, ExactRational>>& weights,
    std::size_t target, const std::vector<bool>& preferUpper,
    const std::function<bool()>& keepGoing = {});
} // namespace stp::lra
#endif

#ifndef STP_LRA_RELAXATION_H
#define STP_LRA_RELAXATION_H
#include "LraRelu.h"
#include <memory>

namespace stp::lra
{
using RelaxationRow = ReluProblem::Row;
using RelaxationBox = ReluProblem::Box;
using RelaxationTerm = ReluProblem::Term;

// A dual proposal is not assumed to cancel coefficients. Its exact residual
// is bounded over the supplied box. Missing required endpoints, nonfinite
// weights and dimension mismatches cause refusal, never an approximate fact.
std::optional<ExactRational>
certifyRelaxationLower(const std::vector<RelaxationRow>& rows,
                       const std::vector<RelaxationBox>& box,
                       const std::vector<RelaxationTerm>& objective,
                       const std::vector<double>& weights);
ExactRational exactDyadic(double value);
double approximate(const ExactRational& value);

struct RelaxationOptions
{
  bool partial = false;
  std::optional<unsigned> iteration_limit;
};

class RelaxationLp final
{
public:
  RelaxationLp(const std::vector<RelaxationRow>& rows,
               const std::vector<RelaxationBox>& box,
               RelaxationOptions options = {});
  ~RelaxationLp();
  RelaxationLp(const RelaxationLp&) = delete;
  RelaxationLp& operator=(const RelaxationLp&) = delete;
  std::optional<ExactRational>
  minimize(const std::vector<RelaxationTerm>& objective, double seconds,
           std::optional<double> minimum_useful = std::nullopt);
  const std::vector<double>& values() const { return values_; }
  double search_seconds = 0, certificate_seconds = 0;
  std::size_t screened = 0, partial_certificates = 0;

private:
  // Only used by the optional HiGHS backend; keep the layout independent of it.
  [[maybe_unused]] const std::vector<RelaxationRow>& rows_;
  [[maybe_unused]] const std::vector<RelaxationBox>& box_;
  [[maybe_unused]] void* engine_ = nullptr;
  [[maybe_unused]] bool usable_ = false;
  [[maybe_unused]] bool partial_ = false;
  std::vector<double> values_;
};

// Always feasible auxiliary LP: add a nonnegative bounded slack to every
// row (both directions of equalities). A certified positive minimum refutes
// precisely the rows and box supplied by the caller.
struct RelaxationProbe
{
  bool refuted = false;
  std::vector<double> values;
};
RelaxationProbe probeRelaxation(const std::vector<RelaxationRow>& rows,
                                const std::vector<RelaxationBox>& box,
                                double seconds, bool partial = false);
} // namespace stp::lra
#endif

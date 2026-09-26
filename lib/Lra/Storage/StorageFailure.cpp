#include "Storage/StorageFailure.h"

#include <utility>

namespace stp::lra {
namespace {

std::string failureMessage(char const* operation, std::string const& detail)
{
  std::string result(operation == nullptr ? "storage operation" : operation);
  if (!detail.empty())
  {
    result += ": ";
    result += detail;
  }
  return result;
}

}  // namespace

StorageFailure::StorageFailure(StorageFailureKind kind,
                               char const* operation,
                               std::string detail)
    : std::runtime_error(failureMessage(operation, detail)),
      kind_(kind),
      operation_(operation == nullptr ? "storage operation" : operation)
{
}

StorageFailureKind StorageFailure::kind() const noexcept
{
  return kind_;
}

char const* StorageFailure::operation() const noexcept
{
  return operation_.c_str();
}

}  // namespace stp::lra

#ifndef STP_LRA_STORAGE_FAILURE_H
#define STP_LRA_STORAGE_FAILURE_H

#include <cstdint>
#include <stdexcept>
#include <string>

namespace stp::lra {

enum class StorageFailureKind : std::uint8_t
{
  InvalidGeneration,
  InvalidOrdinal,
  InvalidCheckpoint,
  Exhausted,
  ResourceLimit,
  AllocationFailure,
  LengthError,
  OutOfRange,
  InvariantViolation,
  InternalError
};

class StorageFailure final : public std::runtime_error
{
 public:
  StorageFailure(StorageFailureKind,
                 char const* operation,
                 std::string detail = {});
  StorageFailureKind kind() const noexcept;
  char const* operation() const noexcept;

 private:
  StorageFailureKind kind_;
  std::string operation_;
};

}  // namespace stp::lra

#endif

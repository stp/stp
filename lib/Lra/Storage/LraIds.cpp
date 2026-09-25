#include "Storage/LraIds.h"

#include <atomic>
#include <charconv>
#include <limits>
#include <new>
#include <stdexcept>
#include <string_view>
#include <utility>

namespace stp::lra {
namespace {

constexpr std::uint32_t reserved_field =
    std::numeric_limits<std::uint32_t>::max();
std::atomic<std::uint64_t> next_domain_ordinal{1};

CoreGeneration makeGeneration(std::uint32_t domain,
                              std::uint32_t epoch) noexcept
{
  return CoreGeneration{(static_cast<std::uint64_t>(domain) << 32U) |
                        static_cast<std::uint64_t>(epoch)};
}

void appendUnsigned(std::string& destination, std::uint64_t value)
{
  char buffer[32];
  auto const converted = std::to_chars(buffer, buffer + sizeof(buffer), value);
  if (converted.ec != std::errc{})
  {
    throw StorageFailure(StorageFailureKind::InternalError,
                         "debugString", "integer formatting failed");
  }
  destination.append(buffer, converted.ptr);
}

template <class Id>
std::string formatId(std::string_view kind, Id id)
{
  std::string result;
  result.reserve(kind.size() + 48U);
  result.append(kind);
  result.push_back('@');
  appendUnsigned(result, id.generation().domainOrdinal());
  result.push_back(':');
  appendUnsigned(result, id.generation().epoch());
  result.push_back('#');
  appendUnsigned(result, id.ordinal());
  return result;
}

template <class Function>
std::string checkedDebug(Function&& function)
{
  try
  {
    return std::forward<Function>(function)();
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "debugString", "debug string allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "debugString", "debug string length limit");
  }
}

}  // namespace

bool CoreGeneration::valid() const noexcept
{
  std::uint32_t const domain = domainOrdinal();
  std::uint32_t const epoch_value = epoch();
  return domain != 0 && domain != reserved_field && epoch_value != 0 &&
         epoch_value != reserved_field;
}

std::uint32_t CoreGeneration::domainOrdinal() const noexcept
{
  return static_cast<std::uint32_t>(value >> 32U);
}

std::uint32_t CoreGeneration::epoch() const noexcept
{
  return static_cast<std::uint32_t>(value);
}

GenerationDomain::GenerationDomain() : domain_(0), epoch_(1)
{
  std::uint64_t observed = next_domain_ordinal.load(std::memory_order_relaxed);
  for (;;)
  {
    if (observed >= reserved_field)
    {
      throw StorageFailure(StorageFailureKind::Exhausted,
                           "GenerationDomain", "domain ordinal exhausted");
    }
    if (next_domain_ordinal.compare_exchange_weak(
            observed, observed + 1U,
            std::memory_order_relaxed, std::memory_order_relaxed))
    {
      domain_ = static_cast<std::uint32_t>(observed);
      return;
    }
  }
}

CoreGeneration GenerationDomain::current() const noexcept
{
  return makeGeneration(domain_, epoch_);
}

CoreGeneration GenerationDomain::advance()
{
  if (epoch_ >= reserved_field - 1U)
  {
    throw StorageFailure(StorageFailureKind::Exhausted,
                         "GenerationDomain::advance", "epoch exhausted");
  }
  ++epoch_;
  return current();
}

bool isImmediateSuccessor(CoreGeneration current,
                          CoreGeneration proposed) noexcept
{
  if (!current.valid() || !proposed.valid() ||
      current.domainOrdinal() != proposed.domainOrdinal() ||
      current.epoch() >= reserved_field - 1U)
  {
    return false;
  }
  return proposed.epoch() == current.epoch() + 1U;
}

std::string debugString(CoreGeneration generation)
{
  return checkedDebug([generation] {
    if (!generation.valid())
    {
      return std::string("generation(invalid)");
    }
    std::string result("generation(");
    appendUnsigned(result, generation.domainOrdinal());
    result.push_back(':');
    appendUnsigned(result, generation.epoch());
    result.push_back(')');
    return result;
  });
}

std::string debugString(VariableId id)
{
  return checkedDebug([id] { return formatId("variable", id); });
}
std::string debugString(RowId id)
{
  return checkedDebug([id] { return formatId("row", id); });
}
std::string debugString(AtomId id)
{
  return checkedDebug([id] { return formatId("atom", id); });
}
std::string debugString(BoundRef id)
{
  return checkedDebug([id] { return formatId("bound", id); });
}

std::string debugString(OriginId id)
{
  return checkedDebug([id] {
    std::string result("origin(");
    appendUnsigned(result, id.solve_epoch);
    result.push_back(':');
    appendUnsigned(result, id.serial);
    result.push_back(')');
    return result;
  });
}

std::string debugString(Checkpoint checkpoint)
{
  return checkedDebug([checkpoint] {
    std::string result("checkpoint(");
    if (checkpoint.generation.valid())
    {
      appendUnsigned(result, checkpoint.generation.domainOrdinal());
      result.push_back(':');
      appendUnsigned(result, checkpoint.generation.epoch());
    }
    else
    {
      result += "invalid";
    }
    result.push_back('#');
    appendUnsigned(result, checkpoint.depth);
    result.push_back(')');
    return result;
  });
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
std::uint64_t detail::StorageTestAccess::exchangeNextDomainOrdinal(
    std::uint64_t value) noexcept
{
  return next_domain_ordinal.exchange(value, std::memory_order_relaxed);
}
#endif

}  // namespace stp::lra

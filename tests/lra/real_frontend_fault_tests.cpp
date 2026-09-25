#include "ImathAllocHooks.h"
#include "LraFrontend.h"
#include "support/CppAllocationFault.h"

#include "stp/STPManager/STPManager.h"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <new>
#include <stdexcept>
#include <string>

namespace {

using namespace stp;
using namespace stp::lra;

[[noreturn]] void fail(const std::string& message)
{
  allocation_fault::disable();
  stp_lra_imath_test_disable_failures();
  throw std::runtime_error(message);
}

void require(bool condition, const std::string& message)
{
  if (!condition)
    fail(message);
}

struct Harness final
{
  STPMgr manager;
  Frontend frontend;
  ASTNode formula;

  Harness() : frontend(manager)
  {
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
    const ASTNode z = manager.CreateSourceSymbol("z", SourceSort::real());
    const ASTNode p = manager.CreateRealTerm(
        REAL_ADD,
        ASTVec{manager.CreateRealTerm(
                   REAL_MUL, ASTVec{manager.CreateRealConst("17/19"), x}),
               manager.CreateRealTerm(
                   REAL_DIV, ASTVec{manager.CreateRealTerm(
                                        REAL_SUB, ASTVec{y, z}),
                                    manager.CreateRealConst("23/29")}),
               manager.CreateRealConst(
                   "123456789123456789123456789/98765432109876543211")});
    const ASTNode equality = manager.CreateRealPredicate(
        EQ, p, manager.CreateRealConst("-99887766/1000033"));
    const ASTNode strict = manager.CreateRealPredicate(
        REAL_LT,
        manager.CreateRealTerm(
            REAL_ADD, ASTVec{p, x, manager.CreateRealConst("7/31")}),
        manager.CreateRealConst("42"));
    formula = manager.defaultNodeFactory->CreateNode(
        XOR, equality,
        manager.defaultNodeFactory->CreateNode(NOT, strict));
  }

  void verifyRecovery()
  {
    const PreregisteredFormula result = frontend.preregister(formula);
    require(!Frontend::containsRealSyntax(result.boolean_formula),
            "recovery left Real syntax in the Boolean formula");
    require(result.predicates.size() == 3 && result.equalities.size() == 1,
            "recovery registration counts changed");
    require(std::string(result.predicates.front().opaque_atom.GetName()) ==
                "@lra_pred_0",
            "failed preregistration leaked an opaque-atom serial");
  }
};

std::uint64_t measureCppAllocations()
{
  Harness harness;
  allocation_fault::begin();
  const PreregisteredFormula result = harness.frontend.preregister(harness.formula);
  const std::uint64_t attempts = allocation_fault::end();
  require(!Frontend::containsRealSyntax(result.boolean_formula),
          "C++ fault measurement did not complete");
  return attempts;
}

std::uint64_t runCppSweep()
{
  const std::uint64_t attempts = measureCppAllocations();
  require(attempts >= 24, "frontend workload exposed too few C++ fault points");
  for (std::uint64_t index = 0; index != attempts; ++index)
  {
    Harness harness;
    const std::uint64_t generation = harness.frontend.registryGeneration();
    allocation_fault::arm(index);
    bool classified = false;
    try
    {
      (void)harness.frontend.preregister(harness.formula);
    }
    catch (const FrontendFailure& failure)
    {
      classified = failure.kind() == FrontendFailureKind::AllocationFailure;
    }
    allocation_fault::disable();
    require(classified, "C++ allocation failure was not typed at point " +
                            std::to_string(index));
    require(harness.frontend.registryGeneration() == generation,
            "C++ allocation failure partially committed the registry");
    harness.verifyRecovery();
  }
  return attempts;
}

std::uint64_t runSymbolSweep()
{
  std::uint64_t points = 0;
  // Empty state, vector growth, and hash-table growth. Sweep the actual
  // allocation sequence rather than depending on a library's bucket sizes.
  for (unsigned count : {0u, 1u, 12u, 13u, 32u})
  {
    auto populate = [count](STPMgr& manager) {
      for (unsigned i = 0; i != count; ++i)
        (void)manager.CreateSourceSymbol(
            ("existing_" + std::to_string(i)).c_str(), SourceSort::real());
    };
    std::uint64_t attempts;
    {
      STPMgr manager;
      populate(manager);
      allocation_fault::begin();
      const ASTNode added =
          manager.CreateSourceSymbol("added", SourceSort::real());
      attempts = allocation_fault::end();
      require(manager.AllRealSymbols().back() == added,
              "symbol allocation measurement did not append");
    }
    require(attempts != 0, "symbol registration exposed no allocation points");
    points += attempts;
    for (std::uint64_t index = 0; index != attempts; ++index)
    {
      STPMgr manager;
      populate(manager);
      ASTVec expected = manager.AllRealSymbols();
      allocation_fault::arm(index);
      bool threw = false;
      try
      {
        (void)manager.CreateSourceSymbol("added", SourceSort::real());
      }
      catch (const std::bad_alloc&)
      {
        threw = true;
      }
      allocation_fault::disable();
      require(threw, "symbol registration did not reach its allocation fault");
      require(manager.AllRealSymbols() == expected,
              "failed symbol registration changed the ordered declarations");
      const ASTNode added =
          manager.CreateSourceSymbol("added", SourceSort::real());
      expected.push_back(added);
      require(manager.AllRealSymbols() == expected,
              "failed symbol registration left stale membership on retry");
      (void)manager.CreateSourceSymbol("added", SourceSort::real());
      require(manager.AllRealSymbols() == expected,
              "retry after an allocation failure registered a duplicate");
    }
  }
  return points;
}

std::uint64_t measureNativeAllocations()
{
  Harness harness;
  stp_lra_imath_test_fail_nth(std::numeric_limits<std::uint64_t>::max());
  harness.verifyRecovery();
  const std::uint64_t attempts = stp_lra_imath_test_allocation_attempts();
  stp_lra_imath_test_disable_failures();
  return attempts;
}

std::uint64_t runNativeSweep()
{
  const std::uint64_t attempts = measureNativeAllocations();
  require(attempts >= 24, "frontend workload exposed too few IMath fault points");
  for (std::uint64_t index = 0; index != attempts; ++index)
  {
    Harness harness;
    const std::uint64_t generation = harness.frontend.registryGeneration();
    stp_lra_imath_test_fail_nth(index);
    bool classified = false;
    std::string observed = "success";
    try
    {
      (void)harness.frontend.preregister(harness.formula);
    }
    catch (const FrontendFailure& failure)
    {
      classified = failure.kind() == FrontendFailureKind::AllocationFailure;
      observed = "FrontendFailure(" +
                 std::to_string(static_cast<unsigned>(failure.kind())) +
                 "): " + failure.what();
    }
    catch (const std::exception& failure)
    {
      observed = std::string("std::exception: ") + failure.what();
    }
    stp_lra_imath_test_disable_failures();
    require(classified, "IMath allocation failure was not typed at point " +
                            std::to_string(index) + ": " + observed);
    require(harness.frontend.registryGeneration() == generation,
            "IMath allocation failure partially committed the registry");
    harness.verifyRecovery();
  }
  return attempts;
}

NumberMetrics runResourceLimit()
{
  STPMgr manager;
  Frontend frontend(manager);
  frontend.configureNumberLimits(
      NumberLimits{128, 24, UINT64_C(1048576), UINT64_C(1048576)});
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode scale = manager.CreateRealConst("65537");
  const ASTNode nested = manager.CreateRealTerm(
      REAL_MUL,
      ASTVec{scale, manager.CreateRealTerm(REAL_MUL, ASTVec{scale, x})});
  const std::uint64_t generation = frontend.registryGeneration();
  bool classified = false;
  try
  {
    (void)frontend.normalize(nested);
  }
  catch (const FrontendFailure& failure)
  {
    classified = failure.kind() == FrontendFailureKind::ResourceLimit;
  }
  require(classified, "coefficient bit resource stop was not typed");
  require(frontend.registryGeneration() == generation,
          "resource stop partially committed the registry");
  require(frontend.numberStopped(), "resource stop did not stop the budget");
  const NumberMetrics stopped = frontend.numberMetrics();
  require(stopped.preflight_stops != 0,
          "resource stop was not present in number metrics");
  frontend.resetNumberAccounting();
  require(!frontend.numberStopped(), "resource accounting reset failed");
  const LinearPolynomial retry = frontend.normalize(x);
  require(retry.terms.size() == 1,
          "safe retry after resource stop did not normalize");
  return stopped;
}

} // namespace

int main()
{
  try
  {
    const std::uint64_t cpp_points = runCppSweep();
    const std::uint64_t symbol_points = runSymbolSweep();
    const std::uint64_t native_points = runNativeSweep();
    const NumberMetrics metrics = runResourceLimit();
    std::cout << "{\"passed\":true,\"cpp_fault_points\":" << cpp_points
              << ",\"symbol_fault_points\":" << symbol_points
              << ",\"native_fault_points\":" << native_points
              << ",\"resource_preflight_stops\":"
              << metrics.preflight_stops << "}\n";
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}

#include "stp/cpp_interface.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "support/CppAllocationFault.h"

#include <iostream>
#include <stdexcept>
#include <string>

namespace {
using namespace stp;

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

void symbols()
{
  STPMgr manager;
  STP engine(&manager);
  struct RestoreGlobal final
  {
    STP* saved = GlobalSTP;
    ~RestoreGlobal() { GlobalSTP = saved; }
  } restore;
  GlobalSTP = &engine;
  Cpp_interface api(manager);
  const auto real = SourceSort::real();
  const ASTNode z = manager.CreateSourceSymbol("z", real);
  const ASTNode a = manager.CreateSourceSymbol("a", real);
  ASTVec expected{z, a};
  // Exercise growth and rehashing, with names deliberately out of sort order.
  for (unsigned i = 96; i != 0; --i)
    expected.push_back(manager.CreateSourceSymbol(
        ("symbol_" + std::to_string(i)).c_str(), real));
  for (const ASTNode& symbol : expected)
    require(manager.CreateSourceSymbol(symbol.GetName(), real) == symbol,
            "duplicate Real declaration changed identity");
  require(manager.AllRealSymbols() == expected,
          "Real declarations lost first-seen order or acquired duplicates");

  const ASTNode assertion = manager.CreateRealPredicate(
      EQ, z, manager.CreateRealConst("1"));
  require(engine.TopLevelSTP(assertion, manager.ASTFalse) == SOLVER_SATISFIABLE,
          "Real-symbol model control did not solve");
  require(manager.HasRealModel() && manager.GetRealModelValue(z) == "1" &&
              manager.GetRealModelValue(a) == "0",
          "Real-symbol model completion changed");
  (void)manager.CreateSourceSymbol("z", real);
  require(manager.HasRealModel() && manager.GetRealModelValue(z) == "1",
          "duplicate Real declaration invalidated the model");
  expected.push_back(manager.CreateSourceSymbol("new_symbol", real));
  require(!manager.HasRealModel() && manager.AllRealSymbols() == expected,
          "new Real declaration did not invalidate the model or append");

  for (unsigned reset = 0; reset != 2; ++reset)
  {
    api.reset();
    require(manager.AllRealSymbols().empty(),
            "public reset retained Real declarations");
    // Retained handles keep the old identities interned. Clearing just the
    // vector would let stale membership suppress their new registration.
    require(manager.CreateSourceSymbol("a", real) == a &&
                manager.CreateSourceSymbol("z", real) == z,
            "retained Real handles changed identity after reset");
    (void)manager.CreateSourceSymbol("a", real);
    require(manager.AllRealSymbols() == ASTVec({a, z}),
            "public reset did not reset Real-symbol membership and order");
  }
  STPMgr other;
  const ASTNode other_z = other.CreateSourceSymbol("z", real);
  require(other_z != z && other.AllRealSymbols() == ASTVec({other_z}),
          "Real-symbol membership leaked between managers");
}

std::uint64_t retainedSymbolFault(std::int64_t fault)
{
  STPMgr manager;
  STP engine(&manager);
  struct RestoreGlobal final
  {
    STP* saved = GlobalSTP;
    ~RestoreGlobal() { GlobalSTP = saved; }
  } restore;
  GlobalSTP = &engine;
  Cpp_interface api(manager);
  const auto real = SourceSort::real();
  const ASTNode retained = manager.CreateSourceSymbol("retained", real);
  api.reset();
  const ASTNode base = manager.CreateSourceSymbol("base", real);
  const ASTNode assertion = manager.CreateRealPredicate(
      EQ, base, manager.CreateRealConst("1"));
  require(engine.TopLevelSTP(assertion, manager.ASTFalse) == SOLVER_SATISFIABLE
              && manager.HasRealModel(), "fault control did not build a model");
  require(manager.AllRealSymbols() == ASTVec({base}),
          "fault control did not reset registration");

  // The retained handle keeps exactly the same ID alive across failure.
  // Filling the old one-element vector also makes this insertion grow it.
  if (fault < 0)
    allocation_fault::begin();
  else
    allocation_fault::arm(static_cast<std::uint64_t>(fault));
  bool threw = false;
  ASTNode added;
  try
  {
    added = manager.CreateSourceSymbol("retained", real);
  }
  catch (const std::bad_alloc&)
  {
    threw = true;
  }
  const auto attempts = allocation_fault::end();
  if (fault >= 0)
  {
    require(threw, "retained-symbol allocation fault was not reached");
    require(manager.AllRealSymbols() == ASTVec({base}),
            "failed registration changed ordered symbols");
    require(manager.HasRealModel() && manager.GetRealModelValue(base) == "1",
            "failed registration invalidated the existing model");
    added = manager.CreateSourceSymbol("retained", real);
  }
  else
    require(!threw, "unarmed retained-symbol registration failed");
  require(added == retained, "registration retry changed the retained identity");
  require(manager.AllRealSymbols() == ASTVec({base, retained}),
          "failed vector growth left membership that suppressed the retry");
  require(!manager.HasRealModel(), "successful retry retained a stale model");
  return attempts;
}

} // namespace

int main()
{
  try
  {
    symbols();
    const auto points = retainedSymbolFault(-1);
    require(points >= 2, "retained-symbol workload missed container growth");
    for (std::uint64_t point = 0; point != points; ++point)
      (void)retainedSymbolFault(static_cast<std::int64_t>(point));
    std::cout << "PASS real-symbol-membership retained-fault-points="
              << points << '\n';
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}

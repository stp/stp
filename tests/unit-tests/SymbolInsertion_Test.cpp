#include "stp/STPManager/STPManager.h"
#include "support/CppAllocationFault.h"
#include <gtest/gtest.h>
#include <string>

namespace
{
using namespace stp;

void populate(STPMgr& manager, unsigned count, bool sameName, ASTVec& retained)
{
  for (unsigned i = 0; i != count; ++i)
  {
    const auto name = sameName ? "existing-name-with-several-source-sorts"
                              : "existing-symbol-" + std::to_string(i);
    retained.push_back(manager.CreateSourceSymbol(
        name.c_str(), SourceSort::bitVector(i + 1)));
  }
}

void checkInsertion(unsigned count, bool sameName)
{
  const std::string name = sameName
      ? "existing-name-with-several-source-sorts"
      : "new-symbol-name-longer-than-the-string-inline-buffer";
  const auto sort = SourceSort::bitVector(count + 8);
  std::uint64_t attempts = 0;
  {
    STPMgr manager;
    ASTVec retained;
    populate(manager, count, sameName, retained);
    allocation_fault::begin();
    const ASTNode added = manager.CreateSourceSymbol(name.c_str(), sort);
    attempts = allocation_fault::end();
    ASSERT_FALSE(added.IsNull());
  }
  ASSERT_GT(attempts, 0u);

  // Exercise each allocation boundary, including symbol/name-table growth.
  for (std::uint64_t point = 0; point != attempts; ++point)
  {
    SCOPED_TRACE(::testing::Message()
                 << "count=" << count << " sameName=" << sameName
                 << " allocation=" << point);
    STPMgr manager;
    ASTVec retained;
    populate(manager, count, sameName, retained);
    const auto before = manager.getSymbols();
    bool refused = false;
    allocation_fault::arm(point);
    try
    {
      (void)manager.CreateSourceSymbol(name.c_str(), sort);
    }
    catch (const std::bad_alloc&)
    {
      refused = true;
    }
    allocation_fault::disable();
    ASSERT_TRUE(refused);
    EXPECT_EQ(before, manager.getSymbols());
    if (!sameName || count == 0)
    {
      EXPECT_FALSE(manager.LookupSymbol(name.c_str()));
    }
    for (const auto& symbol : retained)
    {
      EXPECT_TRUE(manager.LookupSymbol(symbol.GetName()));
      EXPECT_EQ(symbol, manager.CreateSourceSymbol(
                            symbol.GetName(), symbol.GetSourceSort()));
    }

    // Retry and intern once, then release it and inspect both indexes again.
    {
      const ASTNode added = manager.CreateSourceSymbol(name.c_str(), sort);
      EXPECT_EQ(added, manager.CreateSourceSymbol(name.c_str(), sort));
      EXPECT_EQ(before.size() + 1, manager.getSymbols().size());
      EXPECT_TRUE(manager.LookupSymbol(name.c_str()));
    }
    EXPECT_EQ(before, manager.getSymbols());
    EXPECT_EQ(sameName && count != 0, manager.LookupSymbol(name.c_str()));
  }
}
} // namespace

TEST(SymbolInsertion, FailedInsertionsLeaveBothIndexesUsable)
{
  for (unsigned count : {0u, 1u, 12u, 13u, 32u})
    for (bool sameName : {false, true})
      checkInsertion(count, sameName);
}

#include "stp/Globals/Globals.h"
#include "stp/Parser/parser.h"
#include "stp/STPManager/STPManager.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <iostream>
#include <sstream>

namespace
{
struct Parser
{
  stp::STPMgr manager;
  stp::Cpp_interface interface{manager, manager.defaultNodeFactory};
  stp::STPMgr* savedManager = stp::GlobalParserBM;
  stp::Cpp_interface* savedInterface = stp::GlobalParserInterface;
  std::ostringstream diagnostics;
  std::streambuf* savedOutput = std::cout.rdbuf(diagnostics.rdbuf());

  Parser()
  {
    stp::GlobalParserBM = &manager;
    stp::GlobalParserInterface = &interface;
    interface.startup();
  }
  ~Parser()
  {
    std::cout.rdbuf(savedOutput);
    stp::GlobalParserBM = savedManager;
    stp::GlobalParserInterface = savedInterface;
  }

  int parse(const char* text)
  {
    stp::SMT2ScanString(text);
    const int result = stp::SMT2Parse();
    smt2lex_destroy();
    return result;
  }
};
} // namespace

TEST(ParserCleanup, DiscardedNodesAndVectorsDoNotRetainSymbols)
{
  for (const char* text : {
      "(set-logic QF_BV)(declare-const p Bool)(assert (not p",
      "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (= x #x01"})
  {
    SCOPED_TRACE(text);
    Parser parser;
    EXPECT_NE(0, parser.parse(text));
    EXPECT_NE(std::string::npos, parser.diagnostics.str().find("error"));
    EXPECT_TRUE(parser.manager.GetAsserts().empty());
    parser.interface.cleanUp();
    parser.manager.ClearAllTables();
    EXPECT_TRUE(parser.manager.getSymbols().empty());
  }
}

// These owning descriptors are not AST symbols. Run this test under a leak
// checker as well to verify their allocations are released on parse abort.
TEST(ParserCleanup, PartialSortsAndFloatingPointLiteralsAreReleased)
{
  for (const char* text : {
      "(set-logic QF_FP)(declare-const f (_ FloatingPoint 8 24)",
      "(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8)",
      "(set-logic QF_ABV)(declare-const a (Array (_ BitVec 8) (_ BitVec 8))",
      "(set-logic QF_FP)(assert (= ((_ to_fp 8 24) RNE 1.25"})
  {
    SCOPED_TRACE(text);
    Parser parser;
    EXPECT_NE(0, parser.parse(text));
    EXPECT_TRUE(parser.manager.GetAsserts().empty());
    parser.interface.cleanUp();
    EXPECT_TRUE(parser.manager.getSymbols().empty());
  }
}

TEST(ParserCleanup, SuccessfulReductionsKeepTheirOperands)
{
  Parser parser;
  ASSERT_EQ(0, parser.parse(
      "(set-logic QF_BV)(declare-const p Bool)(assert (not p))"));
  const auto assertions = parser.manager.GetAsserts();
  ASSERT_EQ(1u, assertions.size());
  EXPECT_EQ(stp::NOT, assertions.front().GetKind());
  ASSERT_EQ(1u, assertions.front().Degree());
  EXPECT_STREQ("p", assertions.front()[0].GetName());
}

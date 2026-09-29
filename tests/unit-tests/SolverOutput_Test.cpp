#include "stp/ToSat/ToSATBase.h"

#include <gtest/gtest.h>

#include <iostream>
#include <sstream>

namespace
{

// Have a fatal error throw rather than end the process, so the test can
// inspect the output and manager state. Restore all global state.
struct PrinterCapture
{
  std::ostringstream out;
  std::ostringstream err;
  std::streambuf* old_out = std::cout.rdbuf(out.rdbuf());
  std::streambuf* old_err = std::cerr.rdbuf(err.rdbuf());
  bool old_throws = stp::FatalErrorThrows();

  PrinterCapture()
  {
    stp::SetFatalErrorThrows(true);
  }

  ~PrinterCapture()
  {
    stp::SetFatalErrorThrows(old_throws);
    std::cout.rdbuf(old_out);
    std::cerr.rdbuf(old_err);
  }
};

TEST(SolverOutput_Test, ErrorsAreFatalInEveryOutputMode)
{
  // The previous error guard depended on whether the manager had seen Real
  // syntax. Error handling must apply to every logic and also to callers
  // that suppress verdict output, which the CLI always enables.
  for (bool smt2 : {false, true})
    for (bool real : {false, true})
      for (bool print : {false, true})
      {
        SCOPED_TRACE(::testing::Message()
                     << "smt2=" << smt2 << " real=" << real
                     << " print=" << print);
        stp::STPMgr manager;
        manager.UserFlags.smtlib2_parser_flag = smt2;
        manager.UserFlags.print_output_flag = print;
        if (real)
          manager.CreateRealConst("0");
        ASSERT_EQ(manager.HasSeenRealSyntax(), real);
        manager.ValidFlag = true;

        PrinterCapture capture;
        EXPECT_THROW(stp::ToSATBase::PrintOutput(&manager, stp::SOLVER_ERROR),
                     stp::EngineFatal);
        EXPECT_FALSE(manager.ValidFlag);
        const char* expected =
            !print ? "" : "(error \"solver returned SOLVER_ERROR\")\n";
        EXPECT_EQ(capture.out.str(), expected);
        EXPECT_EQ(capture.err.str(),
                  "Fatal Error: solver returned SOLVER_ERROR\n");
      }
}

} // namespace

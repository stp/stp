#include "stp/ToSat/ToSATBase.h"

#include <gtest/gtest.h>

#include <iostream>
#include <sstream>

namespace
{

struct SolverError
{
};

// Intercept the fatal-error callback so the test can inspect the output and
// manager state without terminating the process. Restore all global state.
struct PrinterCapture
{
  std::ostringstream out;
  std::ostringstream err;
  std::streambuf* old_out = std::cout.rdbuf(out.rdbuf());
  std::streambuf* old_err = std::cerr.rdbuf(err.rdbuf());
  decltype(stp::vc_error_hdlr) old_handler = stp::vc_error_hdlr;

  PrinterCapture()
  {
    stp::vc_error_hdlr = [](const char*) { throw SolverError{}; };
  }

  ~PrinterCapture()
  {
    stp::vc_error_hdlr = old_handler;
    std::cout.rdbuf(old_out);
    std::cerr.rdbuf(old_err);
  }
};

TEST(SolverOutput_Test, ErrorsAreFatalInEveryOutputMode)
{
  // The previous error guard depended on whether the manager had seen Real
  // syntax. Error handling must apply to every logic and also to callers
  // that suppress verdict output, which the CLI always enables.
  for (int mode = 0; mode < 3; ++mode)
    for (bool real : {false, true})
      for (bool print : {false, true})
      {
        SCOPED_TRACE(::testing::Message()
                     << "mode=" << mode << " real=" << real
                     << " print=" << print);
        stp::STPMgr manager;
        manager.UserFlags.smtlib1_parser_flag = mode == 1;
        manager.UserFlags.smtlib2_parser_flag = mode == 2;
        manager.UserFlags.print_output_flag = print;
        if (real)
          manager.CreateRealConst("0");
        ASSERT_EQ(manager.HasSeenRealSyntax(), real);
        manager.ValidFlag = true;

        PrinterCapture capture;
        EXPECT_THROW(stp::ToSATBase::PrintOutput(&manager, stp::SOLVER_ERROR),
                     SolverError);
        EXPECT_FALSE(manager.ValidFlag);
        const char* expected = !print ? "" : mode == 0 ? "Error.\n"
            : "(error \"solver returned SOLVER_ERROR\")\n";
        EXPECT_EQ(capture.out.str(), expected);
        EXPECT_EQ(capture.err.str(),
                  "Fatal Error: solver returned SOLVER_ERROR\n");
      }
}

} // namespace

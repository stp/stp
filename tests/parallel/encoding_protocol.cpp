/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

// Encoding coordinator protocol boundaries, including answers written by a
// worker before its owner was stopped.
#include "../../tools/stp-p/EncodingGroups.cpp"
#include <gtest/gtest.h>
using namespace stpp;

TEST(EncodingProtocol, ADecisionNoteDecidesBeforeTheOwnerExits)
{
  Groups state;
  state.groups.resize(1);
  int pipe[2];
  ASSERT_EQ(pipe2(pipe, O_CLOEXEC | O_NONBLOCK), 0);
  auto& group = state.groups[0];
  group.fd = pipe[0];
  write_bounded(pipe[1], "{\"note\":{\"decided\":\"sat\",\"by\":\"root 0\"}}\n",
                now() + 1);
  Options options;
  observe(group, options, 0);
  EXPECT_EQ(group.decision, "sat");
  EXPECT_FALSE(group.done);
  EXPECT_FALSE(group.eof);
  close(pipe[1]);
}

TEST(EncodingProtocol, AConflictingRootReportIsStillComparedAfterCancellation)
{
  Groups state;
  state.groups.resize(2);
  state.groups[0].channel.evidence.push_back({{"decided", "sat"}});
  state.groups[1].cancelled = true;
  state.groups[1].channel.evidence.push_back(
      {{"root", 1}, {"answer", "unsat"}});
  EXPECT_THROW(consistent(state), Failure);
  state.groups[1].channel.evidence.clear();
  state.groups[1].report = {{"answer", "unsat"}};
  EXPECT_THROW(consistent(state), Failure);
}

TEST(EncodingProtocol, APlainRootNoteCannotDecideAndFatalReportsAreNotMasked)
{
  Groups state;
  state.groups.resize(2);
  state.groups[0].channel.evidence.push_back({{"root", 0}, {"answer", "sat"}});
  Options options;
  observe(state.groups[0], options, 0);
  EXPECT_TRUE(state.groups[0].decision.empty());
  state.groups[1].report = {{"error", "broken handoff"}, {"fatal", true}};
  EXPECT_THROW(consistent(state), Failure);
}

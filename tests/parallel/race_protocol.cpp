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

// The race's report boundaries, on parsed reports and on real forked
// processes, from the inside: Race.cpp is compiled into this test.
#include "../../tools/stp-p/Race.cpp"
#include <gtest/gtest.h>
using namespace stpp;
namespace
{
Side report(const std::string& line, bool normal = true)
{
  Side s; s.done = s.eof = true; s.normal = normal;
  s.channel.take(line.data(), line.size()); s.channel.end();
  parse_report(s); return s;
}
template <class F> bool fails(F f)
{
  try { f(); } catch (const Failure&) { return true; }
  return false;
}
// A real side: writes `lines` and then exits with `code`, or waits to be
// killed (code < 0).
void launch(Children& c, unsigned i, const std::string& lines, int code)
{
  int fds[2];
  ASSERT_EQ(pipe2(fds, O_CLOEXEC | O_NONBLOCK), 0);
  auto& s = c.sides[i]; s.read_fd = fds[0];
  const pid_t parent = getpid(); s.pid = fork();
  ASSERT_GE(s.pid, 0);
  if (!s.pid)
  {
    parent_death(parent); close(fds[0]);
    try { write_bounded(fds[1], lines, now() + 3); } catch (...) { _exit(2); }
    if (code >= 0) _exit(code);
    for (;;) pause();
  }
  close(fds[1]);
}
} // namespace

TEST(RaceProtocol, OnlyACompleteReportOfANormalExitDecides)
{
  EXPECT_EQ(answer(report("{\"answer\":\"sat\"}\n")), "sat");
  EXPECT_EQ(answer(report("{\"answer\":\"unsat\"}\n", false)), "unknown") << "a killed side decides nothing";
  EXPECT_EQ(answer(report("{broken\n")), "unknown");
  EXPECT_EQ(answer(report("[]\n")), "unknown");
  EXPECT_EQ(answer(report("{\"answer\":7}\n")), "unknown");
  EXPECT_EQ(answer(report("{\"answer\":\"unsat\",\"error\":\"failed\"}\n")), "unknown");
}

TEST(RaceProtocol, EveryCompleteAnswerInHandIsEvidence)
{
  Children c;
  c.sides = {report("{\"answer\":\"sat\"}\n"), report("{\"answer\":\"unsat\"}\n")};
  EXPECT_TRUE(fails([&] { consistent(c); })) << "two decisions disagree";
  // A side killed after it wrote its report, and the answers a side passed
  // on as evidence.
  c.sides = {report("{\"answer\":\"sat\"}\n"), report("{\"answer\":\"unsat\"}\n", false)};
  EXPECT_TRUE(fails([&] { consistent(c); })) << "a killed side's report is evidence";
  c.sides[1] = report("{\"note\":{\"root\":1,\"answer\":\"unsat\"}}\n{\"answer\":\"unknown\"}\n");
  c.sides[1].role = Role::Ordinary;
  EXPECT_TRUE(fails([&] { consistent(c); })) << "a side's evidence is compared";
  c.sides[1] = report("{\"note\":{\"root\":1,\"failed\":\"signal 11\"}}\n{\"answer\":\"unknown\"}\n");
  EXPECT_NO_THROW(consistent(c)) << "a failure is no answer";
}

TEST(RaceProtocol, AFatalReportEndsTheRaceAndAnErrorIsAFailedSide)
{
  Children c;
  c.sides = {report("{\"answer\":\"sat\"}\n"),
             report("{\"error\":\"answers disagree\",\"fatal\":true}\n", false)};
  c.sides[0].role = Role::Retained;
  c.sides[1].role = Role::Ordinary;
  bool refused = false;
  try { refuse_fatal(c); } catch (const Failure& f) { refused = std::string(f.what()) == "answers disagree"; }
  EXPECT_TRUE(refused);
  c.sides[1] = report("{\"error\":\"setup failed\"}\n", false);
  c.sides[1].role = Role::Ordinary;
  EXPECT_NO_THROW(refuse_fatal(c));
  EXPECT_NO_THROW(consistent(c));
  EXPECT_EQ(answer(c.sides[0]), "sat");
  EXPECT_EQ(answer(c.sides[1]), "unknown");
}

// A side that dies on its own without a report is passed on once, with how
// it ended: its death is in the stats even when the run ends at the deadline
// before the race reports.
TEST(RaceProtocol, ASideThatDiesWithoutAReportIsPassedOn)
{
  Children c; c.sides.resize(1);
  launch(c, 0, "", 3);
  std::vector<Json> forwarded;
  const double deadline = now() + 4;
  while (!c.sides[0].parsed && now() < deadline)
  {
    observe(c.sides[0], [&](const Json& e) { forwarded.push_back(e); });
    poll(nullptr, 0, 1);
  }
  observe(c.sides[0], [&](const Json& e) { forwarded.push_back(e); });
  ASSERT_EQ(forwarded.size(), 1u);
  EXPECT_EQ(forwarded[0]["side"], "ordinary-root");
  EXPECT_EQ(forwarded[0]["failed"], "ordinary-root exited 3");
  settle(c, nullptr);
}

TEST(RaceProtocol, ASideWithoutAReportSaysHowItEnded)
{
  Side s; s.role = Role::Retained; s.fork_error = strerror(EAGAIN);
  EXPECT_EQ(death(s), "retained-root could not be forked: " + std::string(strerror(EAGAIN)));
  Side t; t.role = Role::Ordinary; t.wait_code = CLD_KILLED; t.wait_value = 9;
  EXPECT_EQ(death(t), "ordinary-root died, signal 9");
}

TEST(RaceProtocol, AnOversizedPeerLeavesACompletePeerEligible)
{
  Children c; c.sides.resize(2);
  launch(c, 0, std::string(3 * 1024 * 1024, 'x'), 0);
  launch(c, 1, "{\"answer\":\"sat\"}\n", 0);
  const double deadline = now() + 4;
  while ((!c.sides[0].parsed || !c.sides[1].parsed) && now() < deadline)
  {
    for (auto& s : c.sides) observe(s);
    poll(nullptr, 0, 1);
  }
  EXPECT_TRUE(c.sides[0].invalid);
  EXPECT_EQ(answer(c.sides[0]), "unknown");
  EXPECT_EQ(answer(c.sides[1]), "sat");
  EXPECT_TRUE(settle(c, nullptr));
  EXPECT_EQ(answer(c.sides[1]), "sat") << "after cleanup";
}

// After the race: a report that was in a side's pipe when it was killed is
// drained and compared, never left unread.
TEST(RaceProtocol, AReportQueuedBeforeTheKillIsCompared)
{
  Children c; c.sides.resize(2);
  c.sides[0].role = Role::Retained;
  c.sides[1].role = Role::Ordinary;
  launch(c, 0, "{\"answer\":\"sat\"}\n", 0);
  launch(c, 1, "{\"answer\":\"unsat\"}\n", -1);
  poll(nullptr, 0, 200);
  EXPECT_TRUE(fails([&] { settle(c, nullptr); }));
}

// Evidence records go on to this process's parent as they arrive, each
// naming its side.
TEST(RaceProtocol, EvidenceIsPassedOnAsItArrives)
{
  Children c; c.sides.resize(1);
  c.sides[0].role = Role::Ordinary;
  launch(c, 0, "{\"note\":{\"root\":0,\"answer\":\"sat\"}}\n", -1);
  std::vector<Json> forwarded;
  const double deadline = now() + 4;
  while (forwarded.empty() && now() < deadline)
  {
    observe(c.sides[0], [&](const Json& e) { forwarded.push_back(e); });
    poll(nullptr, 0, 1);
  }
  ASSERT_EQ(forwarded.size(), 1u);
  EXPECT_EQ(forwarded[0]["side"], "ordinary-root");
  EXPECT_EQ(forwarded[0]["answer"], "sat");
  settle(c, nullptr);
}

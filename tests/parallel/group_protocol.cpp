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

// The batch group's report boundaries, on real forked processes: a root's
// report complete before the group kills it still counts, and the group's
// parent hears of each root's answer or death as it happens. BatchGroup.cpp
// is compiled into this test.
#include "../../tools/stp-p/BatchGroup.cpp"
#include <gtest/gtest.h>
#include <csignal>
using namespace stpp;
namespace
{
// A root (or the hedge) that writes `line` and then exits 0, waits to be
// killed (`wait`), or raises SIGSEGV (`crash`).
enum class After { Exit, Wait, Crash };
Root launch(unsigned slot, const std::string& line, After after, bool hedge = false)
{
  int fds[2];
  if (pipe2(fds, O_CLOEXEC | O_NONBLOCK))
    throw std::runtime_error("pipe");
  Root c;
  c.slot = slot;
  c.hedge = hedge;
  c.fd = fds[0];
  const pid_t parent = getpid();
  c.pid = fork();
  if (c.pid < 0)
    throw std::runtime_error("fork");
  if (!c.pid)
  {
    parent_death(parent);
    close(fds[0]);
    try
    {
      if (!line.empty())
        write_bounded(fds[1], line, now() + 3);
    }
    catch (...)
    {
      _exit(2);
    }
    if (after == After::Crash)
    {
      signal(SIGSEGV, SIG_DFL);
      raise(SIGSEGV);
    }
    if (after == After::Exit)
      _exit(0);
    for (;;)
      pause();
  }
  close(fds[1]);
  return c;
}
} // namespace

// Root 1's report is in its pipe when the group stops it: settle reads it
// after the kill, and the disagreement ends the invocation.
TEST(GroupProtocol, AReportCompleteBeforeTheKillIsCompared)
{
  std::vector<Json> notes;
  Options o;
  o.note = [&](const Json& e) { notes.push_back(e); };
  std::vector<Root> roots;
  roots.push_back(launch(0, "{\"answer\":\"unsat\"}\n", After::Exit));
  roots.push_back(launch(1, "{\"answer\":\"sat\"}\n", After::Wait));
  poll(nullptr, 0, 200);
  bool refused = false;
  try
  {
    settle(roots, o);
  }
  catch (const Failure& f)
  {
    refused = std::string(f.what()) == disagreement &&
              f.evidence["children"].size() == 2;
  }
  EXPECT_TRUE(refused);
  // A killed root's report is evidence, not a decision.
  EXPECT_EQ(decided(roots[0]), "unsat");
  EXPECT_EQ(decided(roots[1]), "unknown");
  EXPECT_EQ(reported(roots[1]), "sat");
  EXPECT_EQ(notes.size(), 2u) << "each root's answer is passed on once";
  for (auto& c : roots)
    close(c.fd);
}

// A root that dies on its own, without a report, is passed on as a failure;
// one that agrees is passed on as its answer.
TEST(GroupProtocol, DeathsAndAnswersArePassedOn)
{
  std::vector<Json> notes;
  Options o;
  o.note = [&](const Json& e) { notes.push_back(e); };
  std::vector<Root> roots;
  roots.push_back(launch(0, "", After::Crash));
  roots.push_back(launch(1, "{\"answer\":\"sat\"}\n", After::Exit));
  for (const double until = now() + 4;
       now() < until && !(roots[0].reaped && roots[1].reaped);)
  {
    for (auto& c : roots)
      observe(c, o);
    poll(nullptr, 0, 2);
  }
  settle(roots, o);
  bool crashed = false, answered = false;
  for (const auto& n : notes)
  {
    crashed = crashed || (n["root"] == 0 && n.value("failed", "") == "signal 11");
    answered = answered || (n["root"] == 1 && n.value("answer", "") == "sat");
  }
  EXPECT_TRUE(crashed);
  EXPECT_TRUE(answered);
  EXPECT_EQ(notes.size(), 2u);
  for (auto& c : roots)
    close(c.fd);
}

// The hedge's report is compared with the roots', and the owner's own
// answer with both.
TEST(GroupProtocol, TheHedgeAndTheOwnerAreCompared)
{
  Options o;
  std::vector<Root> group;
  group.push_back(launch(0, "{\"answer\":\"unsat\"}\n", After::Exit, true));
  group.push_back(launch(0, "{\"answer\":\"sat\"}\n", After::Wait));
  poll(nullptr, 0, 200);
  bool refused = false;
  try
  {
    settle(group, o);
  }
  catch (const Failure& f)
  {
    refused = std::string(f.what()) == disagreement &&
              f.evidence["children"][0]["role"] == "hedge";
  }
  EXPECT_TRUE(refused) << "the hedge against a root";
  for (auto& c : group)
    close(c.fd);
  std::vector<Root> one;
  one.push_back(launch(1, "{\"answer\":\"unsat\"}\n", After::Exit));
  poll(nullptr, 0, 200);
  refused = false;
  try
  {
    settle(one, o, "sat");
  }
  catch (const Failure& f)
  {
    refused = f.evidence["owner_answer"] == "sat";
  }
  EXPECT_TRUE(refused) << "the owner's answer against a root";
  for (auto& c : one)
    close(c.fd);
}

// A process that ends with an unknown report of its own has answered
// unknown, with its reason: it is passed on as ended, not as failed.
TEST(GroupProtocol, AnUnknownIsAnAnswerNotAFailure)
{
  std::vector<Json> notes;
  Options o;
  o.note = [&](const Json& e) { notes.push_back(e); };
  std::vector<Root> roots;
  roots.push_back(launch(0, "{\"answer\":\"unknown\",\"reason\":\"carrier\"}\n",
                         After::Exit));
  roots.push_back(launch(1, "{\"error\":\"root setup failed: x\"}\n", After::Exit));
  for (const double until = now() + 4;
       now() < until && !(roots[0].reaped && roots[1].reaped);)
  {
    for (auto& c : roots)
      observe(c, o);
    poll(nullptr, 0, 2);
  }
  settle(roots, o);
  EXPECT_EQ(failure(roots[0]), "");
  EXPECT_EQ(failure(roots[1]), "root setup failed: x");
  ASSERT_EQ(notes.size(), 2u);
  for (const auto& n : notes)
    if (n["root"] == 0)
      EXPECT_EQ(n.value("ended", ""), "carrier");
    else
      EXPECT_EQ(n.value("failed", ""), "root setup failed: x");
  for (auto& c : roots)
    close(c.fd);
}

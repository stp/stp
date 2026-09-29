/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// c-runs.cpp -- the C twins of an input run as the stp command line runs it:
// a text source as the input, PARSE_ONLY, the output sink and its flushes,
// the fatal error handler, the CNF sink and an input printed back.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

namespace
{
struct Session
{
  stp_tm tm;
  stp_solver s;
  Session()
  {
    tm = stp_tm_new(nullptr);
    s = stp_solver_new(tm, nullptr);
  }
  ~Session()
  {
    stp_solver_delete(s);
    stp_tm_release(tm);
  }
};

// What the sinks heard.
struct Heard
{
  std::string out, err, fatal;
  size_t flushes = 0;
  std::vector<std::pair<std::string, stp_cnf_scope>> cnfs;
};

void out_sink(const char* text, size_t len, void* user)
{
  Heard* h = static_cast<Heard*>(user);
  if (len == 0)
    ++h->flushes;
  h->out.append(text, len);
}

void err_sink(const char* text, size_t len, void* user)
{
  static_cast<Heard*>(user)->err.append(text, len);
}

void on_fatal(const char* message, void* user)
{
  static_cast<Heard*>(user)->fatal += message;
}

void cnf_sink(const char* dimacs, size_t len, stp_cnf_scope scope, void* user)
{
  static_cast<Heard*>(user)->cnfs.emplace_back(std::string(dimacs, len), scope);
}

void attach(stp_solver s, Heard& h)
{
  stp_solver_set_output_sink(s, out_sink, &h);
  stp_solver_set_diagnostic_sink(s, err_sink, &h);
  stp_solver_set_fatal_error_handler(s, on_fatal, &h);
  stp_solver_set_cnf_sink(s, cnf_sink, &h);
}

// A text source over lines: one per call; `fail_after` lines, then a failure.
struct Lines
{
  std::vector<std::string> lines;
  size_t next = 0;
  size_t fail_after = static_cast<size_t>(-1);
};

size_t read_lines(char* buf, size_t max, void* user)
{
  Lines* l = static_cast<Lines*>(user);
  if (l->next == l->fail_after)
    return static_cast<size_t>(-1);
  if (l->next == l->lines.size())
    return 0;
  const std::string& line = l->lines[l->next++];
  const size_t n = line.size() < max ? line.size() : max;
  std::memcpy(buf, line.data(), n);
  return n;
}
} // namespace

TEST(c_runs, a_source_is_read_and_executed)
{
  Session a;
  Heard h;
  attach(a.s, h);
  Lines l{{"(declare-fun a () (_ BitVec 8))\n", "(declare-fun b () (_ BitVec 8))\n",
           "(assert (= (bvmul a b) #x0f))\n", "(assert (bvugt a #x01))\n",
           "(assert (bvugt b #x01))\n", "(check-sat)\n"}};
  ASSERT_EQ(STP_OK, stp_solver_parse_source(a.s, read_lines, &l, STP_FORMAT_AUTO, STP_PARSE_EXECUTE));
  EXPECT_EQ("sat\n", h.out);
  EXPECT_GT(h.flushes, 0u);
  ASSERT_FALSE(h.cnfs.empty());
  EXPECT_NE(std::string::npos, h.cnfs[0].first.find("\np cnf "));
  EXPECT_EQ(STP_CNF_WHOLE, h.cnfs[0].second);
}

TEST(c_runs, a_failed_source_is_an_io_error)
{
  Session a;
  Lines l{{"(declare-fun a () Bool)\n", "(assert a)\n"}};
  l.fail_after = 1;
  EXPECT_EQ(STP_ERROR, stp_solver_parse_source(a.s, read_lines, &l, STP_FORMAT_SMTLIB2, STP_PARSE_EXECUTE));
  EXPECT_EQ(STP_ERR_IO, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
  EXPECT_EQ(0u, stp_solver_num_assertions(a.s));
  // no source, or no such mode
  EXPECT_EQ(STP_ERROR, stp_solver_parse_source(a.s, nullptr, nullptr, STP_FORMAT_SMTLIB2, STP_PARSE_EXECUTE));
  EXPECT_EQ(STP_ERR_NULL_HANDLE, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
  Lines empty;
  EXPECT_EQ(STP_ERROR, stp_solver_parse_source(a.s, read_lines, &empty, STP_FORMAT_SMTLIB2,
                                               static_cast<stp_parse_mode>(9)));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
}

TEST(c_runs, parse_only_decides_nothing)
{
  Session a;
  Heard h;
  attach(a.s, h);
  Lines l{{"(declare-fun x () (_ BitVec 8))\n", "(assert (= x #x05))\n", "(check-sat)\n"}};
  ASSERT_EQ(STP_OK, stp_solver_parse_source(a.s, read_lines, &l, STP_FORMAT_SMTLIB2, STP_PARSE_ONLY));
  EXPECT_EQ("", h.out); // nothing decided
  EXPECT_EQ(1u, stp_solver_num_assertions(a.s));
  // PARSE_ONLY through parse_smt2: the commands run, the check does not
  Heard h2;
  attach(a.s, h2);
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(a.s, "(declare-fun p () Bool)(assert p)(check-sat)(echo \"done\")",
                                          STP_PARSE_ONLY));
  EXPECT_EQ("\"done\"\n", h2.out);
}

TEST(c_runs, execute_answers_a_script_from_a_source)
{
  Session a;
  Heard h;
  attach(a.s, h);
  Lines l{{"(declare-fun x () (_ BitVec 8))\n", "(assert (= x #x05))\n", "(assert (not (= x #x05)))\n",
           "(check-sat)\n"}};
  ASSERT_EQ(STP_OK, stp_solver_parse_source(a.s, read_lines, &l, STP_FORMAT_SMTLIB2, STP_PARSE_EXECUTE));
  EXPECT_EQ("unsat\n", h.out);
}

TEST(c_runs, the_fatal_error_handler_hears_first)
{
  Session a;
  Heard h;
  attach(a.s, h);
  Lines l{{"(declare-fun x () (_ BitVec 0))\n"}};
  EXPECT_EQ(STP_ERROR, stp_solver_parse_source(a.s, read_lines, &l, STP_FORMAT_SMTLIB2, STP_PARSE_EXECUTE));
  EXPECT_EQ(STP_ERR_PARSE, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
  EXPECT_NE(std::string::npos, h.fatal.find("bit-vectors must be of positive length")) << h.fatal;
  EXPECT_NE(std::string::npos, h.err.find("Fatal Error: " + h.fatal)) << h.err;
  // cleared: nobody is told
  stp_solver_set_fatal_error_handler(a.s, nullptr, nullptr);
  Lines again{{"(declare-fun y () (_ BitVec 0))\n"}};
  h.fatal.clear();
  EXPECT_EQ(STP_ERROR, stp_solver_parse_source(a.s, read_lines, &again, STP_FORMAT_SMTLIB2, STP_PARSE_EXECUTE));
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
  EXPECT_EQ("", h.fatal);
}

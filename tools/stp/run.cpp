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

// run.cpp -- the stp binary's run of its input over the 3.x API.
//
// The library prints nothing of its own; the binary's sinks put what the
// solver says where stp always put it: the output on stdout (line buffered),
// the diagnostics on stderr, and a fatal error's report followed by
// "STP Error:" and exit status -1. The input is read as the parsers read
// their FILE*: a line at a time when interactive, in blocks otherwise.

#include "run.h"

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <istream>
#include <streambuf>
#include <string>
#include <string_view>

namespace stp_cli
{
namespace
{

// The input from its FILE*, as the lexers read it before the library read a
// stream: when interactive, a character at a time up to the end of a line
// (a program driving stp over a pipe waits for each answer), and otherwise
// in blocks. A read that fails is the lexers' "input in flex scanner
// failed": the stream goes bad, and the parse fails with IO.
class FileInput final : public std::streambuf
{
public:
  FileInput(std::FILE* file, bool interactive) : file_(file), interactive_(interactive) {}

protected:
  int_type underflow() override
  {
    if (gptr() < egptr())
      return traits_type::to_int_type(*gptr());
    std::size_t n = 0;
    if (interactive_)
    {
      int c = '*';
      while (n < sizeof buf_ && (c = std::getc(file_)) != EOF && c != '\n')
        buf_[n++] = static_cast<char>(c);
      if (c == '\n')
        buf_[n++] = static_cast<char>(c);
      if (c == EOF && std::ferror(file_))
        throw std::ios_base::failure("input in flex scanner failed");
    }
    else
    {
      errno = 0;
      while ((n = std::fread(buf_, 1, sizeof buf_, file_)) == 0 && std::ferror(file_))
      {
        if (errno != EINTR)
          throw std::ios_base::failure("input in flex scanner failed");
        errno = 0;
        std::clearerr(file_);
      }
    }
    if (n == 0)
      return traits_type::eof();
    setg(buf_, buf_, buf_ + n);
    return traits_type::to_int_type(*gptr());
  }

private:
  std::FILE* file_;
  bool interactive_;
  char buf_[8192];
};

void write_output(std::string_view text)
{
  if (text.empty())
    std::fflush(stdout);
  else
    std::fwrite(text.data(), 1, text.size(), stdout);
}

void write_diagnostic(std::string_view text)
{
  std::fwrite(text.data(), 1, text.size(), stderr);
}

// A fatal error has been reported ("Fatal Error: ..." on stderr): stp says
// so again and stops, before anything unwinds.
[[noreturn]] void fatal_exit(std::string_view message)
{
  std::cerr << "STP Error: " << message << std::endl;
  std::exit(-1);
}

// A refusal stp reported as a fatal error of its own.
[[noreturn]] void refuse_fatally(const std::string& message)
{
  std::cerr << "Fatal Error: " << message << std::endl;
  fatal_exit(message);
}

// Where --output-CNF writes: output_0.cnf, output_1.cnf, ... in the working
// directory, one per CNF, with the warning a partial CNF has always carried.
void write_cnf_file(unsigned& counter, std::string_view dimacs, stp::CnfScope scope)
{
  const std::string name = "output_" + std::to_string(counter++) + ".cnf";
  std::ofstream out(name.c_str());
  if (!out)
  {
    std::cerr << "Warning: could not open " << name << " for writing." << std::endl;
    return;
  }
  out.write(dimacs.data(), static_cast<std::streamsize>(dimacs.size()));
  const char* what = "the CNF written by --output-CNF";
  if (scope == stp::CnfScope::PARTIAL)
    std::cerr << "Warning: " << what << " is partial: a refinement (of array"
              << " reads, uninterpreted functions, Real arithmetic or the"
              << " floating-point abstraction) adds what the search asks for as"
              << " it goes. --ackermanize puts the array axioms in up front,"
              << " which makes the CNF whole when arrays are the only"
              << " refinement." << std::endl;
  else if (scope == stp::CnfScope::OVER_APPROXIMATION)
    std::cerr << "Warning: " << what << " is an over-approximation of the query:"
              << " --bv-eq-abstraction and --bv-term-abstraction replace"
              << " operations with free inputs that refinement pins later. No"
              << " flag completes this CNF; turn the abstraction off to get one"
              << " that is the whole query." << std::endl;
}

} // namespace

void print_version()
{
  const stp::Version v = stp::version();
  std::cout << "STP version " << v.git_tag << std::endl;
  std::cout << "STP version SHA string " << v.git_sha << std::endl;
  std::cout << "STP compilation options " << v.build_info << std::endl;

  // Which SAT library is behind the build is not otherwise visible from
  // outside it, and it changes the answers -- so it belongs next to the STP
  // version rather than buried in a --verbose solve.
  const std::string solvers = stp::capabilities()["sat.versions"];
  std::cout << "STP SAT solvers " << (solvers.empty() ? std::string("none") : solvers)
            << std::endl;

#ifdef __GNUC__
  std::cout << "c compiled with gcc version " << __VERSION__ << std::endl;
#else
  std::cout << "c compiled with non-gcc compiler" << std::endl;
#endif
}

int run(const Invocation& in, std::unique_ptr<stp::Solver> owned)
{
  // ensure that all output is (at most) line buffered
  // A size of 0 is rejected by MSVC's CRT (fatal invalid-parameter error);
  // it requires 2 <= size <= INT_MAX.
  std::setvbuf(stdout, nullptr, _IOLBF, BUFSIZ);

  stp::Solver& solver = *owned;
  solver.set_output_sink(write_output);
  solver.set_diagnostic_sink(write_diagnostic);
  solver.set_fatal_error_handler(fatal_exit);

  // Every CNF --output-CNF writes, and whether one ended the run
  // (--exit-after-CNF, the solver's end-after-cnf).
  unsigned cnf_files = 0;
  bool cnf_generated = false;
  if (in.output_cnf || in.exit_after_cnf)
    solver.set_cnf_sink([&](std::string_view dimacs, stp::CnfScope scope) {
      cnf_generated = true;
      if (in.output_cnf)
        write_cnf_file(cnf_files, dimacs, scope);
    });

  std::FILE* file = stdin;
  if (!in.infile.empty())
  {
    file = std::fopen(in.infile.c_str(), "r");
    if (file == nullptr)
      refuse_fatally("Cannot open " + in.infile);
  }

  // The lexer reads a line at a time by default when the input is standard
  // input, or as --interactive says.
  const bool interactive = in.interactive.has_value() ? *in.interactive : in.infile.empty();
  FileInput input_buffer(file, interactive);
  std::istream input(&input_buffer);

  const stp::ParseMode mode = in.parse_only ? stp::ParseMode::PARSE_ONLY : stp::ParseMode::EXECUTE;
  try
  {
    solver.parse(input, stp::Format::SMTLIB2, mode);
  }
  catch (const stp::Error& e)
  {
    switch (e.code())
    {
      case stp::ErrorCode::IO:
        std::fputs("input in flex scanner failed\n", stderr);
        std::exit(2);
      case stp::ErrorCode::PARSE:
        // The parser has said why, as a response or a fatal error; what
        // remains is the status of the run as a whole. Scripted callers have
        // no other way to tell a rejected input from a solved one, and a
        // script may legitimately have answered several check-sats before
        // the command that broke -- those answers stand.
        std::exit(-1);
      default:
        fatal_exit(e.what());
    }
  }
  if (file != stdin)
    std::fclose(file);

  // The run ended at its first CNF, as the process once did there: nothing
  // more is said.
  if (in.exit_after_cnf && cnf_generated)
    std::exit(0);

#ifdef NDEBUG
  // The teardown frees every node of the run, which after a large input
  // takes a good part of what the answer did; the process is ending anyway,
  // so a release build leaves it undone, as the command line always did.
  // What the solver's teardown says -- a Real session's statistics, the
  // floating-point abstraction's -- it says under -s alone, so under -s the
  // solver still goes first. A build with assertions tears everything down,
  // and checks it.
  if (in.statistics)
    owned.reset();
  std::exit(0);
#else
  // What the solver's teardown says (under -s) is said before the manager
  // goes.
  owned.reset();
  return 0;
#endif
}

} // namespace stp_cli

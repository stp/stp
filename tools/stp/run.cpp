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
#include <vector>

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

// The parser's own diagnostic in a PARSE error's text, which the API wraps
// as "parse error[ at L:C]: <diagnostic> [PARSE]".
std::string parser_diagnostic(const stp::Error& e)
{
  std::string_view text = e.what();
  const std::string_view head = "parse error", tail = " [PARSE]";
  const std::size_t colon = text.find(": ");
  if (text.substr(0, head.size()) == head && colon != std::string_view::npos)
    text.remove_prefix(colon + 2);
  if (text.size() >= tail.size() && text.substr(text.size() - tail.size()) == tail)
    text.remove_suffix(tail.size());
  return std::string(text);
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
    std::cerr << "Warning: " << what << " is partial: array read refinement adds"
              << " its congruence axioms as the search asks for them. Use"
              << " --ackermanize to have them all up front." << std::endl;
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

  const bool print_back = in.print_back() && !in.parse_only;
  if (in.print_back() && in.format == stp::Format::SMTLIB2)
  {
    std::cerr << "Printback from SMTLIB2 inputs isn't currently working." << std::endl;
    std::cerr << "Please try again later" << std::endl;
    std::cerr << "It works prior to revision 1354" << std::endl;
    std::exit(1);
  }

  // Only the SMT-LIB 2 lexer reads a line at a time: by default when the
  // input is standard input, or as --interactive says.
  bool interactive = false;
  if (in.format == stp::Format::SMTLIB2)
    interactive = in.interactive.has_value() ? *in.interactive : in.infile.empty();
  FileInput input_buffer(file, interactive);
  std::istream input(&input_buffer);

  const stp::ParseMode mode =
      in.parse_only || print_back ? stp::ParseMode::PARSE_ONLY : stp::ParseMode::EXECUTE;
  try
  {
    solver.parse(input, in.format, mode);
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
        // the command that broke -- those answers stand. A CVC or SMT-LIB 1
        // input's refusal was a fatal error, whose two lines follow the
        // parser's own.
        if (in.format != stp::Format::SMTLIB2)
          refuse_fatally(parser_diagnostic(e));
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

  if (print_back)
  {
    std::vector<stp::Format> formats;
    const bool smtlib1 = in.format == stp::Format::SMTLIB1;
    if (in.print_back_cvc || (in.print_stpinput && !smtlib1))
      formats.push_back(stp::Format::CVC);
    if (in.print_back_smtlib2 || (in.print_stpinput && smtlib1))
      formats.push_back(stp::Format::SMTLIB2);
    if (in.print_back_gdl)
      formats.push_back(stp::Format::GDL);
    if (in.print_back_dot)
      formats.push_back(stp::Format::DOT);
    for (stp::Format f : formats)
    {
      std::string text;
      try
      {
        text = solver.input_to_string(f);
      }
      catch (const stp::Error& e)
      {
        // A CVC input without a query has no question to print back.
        if (e.code() != stp::ErrorCode::STATE)
          fatal_exit(e.what());
        refuse_fatally("Input is Empty. Please enter some asserts and query\n");
      }
      write_output(text);
    }
    std::fflush(stdout);
  }

  // What stp's teardown says (a Real session's -s statistics) is said as the
  // solver goes, and before the manager does.
  owned.reset();
  return 0;
}

} // namespace stp_cli

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

// run.h -- the stp binary's run of its input over the 3.x API, once the
// command line (main.cpp) has made the solver and decided the rest.

#ifndef STP_TOOLS_RUN_H
#define STP_TOOLS_RUN_H

#include <stp/stp.hpp>

#include <memory>
#include <optional>
#include <string>

namespace stp_cli
{

// What the command line asked for besides the solver's options: the frontend
// rows of the option registry.
struct Invocation
{
  std::string infile; // empty: standard input
  // The parser: --CVC, --SMTLIB1 or --SMTLIB2, or else the file's extension.
  stp::Format format = stp::Format::SMTLIB2;
  std::optional<bool> interactive; // --interactive, when it was given
  bool parse_only = false;
  bool exit_after_cnf = false;
  bool output_cnf = false;
  bool print_output = false; // -n: the answers are printed regardless
  bool print_stpinput = false; // -b: the input back, in CVC (SMT-LIB 2 for SMT-LIB 1)
  bool print_back_cvc = false;
  bool print_back_smtlib2 = false;
  bool print_back_gdl = false;
  bool print_back_dot = false;

  bool print_back() const
  {
    return print_stpinput || print_back_cvc || print_back_smtlib2 || print_back_gdl ||
           print_back_dot;
  }
};

// Reads the input into `solver` and runs it; the process's exit status.
// Ends the process itself on the paths that always did (a fatal error, an
// input that cannot be read, the end of the run at the first CNF).
int run(const Invocation& invocation, std::unique_ptr<stp::Solver> solver);

// --version.
void print_version();

} // namespace stp_cli

#endif

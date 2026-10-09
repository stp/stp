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

#pragma once
#include "Common.h"
#include <string_view>
namespace stpp
{
// The query's bytes, read once by the supervisor before anything is forked:
// a regular file is mapped read-only; standard input (or any other stream)
// is spooled into anonymous memory that grows in place (mremap), so that
// the source is never copied while it grows and no file-size limit applies
// to it. Both count against the process's address space. Read-only from
// then on: a forked process shares its pages until it releases them.
class Source
{
public:
  Source() = default;
  explicit Source(std::string text) : heap(std::move(text)) {}
  ~Source();
  Source(const Source&) = delete;
  Source& operator=(const Source&) = delete;
  std::string_view text() const
  {
    return map ? std::string_view(static_cast<const char*>(map), size)
               : std::string_view(heap);
  }
  void release(); // the bytes go; text() is empty from here on

private:
  friend bool read_source(const std::string&, Source&, std::uint64_t, double,
                          const volatile int&);
  std::string heap;
  void* map = nullptr;
  std::size_t size = 0, mapped = 0; // the text's bytes; the mapping's
};
// The whole input: a file, or stdin for "-". At most `limit` bytes: a larger
// input is an error (the process that parses it could not hold it), as is
// one that cannot be mapped or spooled (an address-space limit: the error
// says so). Returns false when `deadline` passes or `stop` becomes nonzero
// first.
bool read_source(const std::string& path, Source& out, std::uint64_t limit,
                 double deadline, const volatile int& stop);
// The bound read_source is given: the per-process address space
// (--worker-memory-mib), or 16 GiB, its default, when that is 0.
std::uint64_t input_limit(const Options&);

// The query, parsed into `solver` by STP's own parser in its single-query
// mode (stp::ParseMode::SINGLE_QUERY): declarations, definitions and
// assertions are applied, the one check-sat is not run, and anything else --
// a stack command, a second check-sat, an option the solver's configuration
// would take, a late set-logic -- is a stp::Error of code PARSE that names
// the command and its line. A NUL anywhere is refused before the parse. The
// parse reads the source where it is, without a copy, and then releases it.
// Returns the logic the script named in its set-logic, "" when it named
// none.
std::string parse_query(stp::Solver& solver, Source& source);
// The logics a route takes: QF_BV, and on the routes that run ordinary STP's
// own pipeline (`theories`) also QF_ABV, QF_FP, QF_BVFP and QF_ABVFP; a
// script that names no logic is taken by every route. Anything else is
// refused, after the parse that read the logic.
void admit_logic(const std::string& logic, bool theories);
// Whether the hedge takes the query: QF_BV, named (the hedge's incremental
// driver was chosen for it, and a script with no set-logic may hold any
// theory).
inline bool hedge_logic(const std::string& logic) { return logic == "QF_BV"; }
} // namespace stpp

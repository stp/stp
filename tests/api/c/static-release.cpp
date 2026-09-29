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

// static-release.cpp -- C handles released from the destructor of a global
// object, which runs at exit after every static constructed later: the C
// layer's own state must still be there. It was a function-local static,
// first used inside main and so destroyed first, and the releases below
// went through a destroyed map and mutex (SIGSEGV at exit).

#include <stp/stp.h>

#include <cstdio>
#include <cstdlib>

namespace
{
struct Holder
{
  stp_tm tm = nullptr;
  stp_solver solver = nullptr;
  stp_term x = nullptr;
  ~Holder()
  {
    stp_term_release(x);
    stp_solver_delete(solver);
    stp_tm_release(tm);
    // the strings stp.h hands out as never freed are still readable
    const stp_version v = stp_get_version();
    const char* backend = stp_num_sat_backends() > 0 ? stp_sat_backend_name(0) : "";
    if (v.string == nullptr || backend == nullptr)
      std::abort();
    std::puts("released");
  }
} holder;
} // namespace

int main()
{
  holder.tm = stp_tm_new(nullptr);
  holder.solver = stp_solver_new(holder.tm, nullptr);
  holder.x = stp_declare(holder.tm, "x", stp_mk_bv_sort(holder.tm, 8));
  return holder.x != nullptr && holder.solver != nullptr ? 0 : 1;
}

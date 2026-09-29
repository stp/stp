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


// threads.cpp -- managers on threads of their own, as a client uses them
// against the installed 3.x C++ API: each thread declares, asserts and checks
// on its own manager, and each model must satisfy that thread's formula.

#include <stp/stp.hpp>

#include <cstdint>
#include <thread>
#include <vector>

int main()
{
  const int threads = 4;
  std::vector<int> failed(threads, 1);
  std::vector<std::thread> pool;
  for (int t = 0; t < threads; ++t)
    pool.emplace_back([t, &failed] {
      stp::TermManager tm;
      stp::Solver s(tm);
      const stp::Term x = tm.declare("x", tm.mk_bv_sort(8));
      const stp::Term y = tm.declare("y", tm.mk_bv_sort(8));
      const std::uint64_t product = 0x21 + 2 * static_cast<std::uint64_t>(t);
      s.add(stp::bvmul(x, y) == tm.mk_bv(8, product));
      s.add(stp::bvult(x, y));
      if (!s.check_sat().is_sat())
        return;
      const stp::Model m = s.model();
      const std::uint64_t vx = m.value(x).to_uint64(), vy = m.value(y).to_uint64();
      failed[t] = (vx * vy) % 256 == product && vx < vy ? 0 : 1;
    });
  for (std::thread& th : pool)
    th.join();
  for (int f : failed)
    if (f != 0)
      return 1;
  return 0;
}

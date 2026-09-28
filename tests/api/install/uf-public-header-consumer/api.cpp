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

// api.cpp -- a C++ program against the installed 3.x C++ API (stp/stp.hpp),
// linking the stp target: 3x = 7 over bytes has one solution, x = 173, and
// no other.

#include <stp/stp.hpp>

int main()
{
  stp::TermManager tm;
  stp::Solver s(tm);
  const stp::Term x = tm.declare("x", tm.mk_bv_sort(8));
  s.add(stp::bvmul(x, tm.mk_bv(8, 3)) == tm.mk_bv(8, 7));
  if (!s.check_sat().is_sat())
    return 1;
  if (s.model().value(x).to_uint64() != 173) // 3 * 173 = 519 = 7 (mod 256)
    return 2;
  s.add(x != tm.mk_bv(8, 173));
  return s.check_sat().is_unsat() ? 0 : 3;
}

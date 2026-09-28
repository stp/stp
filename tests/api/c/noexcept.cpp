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

// A C++ consumer of <stp/stp.h> built with -fno-exceptions -fno-rtti: the C
// header must be usable from such code, and no exception may cross the
// boundary (an escaping one would terminate this program).

#include <stp/stp.h>

#include <cstdio>
#include <cstring>

int main()
{
  int failures = 0;
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_term y = stp_declare(tm, "y", bv8);
  stp_solver s = stp_solver_new(tm, nullptr);
  if (stp_solver_assert(s, stp_eq(tm, stp_bvadd(tm, x, y), stp_mk_bv_uint64(tm, 8, 10))) != STP_OK)
    ++failures;
  if (stp_solver_assert(s, stp_bvult(tm, x, stp_mk_bv_uint64(tm, 8, 3))) != STP_OK)
    ++failures;
  stp_result r;
  if (stp_solver_check_sat(s, &r) != STP_OK || r.kind != STP_SAT)
    ++failures;
  uint64_t xv = 0, yv = 0;
  if (stp_solver_check_sat(s, &r) != STP_OK)
    ++failures;
  stp_model m = stp_solver_model(s);
  if (m == nullptr || stp_model_uint64(m, x, &xv) != STP_OK || stp_model_uint64(m, y, &yv) != STP_OK)
    ++failures;
  if (((xv + yv) & 0xff) != 10 || xv >= 3)
    ++failures;
  // an error must come back as a record, never as an exception
  if (stp_bvadd(tm, x, stp_mk_true(tm)) != nullptr)
    ++failures;
  const stp_error* e = stp_tm_error(tm);
  if (e == nullptr || e->code != STP_ERR_SORT_MISMATCH)
    ++failures;
  if (stp_solver_parse_smt2(s, "(assert (= x", STP_PARSE_DECLARE_AND_ASSERT) != STP_ERROR)
    ++failures;
  if (stp_solver_failed(s) == nullptr || stp_solver_failed(s)->code != STP_ERR_PARSE)
    ++failures;
  stp_model_release(m);
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
  std::printf("%s%d\n", failures ? "FAILURES: " : "all passed: ", failures);
  return failures ? 1 : 0;
}

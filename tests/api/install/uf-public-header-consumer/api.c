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

/* api.c -- a C program against the installed 3.x C API (stp/stp.h), linking
 * the stp target: 3x = 7 over bytes has one solution, x = 173. */

#include <stp/stp.h>

#include <stdio.h>

int main(void)
{
  stp_tm tm = stp_tm_new(NULL);
  if (tm == NULL)
    return 1;
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_term c = stp_eq(tm, stp_bvmul(tm, x, stp_mk_bv_uint64(tm, 8, 3)),
                      stp_mk_bv_uint64(tm, 8, 7));
  stp_solver s = stp_solver_new(tm, NULL);
  int status = 2;
  stp_result r;
  if (s != NULL && stp_solver_assert(s, c) == STP_OK &&
      stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT)
  {
    stp_model m = stp_solver_model(s);
    uint64_t v = 0;
    /* 3 * 173 = 519 = 7 (mod 256) */
    if (m != NULL && stp_model_uint64(m, x, &v) == STP_OK && v == 173)
      status = 0;
    if (m != NULL)
      stp_model_release(m);
  }
  if (stp_tm_error(tm) != NULL)
    fprintf(stderr, "%s\n", stp_tm_error(tm)->message);
  if (s != NULL)
    stp_solver_delete(s);
  stp_tm_release_all(tm);
  stp_tm_release(tm);
  return status;
}

/***********
AUTHORS: Andrew Teylu

BEGIN DATE: Aug, 2026

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
**********************/

#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <cstdio>
#include <gtest/gtest.h>
#include <string>

#ifdef _MSC_VER
#include <io.h>
#define stp_test_fileno _fileno
#define stp_test_lseek _lseek
#define stp_test_read _read
#else
#include <unistd.h>
#define stp_test_fileno fileno
#define stp_test_lseek lseek
#define stp_test_read read
#endif

namespace
{

struct TempFd
{
  FILE* file;
  int fd;

  TempFd() : file(std::tmpfile()), fd(file == NULL ? -1 : stp_test_fileno(file))
  {
  }

  ~TempFd()
  {
    if (file != NULL)
      std::fclose(file);
  }

  std::string contents() const
  {
    std::string all;
    stp_test_lseek(fd, 0, SEEK_SET);
    char chunk[4096];
    for (;;)
    {
      const auto got = stp_test_read(fd, chunk, sizeof(chunk));
      if (got <= 0)
        break;
      all.append(chunk, static_cast<size_t>(got));
    }
    return all;
  }
};

} // namespace

// The C API's counterexample lifetime contract, as its idiomatic usage
// (push / query / pop, then read the model) depends on it:
//
//   - the counterexample describes the last vc_query and SURVIVES vc_pop;
//   - the next vc_push or vc_query discards it.
//
// This is deliberately different from the SMT-LIB frontend, where a pop
// invalidates the model. See vc_pop's documentation in c_interface.h.
TEST(push_pop_model, counterexample_survives_pop_until_next_query)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'c');
  vc_setFlags(vc, 'd');

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr y = vc_varExpr(vc, "y", bv8);

  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 5)));

  // The classic bracket: push, query, pop -- then read the model.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 7)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  // Both values are still readable after the pop.
  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));
  EXPECT_EQ(7ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, y)));

  // A new bracket replaces the model wholesale.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 9)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));
  EXPECT_EQ(9ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, y)));

  // These two queries still used the batch path. Reading their models must
  // not instantiate a persistent SAT backend as a side effect.
  EXPECT_FALSE(((stp::STP*)vc)->hasIncrementalSolver());

  vc_Destroy(vc);
}

// Every counterexample reader must trigger the incremental driver's deferred
// construction. The fd printer used to be the sole exception: after a lazy
// satisfiable solve it printed only the begin/end markers around an empty map.
TEST(push_pop_model, file_printer_materializes_deferred_counterexample)
{
  stp::STPMgr* bm = new stp::STPMgr();
  VC vc = vc_createValidityCheckerReuse(bm);
  vc_setFlags(vc, 'i');

  // vc_createValidityCheckerReuse enables eager counterexample checking for
  // historical C-API compatibility. Recreate SMT-LIB's produce-models mode:
  // the model must be readable, but construction waits for the first reader.
  bm->UserFlags.check_counterexample_flag = false;
  bm->UserFlags.construct_counterexample_flag = false;
  bm->UserFlags.produce_models = true;

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "lazy_file_x", bv8);

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 42)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  TempFd output;
  ASSERT_NE(nullptr, output.file);
  ASSERT_GE(output.fd, 0);
  vc_printCounterExampleFile(vc, output.fd);

  const std::string printed = output.contents();
  EXPECT_NE(std::string::npos, printed.find("COUNTEREXAMPLE BEGIN")) << printed;
  EXPECT_NE(std::string::npos, printed.find("ASSERT( lazy_file_x = 0x2A );"))
      << printed;

  vc_Destroy(vc);
}

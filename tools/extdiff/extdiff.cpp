/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

/*
 * C API observation driver for the default-off baseline differential
 * (scripts/extdiff-baseline-differential.sh).
 *
 * The array-equality feature promises that STP with --array-equality
 * DISABLED behaves exactly like STP before the feature existed. This
 * program exercises vc_getCounterExampleArray and neighboring model
 * APIs with the feature disabled, and serializes every documented
 * observation to stdout: query status, entry counts, and each exact
 * (index, value) pair. It deliberately uses only the C API that exists at
 * the pre-feature baseline commit, so the identical source builds against
 * both the pinned baseline and the candidate tree.
 *
 * vc_getCounterExampleArray does not specify an entry order when array
 * equality is disabled. Its legacy implementation iterates an unordered_map
 * hashed by node_uid, so unrelated changes in AST-node creation can permute
 * an otherwise identical model. Canonicalize the returned pairs here before
 * comparing the two builds; entry count and contents remain exact.
 */

#include "stp/c_interface.h"
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <utility>
#include <vector>

// Cleanup sticks to the API that exists at the baseline commit:
// vc_DeleteExpr for the entry expressions, plain free for the strdup'd
// strings and the malloc'd entry buffers (the newer
// vc_deleteCounterExampleArray is not available in the baseline
// library this same source is compiled against).
static void dumpArray(VC vc, const char* label, Expr arr)
{
  Expr* indices = 0;
  Expr* values = 0;
  int size = 0;
  vc_getCounterExampleArray(vc, arr, &indices, &values, &size);
  printf("array %s entries %d\n", label, size);

  std::vector<std::pair<std::string, std::string>> entries;
  entries.reserve(size);
  for (int i = 0; i < size; i++)
  {
    char* is = exprString(indices[i]);
    char* vs = exprString(values[i]);
    entries.push_back(std::make_pair(std::string(is), std::string(vs)));
    free(is);
    free(vs);
    vc_DeleteExpr(indices[i]);
    vc_DeleteExpr(values[i]);
  }
  std::sort(entries.begin(), entries.end());
  for (int i = 0; i < size; i++)
    printf("  [%d] index %s value %s\n", i, entries[i].first.c_str(),
           entries[i].second.c_str());

  if (size != 0)
  {
    free(indices);
    free(values);
  }
}

static void dumpScalar(VC vc, const char* label, Expr e)
{
  Expr val = vc_getCounterExample(vc, e);
  char* s = exprString(val);
  printf("scalar %s = %s\n", label, s);
  free(s);
  vc_DeleteExpr(val);
}

// One observed index.
static void case_single(void)
{
  printf("== case single\n");
  VC vc = vc_createValidityChecker();
  Type arrT = vc_arrayType(vc, vc_bvType(vc, 8), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrT);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 5)),
                                 vc_bvConstExprFromInt(vc, 8, 77)));
  printf("query %d\n", vc_query(vc, vc_falseExpr(vc)));
  dumpArray(vc, "a", a);
  vc_Destroy(vc);
}

// Several indices in nonascending order; repeated calls interleaved
// with scalar model lookups; a second array; an unconstrained array;
// Boolean and bit-vector scalars alongside.
static void case_mixed(void)
{
  printf("== case mixed\n");
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  Type arrT = vc_arrayType(vc, vc_bvType(vc, 4), bv8);
  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);
  Expr unconstrained = vc_varExpr(vc, "u", arrT);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr p = vc_varExpr(vc, "p", vc_boolType(vc));

  const int idxs[4] = {11, 3, 0, 7};
  for (int i = 0; i < 4; i++)
    vc_assertFormula(
        vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 4, idxs[i])),
                      vc_bvConstExprFromInt(vc, 8, 100 + idxs[i])));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, b, vc_bvConstExprFromInt(vc, 4, 9)),
                                 x));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 42)));
  vc_assertFormula(vc, p);

  printf("query %d\n", vc_query(vc, vc_falseExpr(vc)));

  dumpArray(vc, "a(first)", a);
  dumpScalar(vc, "x", x);
  dumpArray(vc, "b", b);
  dumpScalar(vc, "p", p);
  dumpArray(vc, "a(second)", a);
  dumpArray(vc, "u", unconstrained);
  vc_Destroy(vc);
}

// Index width wider than a host integer.
static void case_wide(void)
{
  printf("== case wide\n");
  VC vc = vc_createValidityChecker();
  Type arrT = vc_arrayType(vc, vc_bvType(vc, 66), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrT);
  // 66-bit index with the top and bottom bits set
  Expr idx = vc_bvConstExprFromStr(
      vc, "100000000000000000000000000000000000000000000000000000000000000001");
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, idx),
                                 vc_bvConstExprFromInt(vc, 8, 3)));
  printf("query %d\n", vc_query(vc, vc_falseExpr(vc)));
  dumpArray(vc, "a", a);
  vc_Destroy(vc);
}

int main(void)
{
  case_single();
  case_mixed();
  case_wide();
  printf("== done\n");
  return 0;
}

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

// api2-golden.cpp -- the 2.x functions no other libstp2 suite calls, KLEE's
// core among them (extract, the extensions, the signed divisions, shifts by
// an expression, the comparisons, the overflow predicates, the buffer
// printers), against what the 2.x library itself returned for the same
// calls. Each expected text below was recorded from a build of 2.x.

#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace
{

unsigned long long rnd(unsigned long long* s)
{
  *s ^= *s << 13;
  *s ^= *s >> 7;
  *s ^= *s << 17;
  return *s;
}

void quiet(const char*) {}

// One round: symbols pinned to constants the seed chooses, every operation
// over them read back through the counterexample, as one line.
std::string round_line(unsigned long long& seed, int r)
{
  const int w = 1 + static_cast<int>(rnd(&seed) % 12);
  const unsigned long long mask = (1ull << w) - 1;
  const unsigned long long a = rnd(&seed) & mask, b = rnd(&seed) & mask;
  const int k = static_cast<int>(rnd(&seed) % (w + 2));
  VC vc = vc_createValidityChecker();
  Type t = vc_bvType(vc, w);
  Expr x = vc_varExpr(vc, "x", t), y = vc_varExpr(vc, "y", t);
  Expr ca = vc_bvConstExprFromLL(vc, w, a), cb = vc_bvConstExprFromLL(vc, w, b);
  vc_assertFormula(vc, vc_eqExpr(vc, x, ca));
  vc_assertFormula(vc, vc_eqExpr(vc, y, cb));
  std::vector<std::pair<const char*, Expr>> ops;
  const auto op = [&](const char* name, Expr e) { ops.emplace_back(name, e); };
  const auto bit = [&](Expr p) { return vc_boolToBVExpr(vc, p); };
  op("bvAnd", vc_bvAndExpr(vc, x, y));
  op("bvOr", vc_bvOrExpr(vc, x, y));
  op("bvXor", vc_bvXorExpr(vc, x, y));
  op("bvNot", vc_bvNotExpr(vc, x));
  op("bvNand", vc_bvNandExpr(vc, x, y));
  op("bvNor", vc_bvNorExpr(vc, x, y));
  op("bvXnor", vc_bvXnorExpr(vc, x, y));
  op("bvMinus", vc_bvMinusExpr(vc, w, x, y));
  op("bvUMinus", vc_bvUMinusExpr(vc, x));
  op("bvDiv", vc_bvDivExpr(vc, w, x, y));
  op("bvMod", vc_bvModExpr(vc, w, x, y));
  op("bvRem", vc_bvRemExpr(vc, w, x, y));
  op("sbvDiv", vc_sbvDivExpr(vc, w, x, y));
  op("sbvMod", vc_sbvModExpr(vc, w, x, y));
  op("sbvRem", vc_sbvRemExpr(vc, w, x, y));
  op("shlEE", vc_bvLeftShiftExprExpr(vc, w, x, y));
  op("lshrEE", vc_bvRightShiftExprExpr(vc, w, x, y));
  op("ashrEE", vc_bvSignedRightShiftExprExpr(vc, w, x, y));
  op("shlK", vc_bvLeftShiftExpr(vc, k, x));
  op("lshrK", vc_bvRightShiftExpr(vc, k, x));
  op("sext", vc_bvSignExtend(vc, x, w + k));
  op("zext", vc_bvZeroExtend(vc, x, w + k));
  op("extract", vc_bvExtract(vc, x, w - 1, (k < w) ? k : 0));
  op("boolToBV", bit(vc_bvLtExpr(vc, x, y)));
  op("bvLt", bit(vc_bvLtExpr(vc, x, y)));
  op("bvGe", bit(vc_bvGeExpr(vc, x, y)));
  op("sbvLt", bit(vc_sbvLtExpr(vc, x, y)));
  op("sbvLe", bit(vc_sbvLeExpr(vc, x, y)));
  op("sbvGt", bit(vc_sbvGtExpr(vc, x, y)));
  op("sbvGe", bit(vc_sbvGeExpr(vc, x, y)));
  op("implies", bit(vc_impliesExpr(vc, vc_bvLtExpr(vc, x, y), vc_sbvLtExpr(vc, x, y))));
  op("xorB", bit(vc_xorExpr(vc, vc_bvLtExpr(vc, x, y), vc_sbvLtExpr(vc, x, y))));
  op("boolExtract", bit(vc_bvBoolExtract(vc, x, w - 1)));
  op("boolExtract1", bit(vc_bvBoolExtract_One(vc, x, 0)));
  op("boolExtract0", bit(vc_bvBoolExtract_Zero(vc, x, 0)));
  op("uaddo", bit(vc_bvUnsignedAddOverflowExpr(vc, x, y)));
  op("smulo", bit(vc_bvSignedMulOverflowExpr(vc, x, y)));
  op("ssubo", bit(vc_bvSignedSubOverflowExpr(vc, x, y)));
  const int q = vc_query(vc, vc_falseExpr(vc));
  std::ostringstream line;
  line << "r" << r << " w=" << w << " a=" << a << " b=" << b << " k=" << k << " q=" << q << ":";
  for (const auto& [name, e] : ops)
  {
    Expr v = e != nullptr ? vc_getCounterExample(vc, e) : nullptr;
    line << " " << name << "=";
    if (e == nullptr)
      line << "NULLOP";
    else if (v == nullptr)
      line << "NULL";
    else
      line << getBVUnsignedLongLong(v) << "/" << getBVLength(v);
  }
  vc_Destroy(vc);
  return line.str();
}

// 2.x's lines for seed 7, rounds 0 to 23.
const char* const two_x_rounds[] = {
    "r0 w=4 a=4 b=15 k=1 q=0: bvAnd=4/4 bvOr=15/4 bvXor=11/4 bvNot=11/4 bvNand=11/4 bvNor=0/4 bvXnor=4/4 bvMinus=5/4 bvUMinus=12/4 bvDiv=0/4 bvMod=4/4 bvRem=4/4 sbvDiv=12/4 sbvMod=0/4 sbvRem=0/4 shlEE=0/4 lshrEE=0/4 ashrEE=0/4 shlK=8/5 lshrK=2/4 sext=4/5 zext=4/5 extract=2/3 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=0/1 xorB=1/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=1/1 smulo=0/1 ssubo=0/1",
    "r1 w=11 a=581 b=721 k=7 q=0: bvAnd=577/11 bvOr=725/11 bvXor=148/11 bvNot=1466/11 bvNand=1470/11 bvNor=1322/11 bvXnor=1899/11 bvMinus=1908/11 bvUMinus=1467/11 bvDiv=0/11 bvMod=581/11 bvRem=581/11 sbvDiv=0/11 sbvMod=581/11 sbvRem=581/11 shlEE=0/11 lshrEE=0/11 ashrEE=0/11 shlK=74368/18 lshrK=4/11 sext=581/18 zext=581/18 extract=4/4 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=1/1 ssubo=0/1",
    "r2 w=4 a=5 b=5 k=4 q=0: bvAnd=5/4 bvOr=5/4 bvXor=0/4 bvNot=10/4 bvNand=10/4 bvNor=10/4 bvXnor=15/4 bvMinus=0/4 bvUMinus=11/4 bvDiv=1/4 bvMod=0/4 bvRem=0/4 sbvDiv=1/4 sbvMod=0/4 sbvRem=0/4 shlEE=0/4 lshrEE=0/4 ashrEE=0/4 shlK=80/8 lshrK=0/4 sext=5/8 zext=5/8 extract=5/4 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=0/1 sbvLe=1/1 sbvGt=0/1 sbvGe=1/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=1/1 ssubo=0/1",
    "r3 w=1 a=1 b=0 k=1 q=0: bvAnd=0/1 bvOr=1/1 bvXor=1/1 bvNot=0/1 bvNand=1/1 bvNor=0/1 bvXnor=0/1 bvMinus=1/1 bvUMinus=1/1 bvDiv=1/1 bvMod=1/1 bvRem=1/1 sbvDiv=1/1 sbvMod=1/1 sbvRem=1/1 shlEE=1/1 lshrEE=1/1 ashrEE=1/1 shlK=2/2 lshrK=0/1 sext=3/2 zext=1/2 extract=1/1 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r4 w=2 a=0 b=1 k=3 q=0: bvAnd=0/2 bvOr=1/2 bvXor=1/2 bvNot=3/2 bvNand=3/2 bvNor=2/2 bvXnor=2/2 bvMinus=3/2 bvUMinus=0/2 bvDiv=0/2 bvMod=0/2 bvRem=0/2 sbvDiv=0/2 sbvMod=0/2 sbvRem=0/2 shlEE=0/2 lshrEE=0/2 ashrEE=0/2 shlK=0/5 lshrK=0/2 sext=0/5 zext=0/5 extract=0/2 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r5 w=4 a=10 b=2 k=0 q=0: bvAnd=2/4 bvOr=10/4 bvXor=8/4 bvNot=5/4 bvNand=13/4 bvNor=5/4 bvXnor=7/4 bvMinus=8/4 bvUMinus=6/4 bvDiv=5/4 bvMod=0/4 bvRem=0/4 sbvDiv=13/4 sbvMod=0/4 sbvRem=0/4 shlEE=8/4 lshrEE=2/4 ashrEE=14/4 shlK=10/4 lshrK=10/4 sext=10/4 zext=10/4 extract=10/4 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=1/1 ssubo=0/1",
    "r6 w=4 a=6 b=1 k=5 q=0: bvAnd=0/4 bvOr=7/4 bvXor=7/4 bvNot=9/4 bvNand=15/4 bvNor=8/4 bvXnor=8/4 bvMinus=5/4 bvUMinus=10/4 bvDiv=6/4 bvMod=0/4 bvRem=0/4 sbvDiv=6/4 sbvMod=0/4 sbvRem=0/4 shlEE=12/4 lshrEE=3/4 ashrEE=3/4 shlK=192/9 lshrK=0/4 sext=6/9 zext=6/9 extract=6/4 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r7 w=4 a=0 b=1 k=1 q=0: bvAnd=0/4 bvOr=1/4 bvXor=1/4 bvNot=15/4 bvNand=15/4 bvNor=14/4 bvXnor=14/4 bvMinus=15/4 bvUMinus=0/4 bvDiv=0/4 bvMod=0/4 bvRem=0/4 sbvDiv=0/4 sbvMod=0/4 sbvRem=0/4 shlEE=0/4 lshrEE=0/4 ashrEE=0/4 shlK=0/5 lshrK=0/4 sext=0/5 zext=0/5 extract=0/3 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r8 w=5 a=4 b=7 k=0 q=0: bvAnd=4/5 bvOr=7/5 bvXor=3/5 bvNot=27/5 bvNand=27/5 bvNor=24/5 bvXnor=28/5 bvMinus=29/5 bvUMinus=28/5 bvDiv=0/5 bvMod=4/5 bvRem=4/5 sbvDiv=0/5 sbvMod=4/5 sbvRem=4/5 shlEE=0/5 lshrEE=0/5 ashrEE=0/5 shlK=4/5 lshrK=4/5 sext=4/5 zext=4/5 extract=4/5 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=1/1 ssubo=0/1",
    "r9 w=11 a=1474 b=505 k=12 q=0: bvAnd=448/11 bvOr=1531/11 bvXor=1083/11 bvNot=573/11 bvNand=1599/11 bvNor=516/11 bvXnor=964/11 bvMinus=969/11 bvUMinus=574/11 bvDiv=2/11 bvMod=464/11 bvRem=464/11 sbvDiv=2047/11 sbvMod=436/11 sbvRem=1979/11 shlEE=0/11 lshrEE=0/11 ashrEE=2047/11 shlK=6037504/23 lshrK=0/11 sext=8388034/23 zext=1474/23 extract=1474/11 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=1/1 ssubo=1/1",
    "r10 w=7 a=19 b=1 k=5 q=0: bvAnd=1/7 bvOr=19/7 bvXor=18/7 bvNot=108/7 bvNand=126/7 bvNor=108/7 bvXnor=109/7 bvMinus=18/7 bvUMinus=109/7 bvDiv=19/7 bvMod=0/7 bvRem=0/7 sbvDiv=19/7 sbvMod=0/7 sbvRem=0/7 shlEE=38/7 lshrEE=9/7 ashrEE=9/7 shlK=608/12 lshrK=0/7 sext=19/12 zext=19/12 extract=0/2 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r11 w=6 a=61 b=30 k=2 q=0: bvAnd=28/6 bvOr=63/6 bvXor=35/6 bvNot=2/6 bvNand=35/6 bvNor=0/6 bvXnor=28/6 bvMinus=31/6 bvUMinus=3/6 bvDiv=2/6 bvMod=1/6 bvRem=1/6 sbvDiv=0/6 sbvMod=27/6 sbvRem=61/6 shlEE=0/6 lshrEE=0/6 ashrEE=63/6 shlK=244/8 lshrK=15/6 sext=253/8 zext=61/8 extract=15/4 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=1/1 smulo=1/1 ssubo=1/1",
    "r12 w=3 a=4 b=6 k=0 q=0: bvAnd=4/3 bvOr=6/3 bvXor=2/3 bvNot=3/3 bvNand=3/3 bvNor=1/3 bvXnor=5/3 bvMinus=6/3 bvUMinus=4/3 bvDiv=0/3 bvMod=4/3 bvRem=4/3 sbvDiv=2/3 sbvMod=0/3 sbvRem=0/3 shlEE=0/3 lshrEE=0/3 ashrEE=7/3 shlK=4/3 lshrK=4/3 sext=4/3 zext=4/3 extract=4/3 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=0/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=1/1 smulo=1/1 ssubo=0/1",
    "r13 w=12 a=3907 b=1981 k=2 q=0: bvAnd=1793/12 bvOr=4095/12 bvXor=2302/12 bvNot=188/12 bvNand=2302/12 bvNor=0/12 bvXnor=1793/12 bvMinus=1926/12 bvUMinus=189/12 bvDiv=1/12 bvMod=1926/12 bvRem=1926/12 sbvDiv=0/12 sbvMod=1792/12 sbvRem=3907/12 shlEE=0/12 lshrEE=0/12 ashrEE=4095/12 shlK=15628/14 lshrK=976/12 sext=16195/14 zext=3907/14 extract=976/10 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=1/1 smulo=1/1 ssubo=1/1",
    "r14 w=1 a=1 b=0 k=2 q=0: bvAnd=0/1 bvOr=1/1 bvXor=1/1 bvNot=0/1 bvNand=1/1 bvNor=0/1 bvXnor=0/1 bvMinus=1/1 bvUMinus=1/1 bvDiv=1/1 bvMod=1/1 bvRem=1/1 sbvDiv=1/1 sbvMod=1/1 sbvRem=1/1 shlEE=1/1 lshrEE=1/1 ashrEE=1/1 shlK=4/3 lshrK=0/1 sext=7/3 zext=1/3 extract=1/1 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r15 w=5 a=5 b=17 k=4 q=0: bvAnd=1/5 bvOr=21/5 bvXor=20/5 bvNot=26/5 bvNand=30/5 bvNor=10/5 bvXnor=11/5 bvMinus=20/5 bvUMinus=27/5 bvDiv=0/5 bvMod=5/5 bvRem=5/5 sbvDiv=0/5 sbvMod=22/5 sbvRem=5/5 shlEE=0/5 lshrEE=0/5 ashrEE=0/5 shlK=80/9 lshrK=0/5 sext=5/9 zext=5/9 extract=0/1 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=0/1 xorB=1/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=1/1 ssubo=1/1",
    "r16 w=2 a=3 b=0 k=3 q=0: bvAnd=0/2 bvOr=3/2 bvXor=3/2 bvNot=0/2 bvNand=3/2 bvNor=0/2 bvXnor=0/2 bvMinus=3/2 bvUMinus=1/2 bvDiv=3/2 bvMod=3/2 bvRem=3/2 sbvDiv=1/2 sbvMod=3/2 sbvRem=3/2 shlEE=3/2 lshrEE=3/2 ashrEE=3/2 shlK=24/5 lshrK=0/2 sext=31/5 zext=3/5 extract=3/2 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r17 w=5 a=7 b=27 k=5 q=0: bvAnd=3/5 bvOr=31/5 bvXor=28/5 bvNot=24/5 bvNand=28/5 bvNor=0/5 bvXnor=3/5 bvMinus=12/5 bvUMinus=25/5 bvDiv=0/5 bvMod=7/5 bvRem=7/5 sbvDiv=31/5 sbvMod=29/5 sbvRem=2/5 shlEE=0/5 lshrEE=0/5 ashrEE=0/5 shlK=224/10 lshrK=0/5 sext=7/10 zext=7/10 extract=7/5 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=0/1 xorB=1/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=1/1 smulo=1/1 ssubo=0/1",
    "r18 w=6 a=9 b=46 k=7 q=0: bvAnd=8/6 bvOr=47/6 bvXor=39/6 bvNot=54/6 bvNand=55/6 bvNor=16/6 bvXnor=24/6 bvMinus=27/6 bvUMinus=55/6 bvDiv=0/6 bvMod=9/6 bvRem=9/6 sbvDiv=0/6 sbvMod=55/6 sbvRem=9/6 shlEE=0/6 lshrEE=0/6 ashrEE=0/6 shlK=1152/13 lshrK=0/6 sext=9/13 zext=9/13 extract=9/6 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=0/1 xorB=1/1 boolExtract=1/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=1/1 ssubo=0/1",
    "r19 w=1 a=1 b=1 k=2 q=0: bvAnd=1/1 bvOr=1/1 bvXor=0/1 bvNot=0/1 bvNand=0/1 bvNor=0/1 bvXnor=1/1 bvMinus=0/1 bvUMinus=1/1 bvDiv=1/1 bvMod=0/1 bvRem=0/1 sbvDiv=1/1 sbvMod=0/1 sbvRem=0/1 shlEE=0/1 lshrEE=0/1 ashrEE=1/1 shlK=4/3 lshrK=0/1 sext=7/3 zext=1/3 extract=1/1 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=0/1 sbvLe=1/1 sbvGt=0/1 sbvGe=1/1 implies=1/1 xorB=0/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=1/1 smulo=1/1 ssubo=0/1",
    "r20 w=5 a=14 b=18 k=1 q=0: bvAnd=2/5 bvOr=30/5 bvXor=28/5 bvNot=17/5 bvNand=29/5 bvNor=1/5 bvXnor=3/5 bvMinus=28/5 bvUMinus=18/5 bvDiv=0/5 bvMod=14/5 bvRem=14/5 sbvDiv=31/5 sbvMod=0/5 sbvRem=0/5 shlEE=0/5 lshrEE=0/5 ashrEE=0/5 shlK=28/6 lshrK=7/5 sext=14/6 zext=14/6 extract=7/4 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=0/1 sbvLe=0/1 sbvGt=1/1 sbvGe=1/1 implies=0/1 xorB=1/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=1/1 smulo=1/1 ssubo=1/1",
    "r21 w=4 a=10 b=14 k=1 q=0: bvAnd=10/4 bvOr=14/4 bvXor=4/4 bvNot=5/4 bvNand=5/4 bvNor=1/4 bvXnor=11/4 bvMinus=12/4 bvUMinus=6/4 bvDiv=0/4 bvMod=10/4 bvRem=10/4 sbvDiv=3/4 sbvMod=0/4 sbvRem=0/4 shlEE=0/4 lshrEE=0/4 ashrEE=15/4 shlK=20/5 lshrK=5/4 sext=26/5 zext=10/5 extract=5/3 boolToBV=1/1 bvLt=1/1 bvGe=0/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=0/1 boolExtract=0/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=1/1 smulo=1/1 ssubo=0/1",
    "r22 w=1 a=1 b=0 k=0 q=0: bvAnd=0/1 bvOr=1/1 bvXor=1/1 bvNot=0/1 bvNand=1/1 bvNor=0/1 bvXnor=0/1 bvMinus=1/1 bvUMinus=1/1 bvDiv=1/1 bvMod=1/1 bvRem=1/1 sbvDiv=1/1 sbvMod=1/1 sbvRem=1/1 shlEE=1/1 lshrEE=1/1 ashrEE=1/1 shlK=1/1 lshrK=1/1 sext=1/1 zext=1/1 extract=1/1 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=1/1 sbvLe=1/1 sbvGt=0/1 sbvGe=0/1 implies=1/1 xorB=1/1 boolExtract=0/1 boolExtract1=1/1 boolExtract0=0/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
    "r23 w=1 a=0 b=0 k=0 q=0: bvAnd=0/1 bvOr=0/1 bvXor=0/1 bvNot=1/1 bvNand=1/1 bvNor=1/1 bvXnor=1/1 bvMinus=0/1 bvUMinus=0/1 bvDiv=1/1 bvMod=0/1 bvRem=0/1 sbvDiv=1/1 sbvMod=0/1 sbvRem=0/1 shlEE=0/1 lshrEE=0/1 ashrEE=0/1 shlK=0/1 lshrK=0/1 sext=0/1 zext=0/1 extract=0/1 boolToBV=0/1 bvLt=0/1 bvGe=1/1 sbvLt=0/1 sbvLe=1/1 sbvGt=0/1 sbvGe=1/1 implies=1/1 xorB=0/1 boolExtract=1/1 boolExtract1=0/1 boolExtract0=1/1 uaddo=0/1 smulo=0/1 ssubo=0/1",
};

std::string take(char* buf)
{
  std::string text = buf != nullptr ? buf : "(null)";
  std::free(buf);
  return text;
}

std::vector<std::string> lines_of(const std::string& text)
{
  std::vector<std::string> lines;
  std::istringstream in(text);
  for (std::string line; std::getline(in, line);)
    lines.push_back(line);
  return lines;
}

std::string replace_all(std::string text, const std::string& from, const std::string& to)
{
  for (std::size_t at = text.find(from); at != std::string::npos; at = text.find(from, at + to.size()))
    text.replace(at, from.size(), to);
  return text;
}

} // namespace

TEST(libstp2_golden, the_uncovered_constructors_give_2x_values)
{
  vc_registerErrorHandler(quiet);
  unsigned long long seed = 7;
  int r = 0;
  for (const char* expected : two_x_rounds)
  {
    EXPECT_EQ(expected, round_line(seed, r)) << "round " << r;
    ++r;
  }
  vc_registerErrorHandler(nullptr);
}

TEST(libstp2_golden, the_buffer_printers_give_2x_text)
{
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  Type arr = vc_arrayType(vc, vc_bvType(vc, 32), bv8);
  Expr x = vc_varExpr(vc, "x", bv8), y = vc_varExpr(vc, "y", bv8);
  Expr a = vc_varExpr(vc, "a", arr);
  Expr b = vc_varExpr(vc, "b", vc_boolType(vc));
  // An equality prints its operands in the order their nodes were made, and
  // C++ leaves the order of a call's arguments to the compiler: the constant
  // is made before the sum, as in the 2.x build this text comes from.
  Expr seven = vc_bvConstExprFromInt(vc, 8, 7);
  Expr sum = vc_bvPlusExpr(vc, 8, x, y);
  vc_assertFormula(vc, vc_eqExpr(vc, sum, seven));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 3)), x));
  vc_assertFormula(vc, vc_iffExpr(vc, b, vc_bvLtExpr(vc, x, y)));
  Expr q = vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 1));

  char* buf = nullptr;
  unsigned long len = 0;
  vc_printExprToBuffer(vc, q, &buf, &len);
  EXPECT_EQ(take(buf), "(x = 0x01\n) ");
  EXPECT_EQ(len, 13u); // the terminating NUL counted, as 2.x did

  const std::string two_x_state = "x  : BITVECTOR(8);\n"
                                  "y  : BITVECTOR(8);\n"
                                  "a  : ARRAY BITVECTOR(32) OF BITVECTOR(8);\n"
                                  "b  : BOOLEAN;\n"
                                  "%----------------------------------------------------\n"
                                  "ASSERT( (0x07 = BVPLUS(8, \nx, \ny)\n\n) );\n"
                                  "ASSERT( (x = a[0x00000003]\n) );\n"
                                  "ASSERT( ( NOT( (b XOR BVGT(y,x)\n\n))) );\n"
                                  "%----------------------------------------------------\n"
                                  "QUERY( (x = 0x01\n)  );\n";
  // 2.x's bytes but for the declarations' single space before the colon
  // (lib/Compat2/NOTES.md, decision 12)
  const std::string state = replace_all(two_x_state, "  : ", " : ");
  buf = nullptr;
  vc_printQueryStateToBuffer(vc, q, &buf, &len, 0);
  EXPECT_EQ(take(buf), state);
  EXPECT_EQ(len, state.size() + 1);

  // y pinned, so the counterexample is the one 2.x printed
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 5)));
  ASSERT_EQ(vc_query(vc, q), 0);
  buf = nullptr;
  vc_printCounterExampleToBuffer(vc, &buf, &len);
  const std::string ce = take(buf);
  EXPECT_EQ(len, 137u);
  std::vector<std::string> got = lines_of(ce);
  std::vector<std::string> expected = {"COUNTEREXAMPLE BEGIN: ",
                                       "ASSERT( a[0x00000003] = 0x02 );",
                                       "ASSERT( b<=>TRUE );",
                                       "ASSERT( x = 0x02 );",
                                       "ASSERT( y = 0x05 );",
                                       "COUNTEREXAMPLE END: "};
  ASSERT_EQ(got.size(), expected.size()) << ce;
  EXPECT_EQ(got.front(), expected.front());
  EXPECT_EQ(got.back(), expected.back());
  // the entries in whichever order the model keeps them
  std::sort(got.begin() + 1, got.end() - 1);
  EXPECT_EQ(got, expected);

  EXPECT_EQ(std::string(exprString(vc_bvPlusExpr(vc, 8, x, y))), "BVPLUS(8, \nx, \ny)\n ");
  EXPECT_EQ(vc_getIndexSize(vc, arr), 32);
  EXPECT_EQ(vc_getValueSize(vc, arr), 8);
  buf = nullptr;
  vc_printBVBitStringToBuffer(vc_bvConstExprFromInt(vc, 8, 5), &buf, &len);
  EXPECT_EQ(take(buf), "00000101");
  EXPECT_EQ(len, 9u);
  vc_Destroy(vc);
}

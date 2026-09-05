/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

// Is the difficulty score a good estimate of the bit-blasted AIG size?
// See README.md.

#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/DifficultyScore.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"

#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/FloatBlaster/rounding_modes.h"

#include <algorithm>
#include <cstdint>
#include <cmath>
#include <cinttypes>
#include <cstdio>
#include <cstring>
#include <string>
#include <sys/wait.h>
#include <unistd.h>
#include <vector>

using namespace stp;
using std::string;
using std::vector;

namespace
{

STPMgr* mgr = NULL;
Simplifier* simp = NULL;
unsigned counter = 0;
bool csv = false;

ASTNode fresh(unsigned width)
{
  char buf[32];
  snprintf(buf, sizeof(buf), "s%u", counter++);
  return mgr->CreateSymbol(buf, 0, width);
}

ASTNode freshBool()
{
  char buf[32];
  snprintf(buf, sizeof(buf), "b%u", counter++);
  return mgr->CreateSymbol(buf, 0, 0);
}

// The AIG AND-node count of bit-blasting `n` on its own. Children that are
// symbols cost nothing, so with fresh children this is the marginal cost of
// the top node.
int aigNodes(const ASTNode& n)
{
  BBNodeManagerAIG nm;
  BitBlasterAIG bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);
  if (n.GetType() == BOOLEAN_TYPE)
    bb.BBForm(n);
  else
  {
    BBNodeSetAIG support;
    bb.BBTerm(n, support);
  }
  return nm.totalNumberOfNodes();
}

int64_t scoreOf(const ASTNode& n)
{
  DifficultyScore d;
  return d.score(n, mgr);
}

struct Totals
{
  double logSum = 0;
  double logSqSum = 0;
  unsigned count = 0;
  unsigned within2x = 0;
} totals;

void report(const string& label, unsigned width, int aig, int64_t score)
{
  if (aig < 0)
  {
    if (csv)
      printf("%s,%u,,%" PRId64 "\n", label.c_str(), width, score);
    else
      printf("%-24s %6u %12s %12" PRId64 " %8s\n", label.c_str(), width,
             "n/a", score, "-");
    return;
  }

  const double ratio =
      static_cast<double>(std::max<int64_t>(1, score)) / std::max(1, aig);
  totals.logSum += std::log(ratio);
  totals.logSqSum += std::log(ratio) * std::log(ratio);
  totals.count++;
  if (ratio > 0.5 && ratio < 2.0)
    totals.within2x++;

  if (csv)
    printf("%s,%u,%d,%" PRId64 "\n", label.c_str(), width, aig, score);
  else
    printf("%-24s %6u %12d %12" PRId64 " %7.2fx\n", label.c_str(), width, aig,
           score, ratio);
}

// Bit-vector operations are measured in-process.
void measure(const string& label, unsigned width, const ASTNode& n)
{
  report(label, width, aigNodes(n), scoreOf(n));
}

// Floating point is lowered first, in a forked child: an operation that has no
// circuit at the format asked for (fp.rem at binary128, fp.roundToIntegral at
// the smallest formats) calls FatalError, which aborts the process.
void measureFp(const string& label, unsigned width, const ASTNode& measured,
               const ASTNode& scored)
{
  const int64_t score = scoreOf(scored);

  int fds[2];
  if (pipe(fds) != 0)
    return;
  const pid_t pid = fork();
  if (pid == 0)
  {
    close(fds[0]);
    int aig = -1;
    {
      FpTotalise totalise(mgr);
      FloatBlast blast(mgr);
      aig = aigNodes(blast.topLevel(totalise.topLevel(measured)));
    }
    const ssize_t ignored = write(fds[1], &aig, sizeof(aig));
    (void)ignored;
    close(fds[1]);
    _exit(0);
  }
  close(fds[1]);
  int aig = -1;
  if (read(fds[0], &aig, sizeof(aig)) != (ssize_t)sizeof(aig))
    aig = -1;
  close(fds[0]);
  int status = 0;
  waitpid(pid, &status, 0);
  report(label, width, aig, score);
}

void header()
{
  if (csv)
    printf("operation,width,aig,score\n");
  else
    printf("%-24s %6s %12s %12s %8s\n", "operation", "width", "aig", "score",
           "ratio");
}

ASTNode constantWithBits(unsigned w, unsigned stride)
{
  CBV cbv = CONSTANTBV::BitVector_Create(w, true);
  for (unsigned i = 0; i < w; i += stride)
    CONSTANTBV::BitVector_Bit_On(cbv, i);
  return mgr->CreateBVConst(cbv, w);
}

void bitvectorSweep(const vector<unsigned>& widths, unsigned arity)
{
  struct NAry { const char* name; Kind kind; };
  const vector<NAry> nary = {{"bvand", BVAND},   {"bvor", BVOR},
                             {"bvxor", BVXOR},   {"bvnand", BVNAND},
                             {"bvnor", BVNOR},   {"bvxnor", BVXNOR},
                             {"bvadd", BVPLUS},  {"bvmul", BVMULT}};
  const vector<NAry> binary = {
      {"bvsub", BVSUB},         {"bvudiv", BVDIV},
      {"bvurem", BVMOD},        {"bvsdiv", SBVDIV},
      {"bvsrem", SBVREM},       {"bvsmod", SBVMOD},
      {"bvshl", BVLEFTSHIFT},   {"bvlshr", BVRIGHTSHIFT},
      {"bvashr", BVSRSHIFT}};
  const vector<NAry> predicates = {
      {"=", EQ},                {"bvult", BVLT},
      {"bvule", BVLE},          {"bvugt", BVGT},
      {"bvuge", BVGE},          {"bvslt", BVSLT},
      {"bvsle", BVSLE},         {"bvsgt", BVSGT},
      {"bvsge", BVSGE},         {"bvuaddo", BVUADDO},
      {"bvsaddo", BVSADDO},     {"bvumulo", BVUMULO},
      {"bvsmulo", BVSMULO},     {"bvusubo", BVUSUBO},
      {"bvssubo", BVSSUBO}};

  for (unsigned w : widths)
  {
    for (const NAry& op : nary)
    {
      ASTVec kids;
      for (unsigned i = 0; i < arity; i++)
        kids.push_back(fresh(w));
      measure(op.name, w, mgr->CreateTerm(op.kind, w, kids));
    }
    for (const NAry& op : binary)
      measure(op.name, w, mgr->CreateTerm(op.kind, w, fresh(w), fresh(w)));
    for (const NAry& op : predicates)
      measure(op.name, w, mgr->CreateNode(op.kind, fresh(w), fresh(w)));

    measure("bvneg", w, mgr->CreateTerm(BVUMINUS, w, fresh(w)));
    measure("bvnot", w, mgr->CreateTerm(BVNOT, w, fresh(w)));
    measure("concat", 2 * w, mgr->CreateTerm(BVCONCAT, 2 * w, fresh(w),
                                             fresh(w)));
    measure("ite", w, mgr->CreateTerm(ITE, w, freshBool(), fresh(w),
                                      fresh(w)));

    // The same operations with one operand fixed. These are several times
    // cheaper, which is the whole reason the scorer looks at its children.
    const ASTNode c = constantWithBits(w, std::max(1u, w / 3));
    measure("bvand-const", w, mgr->CreateTerm(BVAND, w, c, fresh(w)));
    measure("bvadd-const", w, mgr->CreateTerm(BVPLUS, w, c, fresh(w)));
    measure("bvsub-const", w, mgr->CreateTerm(BVSUB, w, fresh(w), c));
    measure("bvmul-const", w, mgr->CreateTerm(BVMULT, w, c, fresh(w)));
    measure("bvudiv-const", w, mgr->CreateTerm(BVDIV, w, fresh(w), c));
    measure("const-bvudiv", w, mgr->CreateTerm(BVDIV, w, c, fresh(w)));
    measure("bvshl-const", w, mgr->CreateTerm(BVLEFTSHIFT, w, fresh(w), c));
    measure("=-const", w, mgr->CreateNode(EQ, fresh(w), c));
    measure("bvugt-const", w, mgr->CreateNode(BVGT, fresh(w), c));
    measure("ite-const", w, mgr->CreateTerm(ITE, w, freshBool(), c, fresh(w)));
  }
}

ASTNode freshFp(unsigned eb, unsigned sb)
{
  char buf[32];
  snprintf(buf, sizeof(buf), "f%u", counter++);
  return mgr->CreateSourceSymbol(buf, SourceSort::floatingPoint(eb, sb));
}

void floatingPointSweep(const vector<std::pair<unsigned, unsigned>>& formats)
{
  const ASTNode rne =
      mgr->CreateRMConst(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);

  for (const auto& format : formats)
  {
    const unsigned eb = format.first, sb = format.second, w = eb + sb;

    // The arithmetic is measured as the *marginal* cost of one more operation
    // in a chain, which is what a per-node estimate has to charge: a chain of
    // two, minus a chain of one. Both are consumed by a classification so that
    // the result is never packed.
    struct Arith { const char* name; Kind kind; };
    for (const Arith& op : vector<Arith>{{"fp.add", FP_ADD},
                                         {"fp.sub", FP_SUB},
                                         {"fp.mul", FP_MUL},
                                         {"fp.div", FP_DIV}})
    {
      const ASTNode one =
          mgr->CreateTerm(op.kind, w, rne, freshFp(eb, sb), freshFp(eb, sb));
      const ASTNode two = mgr->CreateTerm(op.kind, w, rne, one,
                                          freshFp(eb, sb));
      measureFp(op.name, w, mgr->CreateNode(FP_ISZERO, two),
                mgr->CreateNode(FP_ISZERO, two));
      measureFp(string("  (depth 1) ") + op.name, w,
                mgr->CreateNode(FP_ISZERO, one),
                mgr->CreateNode(FP_ISZERO, one));
    }

    // These are measured as one operation whose result is packed, so the
    // score has to include the pack -- score and measure the same node.
    const ASTNode fma =
        mgr->CreateTerm(FP_TO_IEEE_BV, w,
                        mgr->CreateTerm(FP_FMA, w,
                                        ASTVec{rne, freshFp(eb, sb),
                                               freshFp(eb, sb),
                                               freshFp(eb, sb)}));
    measureFp("fp.fma (+pack)", w, fma, fma);

    struct Un { const char* name; Kind kind; bool rounded; };
    for (const Un& op : vector<Un>{{"fp.sqrt", FP_SQRT, true},
                                   {"fp.roundToIntegral", FP_ROUNDTOINTEGRAL,
                                    true},
                                   {"fp.abs", FP_ABS, false},
                                   {"fp.neg", FP_NEG, false}})
    {
      const ASTNode t =
          op.rounded ? mgr->CreateTerm(op.kind, w, rne, freshFp(eb, sb))
                     : mgr->CreateTerm(op.kind, w, freshFp(eb, sb));
      const ASTNode packed = mgr->CreateTerm(FP_TO_IEEE_BV, w, t);
      measureFp(string(op.name) + " (+pack)", w, packed, packed);
    }

    for (const Un& op : vector<Un>{{"fp.rem", FP_REM, false},
                                   {"fp.min", FP_MIN, false},
                                   {"fp.max", FP_MAX, false}})
    {
      const ASTNode t =
          mgr->CreateTerm(op.kind, w, freshFp(eb, sb), freshFp(eb, sb));
      const ASTNode packed = mgr->CreateTerm(FP_TO_IEEE_BV, w, t);
      measureFp(string(op.name) + " (+pack)", w, packed, packed);
    }

    measureFp("fp.to_ieee_bv", w,
              mgr->CreateTerm(FP_TO_IEEE_BV, w, freshFp(eb, sb)),
              mgr->CreateTerm(FP_TO_IEEE_BV, w, freshFp(eb, sb)));

    for (const Un& op : vector<Un>{{"fp.leq", FP_LEQ, false},
                                   {"fp.lt", FP_LT, false},
                                   {"fp.geq", FP_GEQ, false},
                                   {"fp.gt", FP_GT, false},
                                   {"fp.eq", FP_EQ, false},
                                   {"= (float)", FP_SMT_EQ, false}})
    {
      const ASTNode p =
          mgr->CreateNode(op.kind, freshFp(eb, sb), freshFp(eb, sb));
      measureFp(op.name, w, p, p);
    }

    for (const Un& op : vector<Un>{{"fp.isNormal", FP_ISNORMAL, false},
                                   {"fp.isSubnormal", FP_ISSUBNORMAL, false},
                                   {"fp.isZero", FP_ISZERO, false},
                                   {"fp.isInfinite", FP_ISINFINITE, false},
                                   {"fp.isNaN", FP_ISNAN, false},
                                   {"fp.isNegative", FP_ISNEGATIVE, false},
                                   {"fp.isPositive", FP_ISPOSITIVE, false}})
    {
      const ASTNode p = mgr->CreateNode(op.kind, freshFp(eb, sb));
      measureFp(op.name, w, p, p);
    }

    // Conversions, from and to binary32 and a 32-bit integer.
    const ASTNode toFp = mgr->CreateTerm(
        FP_TOFP, w,
        ASTVec{mgr->CreateBVConst(32, eb), mgr->CreateBVConst(32, sb), rne,
               freshFp(8, 24)});
    measureFp("to_fp (float)", w, mgr->CreateNode(FP_ISZERO, toFp), toFp);

    const ASTNode fromSigned = mgr->CreateTerm(
        FP_TOFP_SIGNED, w,
        ASTVec{mgr->CreateBVConst(32, eb), mgr->CreateBVConst(32, sb), rne,
               fresh(32)});
    measureFp("to_fp (signed bv32)", w, mgr->CreateNode(FP_ISZERO, fromSigned),
              fromSigned);

    const ASTNode fromUnsigned = mgr->CreateTerm(
        FP_TOFP_UNSIGNED, w,
        ASTVec{mgr->CreateBVConst(32, eb), mgr->CreateBVConst(32, sb), rne,
               fresh(32)});
    measureFp("to_fp_unsigned (bv32)", w,
              mgr->CreateNode(FP_ISZERO, fromUnsigned), fromUnsigned);
  }
}

vector<unsigned> parseWidths(const char* s)
{
  vector<unsigned> out;
  const char* p = s;
  while (*p != '\0')
  {
    out.push_back((unsigned)strtoul(p, NULL, 10));
    while (*p != '\0' && *p != ',')
      p++;
    if (*p == ',')
      p++;
  }
  return out;
}

void usage()
{
  printf("usage: difficulty_bench [options]\n\n"
         "Compares DifficultyScore's estimate with the number of AIG AND\n"
         "nodes the bit-blaster really builds for one operation.\n\n"
         "  --widths LIST   bit-vector widths (default 8,16,32,64,128)\n"
         "  --arity N       operands for the n-ary operations (default 2)\n"
         "  --no-bv         skip the bit-vector operations\n"
         "  --no-fp         skip the floating-point operations\n"
         "  --csv           machine-readable output\n"
         "  --help\n");
}

} // namespace

int main(int argc, char** argv)
{
  vector<unsigned> widths = {8, 16, 32, 64, 128};
  unsigned arity = 2;
  bool doBv = true, doFp = true;

  for (int i = 1; i < argc; i++)
  {
    const string a = argv[i];
    if (a == "--help")
    {
      usage();
      return 0;
    }
    else if (a == "--csv")
      csv = true;
    else if (a == "--no-bv")
      doBv = false;
    else if (a == "--no-fp")
      doFp = false;
    else if (a == "--widths" && i + 1 < argc)
      widths = parseWidths(argv[++i]);
    else if (a == "--arity" && i + 1 < argc)
      arity = (unsigned)strtoul(argv[++i], NULL, 10);
    else
    {
      printf("unrecognised argument: %s\n", a.c_str());
      usage();
      return 1;
    }
  }

  STPMgr localMgr;
  mgr = &localMgr;
  SubstitutionMap substitutions(mgr);
  Simplifier localSimp(mgr, &substitutions);
  simp = &localSimp;

  header();

  if (doBv)
    bitvectorSweep(widths, arity);

  if (doFp)
    floatingPointSweep({{5, 11}, {8, 24}, {11, 53}, {15, 113}});

  if (!csv && totals.count > 0)
  {
    const double mean = totals.logSum / totals.count;
    const double variance =
        std::max(0.0, totals.logSqSum / totals.count - mean * mean);
    printf("\n%u measurements: geomean score/aig %.3f, typical error x%.2f, "
           "%.1f%% within 2x\n",
           totals.count, std::exp(mean), std::exp(std::sqrt(variance)),
           100.0 * totals.within2x / totals.count);
  }

  return 0;
}

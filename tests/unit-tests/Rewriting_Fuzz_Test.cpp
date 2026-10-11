/********************************************************************
 * AUTHORS: Trevor Hansen
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

// Randomised checking of the sharing-aware rewriting on the mutable graph.
//
// Random formulas from support/RandomFormula.h, rebuilt once through the
// simplifying factory so that the input is a fixpoint of its rules, as
// the pipeline's is. For each formula:
//
//   1. Soundness. Every rule is a pointwise identity: the result agrees
//      with the input on every assignment of the free variables.
//   2. Idempotence. A second run over the result returns it unchanged.
//   3. The graph. STP_REWRITING_CHECK_GRAPH is set for the run, so the
//      pass recounts the graph from scratch after every edit.
//
// MUTABLEGRAPH_FUZZ_SEEDS overrides the number of seeds (default 300);
// MUTABLEGRAPH_FUZZ_ONLY runs one seed; MUTABLEGRAPH_FUZZ_PROGRESS prints
// each seed as it starts.

#include "stp/Simplifier/Rewriting.h"
#include "support/RandomFormula.h"
#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <string>

using namespace stp;

namespace
{
int seedsFromEnv(int dflt)
{
  const char* e = std::getenv("MUTABLEGRAPH_FUZZ_SEEDS");
  return e == NULL ? dflt : std::atoi(e);
}

TEST(RewritingFuzz, PointwiseIdentityAndIdempotence)
{
  setenv("STP_REWRITING_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0, changed = 0;
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    fuzz::RandomFormula fz(s);
    fz.rewritingShapes = true;
    ASTNodeMap canonMemo;
    ASTNode f;
    for (int attempt = 0; attempt < 8; attempt++)
    {
      f = fz.canonical(fz.randomFormula(false), canonMemo);
      if (!f.isConstant())
        break;
    }
    if (f.isConstant())
    {
      trivial++;
      continue;
    }
    if (std::getenv("MUTABLEGRAPH_FUZZ_PROGRESS") != NULL)
      std::cerr << "seed " << s << "\n";

    Rewriting r1(&fz.mgr, &fz.snf);
    ASTNode input = f;
    const ASTNode result = r1.topLevel(input);
    if (result != f)
      changed++;

    std::string why;
    const bool ok = fz.checkEquivalent(f, result, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << why << ", seed " << s << "\nformula " << f
                    << "\nresult " << result;

    Rewriting r2(&fz.mgr, &fz.snf);
    ASTNode second = result;
    const ASTNode again = r2.topLevel(second);
    ASSERT_EQ(again, result) << "second pass changed the result, seed " << s
                             << "\nformula " << f << "\nresult " << result
                             << "\nagain " << again;
  }
  std::cerr << "seeds " << seeds << ", skipped (too many assignments) " << skipped
            << ", trivial " << trivial << ", rewritten " << changed << "\n";
}
} // namespace

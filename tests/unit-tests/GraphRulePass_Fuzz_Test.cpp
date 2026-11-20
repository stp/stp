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

// Randomised checking of the GraphRulePass passes: the sharing-aware
// rewriting, flattening and common-factor extraction on the mutable graph.
//
// Random formulas from support/RandomFormula.h, rebuilt once through the
// simplifying factory so that the input is a fixpoint of its rules, as
// the pipeline's is, with the shapes the rules match mixed in. For each
// formula and each pass:
//
//   1. Soundness. Every rule is a pointwise identity: the result agrees
//      with the input on every assignment of the free variables.
//   2. Idempotence. A second run over the result returns it unchanged.
//   3. The graph. STP_CHECK_GRAPH is set for the run, so the pass recounts
//      the graph from scratch after every edit.
//   4. The original pass (the rebuild over a share count of the input) is
//      run on the same formula and checked for equivalence too; how often
//      the two results differ is reported, not asserted, since the live
//      counts fire where the stale ones did not.
//
// PureLiterals and SplitExtracts record definitions, so they are checked
// as the unconstrained fuzzer checks its pass: the original with the
// definitions substituted back against the result, pointwise for the
// split (an identity over the fresh pieces), equisatisfiable with model
// mapping for the literals (setting a pure literal is not an identity).
// Each is also run through its original pass and the results compared.
//
// The Chained case runs the three on one graph with the strength-reducing
// layer installed, as sizeReducingOnGraph does, and checks the result
// equivalent to the input. It also runs them
// one after another with an export and import between each; the two
// usually agree, and where they differ it is two normal forms of one
// rewrite (the hashing order of commutative children follows node numbers,
// and the graph numbers its edited nodes differently from a re-import),
// so the count is reported and both results are checked, not compared.
//
// MUTABLEGRAPH_FUZZ_SEEDS overrides the number of seeds (default 300);
// MUTABLEGRAPH_FUZZ_ONLY runs one seed; MUTABLEGRAPH_FUZZ_PROGRESS prints
// each seed as it starts.

#include "stp/Simplifier/CommonFactor.h"
#include "stp/Simplifier/FindPureLiterals.h"
#include "stp/Simplifier/GraphConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/MergeSame.h"
#include "stp/Simplifier/Flatten.h"
#include "stp/Simplifier/GraphRulePasses.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/StrengthReducingNodeFactory.h"
#include "stp/Simplifier/StrengthReduction.h"
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

template <class Pass, class Original>
void runSeeds(const char* name)
{
  setenv("STP_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0, changed = 0, differs = 0;
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

    Pass p1(&fz.mgr);
    ASTNode input = f;
    const ASTNode result = p1.topLevel(input);
    if (result != f)
      changed++;

    std::string why;
    const bool ok = fz.checkEquivalent(f, result, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << name << ": " << why << ", seed " << s << "\nformula " << f
                    << "\nresult " << result;

    Pass p2(&fz.mgr);
    ASTNode second = result;
    const ASTNode again = p2.topLevel(second);
    ASSERT_EQ(again, result) << name << ": second pass changed the result, seed "
                             << s << "\nformula " << f << "\nresult " << result
                             << "\nagain " << again;

    Original o(&fz.mgr, &fz.snf);
    ASTNode input2 = f;
    const ASTNode viaRebuild = o.topLevel(input2);
    if (viaRebuild != result)
      differs++;
    const bool okOriginal = fz.checkEquivalent(f, viaRebuild, why);
    ASSERT_TRUE(okOriginal || why == "skip")
        << name << " (original): " << why << ", seed " << s << "\nformula " << f
        << "\nresult " << viaRebuild;
  }
  std::cerr << name << ": seeds " << seeds << ", skipped (too many assignments) "
            << skipped << ", trivial " << trivial << ", changed " << changed
            << ", differs from the original pass " << differs << "\n";
}

TEST(GraphRulePassFuzz, Rewriting)
{
  runSeeds<GraphRewriting, Rewriting>("Rewriting");
}

TEST(GraphRulePassFuzz, Flatten)
{
  runSeeds<GraphFlatten, Flatten>("Flatten");
}

TEST(GraphRulePassFuzz, CommonFactor)
{
  runSeeds<GraphCommonFactor, CommonFactor>("CommonFactor");
}

TEST(GraphRulePassFuzz, MergeSame)
{
  runSeeds<GraphMergeSame, MergeSame>("MergeSame");
}

// One formula per seed through a definition-recording pass on the graph
// and through its original; `graphPass` and `originalPass` run them.
template <class GraphPass, class OriginalPass>
void runDefinitionSeeds(const char* name, bool pointwise, GraphPass graphPass,
                        OriginalPass originalPass)
{
  setenv("STP_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0, changed = 0, differs = 0;
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    fuzz::DefinitionFuzz fz(s);
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

    const ASTNode result = graphPass(fz, fz.simp, f);
    if (result != f)
      changed++;
    ASTNode back;
    std::string why;
    ASSERT_TRUE(fz.backSubstitute(f, back, why)) << name << ": " << why << ", seed " << s;
    bool ok = pointwise ? fz.checkEquivalent(back, result, why)
                        : fz.checkEquisat(f, back, result, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << name << ": " << why << ", seed " << s << "\nformula " << f
                    << "\nresult " << result << "\nback " << back;

    // The original pass on the same formula, with a map of its own.
    SubstitutionMap sm2(&fz.mgr);
    Simplifier simp2(&fz.mgr, &sm2);
    const ASTNode viaOriginal = originalPass(fz, simp2, f);
    if (viaOriginal != result)
      differs++;
    ASTNode back2;
    ASSERT_TRUE(fz.backSubstitute(f, back2, why, simp2)) << name << " (original): " << why << ", seed " << s;
    ok = pointwise ? fz.checkEquivalent(back2, viaOriginal, why)
                   : fz.checkEquisat(f, back2, viaOriginal, why);
    ASSERT_TRUE(ok || why == "skip") << name << " (original): " << why << ", seed " << s
                                     << "\nformula " << f << "\nresult " << viaOriginal;
  }
  std::cerr << name << ": seeds " << seeds << ", skipped (too many assignments) "
            << skipped << ", trivial " << trivial << ", changed " << changed
            << ", differs from the original pass " << differs << "\n";
}

TEST(GraphRulePassFuzz, PureLiterals)
{
  runDefinitionSeeds(
      "PureLiterals", false,
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        GraphFindPureLiterals pure(&fz.mgr);
        return pure.topLevel(f, &simp);
      },
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        FindPureLiterals find;
        ASTNode n = f;
        if (find.topLevel(n, &simp, &fz.mgr))
        {
          n = simp.applySubstitutionMap(n);
          simp.haveAppliedSubstitutionMap();
        }
        return n;
      });
}

// Each run mints its own fresh pieces, so every formula the pass changes
// differs from the original's result by those symbols; the count says how
// often it fired.
TEST(GraphRulePassFuzz, SplitExtracts)
{
  runDefinitionSeeds(
      "SplitExtracts", true,
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        fz.mgr.UserFlags.enable_split_extracts = true;
        GraphSplitExtracts split(fz.mgr);
        return split.topLevel(f, &simp);
      },
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        fz.mgr.UserFlags.enable_split_extracts = true;
        SplitExtracts split(fz.mgr);
        return split.topLevel(f, &simp);
      });
}

// Fixing bits under the assertion is an equivalence modulo the formula and
// records definitions for the symbols it fixes: the equisatisfiability
// oracle, as for the pure literals.
TEST(GraphRulePassFuzz, ConstantBitPropagation)
{
  runDefinitionSeeds(
      "ConstantBitPropagation", false,
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        GraphConstantBitPropagation cb(&fz.mgr);
        return cb.topLevel(f, &simp);
      },
      [](fuzz::DefinitionFuzz& fz, Simplifier& simp, const ASTNode& f) {
        simplifier::constantBitP::ConstantBitPropagation cb(
            &fz.mgr, &simp, fz.mgr.defaultNodeFactory, f);
        if (cb.isUnsatisfiable())
          return fz.mgr.ASTFalse;
        return cb.topLevelBothWays(f);
      });
}

TEST(GraphRulePassFuzz, Chained)
{
  setenv("STP_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0, changed = 0, differs = 0;
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

    ASTNode chained;
    {
      MutableGraph graph(fz.mgr);
      graph.import(f);
      // With the strength reductions installed as sizeReducingOnGraph
      // installs them.
      NodeDomainAnalysis nda(&fz.mgr);
      StrengthReduction sr(&graph.simplifyingFactory(), &fz.mgr.UserFlags);
      StrengthReducingNodeFactory layer(fz.mgr, graph.simplifyingFactory(), sr, nda);
      graph.installReducer(layer, nda);
      GraphFlatten flatten(&fz.mgr);
      flatten.topLevel(graph);
      GraphCommonFactor factor(&fz.mgr);
      factor.topLevel(graph);
      GraphRewriting rewrite(&fz.mgr);
      rewrite.topLevel(graph);
      chained = graph.exportRoot();
      nda.forgetMutable();
    }
    ASTNode separate = f;
    {
      GraphFlatten flatten(&fz.mgr);
      separate = flatten.topLevel(separate);
      GraphCommonFactor factor(&fz.mgr);
      separate = factor.topLevel(separate);
      GraphRewriting rewrite(&fz.mgr);
      separate = rewrite.topLevel(separate);
    }
    if (chained != f)
      changed++;
    if (chained != separate)
      differs++;
    std::string why;
    const bool ok = fz.checkEquivalent(f, chained, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << "chained: " << why << ", seed " << s << "\nformula " << f
                    << "\nresult " << chained;
    const bool okSeparate = fz.checkEquivalent(f, separate, why);
    ASSERT_TRUE(okSeparate || why == "skip")
        << "separately: " << why << ", seed " << s << "\nformula " << f
        << "\nresult " << separate;
  }
  std::cerr << "Chained: seeds " << seeds << ", skipped (too many assignments) "
            << skipped << ", trivial " << trivial << ", changed " << changed
            << ", differs from the three run separately " << differs << "\n";
}
} // namespace

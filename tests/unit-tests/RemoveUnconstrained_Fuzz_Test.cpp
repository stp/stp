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

// Randomised checking of RemoveUnconstrained on the mutable graph.
//
// Random formulas at width 2 over a handful of symbols, built through the
// hashing factory so nothing is pre-simplified, then rebuilt once through
// the simplifying factory (see canonical), over every kind the pass
// has a rule for: the per-kind arms, n-ary operators, chains of constant
// operations under a predicate (the ground-path collapse), comparisons
// against constants and against terms, term and Boolean if-then-else,
// extracts, concatenations and extensions. For each formula:
//
//   1. Soundness. With the image-variable rewrite off every rule is a
//      pointwise identity: the original with the recorded definitions
//      substituted back agrees with the result on every assignment. With
//      it on, equisatisfiability with model mapping: every model of the
//      result maps back to a model of the original, and both are
//      satisfiable or neither is.
//   2. Idempotence. A second run over the result returns it unchanged.
//   3. The graph. STP_CHECK_GRAPH is set for the run, so the pass
//      recounts the graph from scratch after every edit.
//
// The checks and their evaluation are those of the exhaustive suite.
// MUTABLEGRAPH_FUZZ_SEEDS overrides the number of seeds (default 300).

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/StrengthReducingNodeFactory.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include "support/RandomFormula.h"
#include <functional>
#include <cstdlib>
#include <gtest/gtest.h>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <random>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Fuzz : fuzz::DefinitionFuzz
{
  explicit Fuzz(uint64_t seed) : DefinitionFuzz(seed) {}

  // Top-level definitions for the equality propagation to find.
  ASTNode randomFormula()
  {
    return RandomFormula::randomFormula(std::getenv("MUTABLEGRAPH_FUZZ_PE") != NULL);
  }
};

int seedsFromEnv(int dflt)
{
  const char* e = std::getenv("MUTABLEGRAPH_FUZZ_SEEDS");
  return e == NULL ? dflt : std::atoi(e);
}

void runSeeds(bool imageVars)
{
  setenv("STP_CHECK_GRAPH", "1", 1);
  const int seeds = seedsFromEnv(300);
  const char* only = std::getenv("MUTABLEGRAPH_FUZZ_ONLY");
  size_t skipped = 0, trivial = 0;
  size_t imageConstrained = 0; // category A, see the idempotence check
  size_t reduced = 0;          // results the strength reductions changed
  for (int s = 1; s <= seeds; s++)
  {
    if (only != NULL && s != std::atoi(only))
      continue;
    Fuzz fz(imageVars ? 7919ULL * s : s);
    fz.mgr.UserFlags.unconstrained_image_vars = imageVars;
    ASTNodeMap canonMemo;
    // Random width-2 formulas fold to a constant six times in ten once the
    // rules have seen them; draw again (same seed, next draw) a few times.
    ASTNode f;
    for (int attempt = 0; attempt < 8; attempt++)
    {
      f = fz.canonical(fz.randomFormula(), canonMemo);
      if (!f.isConstant())
        break;
    }
    if (std::getenv("MUTABLEGRAPH_FUZZ_PROGRESS") != NULL)
      std::cerr << "seed " << s << "\n";
    const char* traceSeed = std::getenv("MUTABLEGRAPH_FUZZ_TRACE_SEED");
    const bool tracing = std::getenv("MUTABLEGRAPH_FUZZ_TRACE") != NULL &&
                         (traceSeed == NULL || std::atoi(traceSeed) == s);
    if (tracing)
      std::cerr << "seed " << s << " image vars " << imageVars << " formula " << f << "\n";
    if (f.isConstant())
    {
      trivial++;
      continue;
    }

    // MUTABLEGRAPH_FUZZ_SR: the strength reductions ride on the graph as
    // well, so every reduction of a graph node is checked by the same
    // oracle (pointwise identity or equisatisfiability).
    const bool withSR = std::getenv("MUTABLEGRAPH_FUZZ_SR") != NULL;
    NodeDomainAnalysis nda1(&fz.mgr);
    StrengthReduction sr1(fz.mgr.defaultNodeFactory, &fz.mgr.UserFlags);
    // MUTABLEGRAPH_FUZZ_PE: the top-level equalities are propagated on
    // the graph first; the oracle back-substitutes their definitions
    // like the pass's own.
    const bool withPE = std::getenv("MUTABLEGRAPH_FUZZ_PE") != NULL;
    // MUTABLEGRAPH_FUZZ_SHARED: the pass runs over a graph the harness owns,
    // as sizeReducingOnGraph runs it, with the reducing layer installed
    // there when MUTABLEGRAPH_FUZZ_SR is set; the refused definitions and
    // image constraints then join the formula at the graph's root.
    const bool shared = std::getenv("MUTABLEGRAPH_FUZZ_SHARED") != NULL;
    auto runShared = [&](RemoveUnconstrained& r, StrengthReduction& sr,
                         NodeDomainAnalysis& nda, const ASTNode& in,
                         Simplifier* sp) {
      MutableGraph graph(fz.mgr);
      graph.import(in);
      std::unique_ptr<StrengthReducingNodeFactory> layer;
      if (withSR)
      {
        sr.setFactory(&graph.simplifyingFactory());
        layer.reset(new StrengthReducingNodeFactory(fz.mgr, graph.simplifyingFactory(), sr, nda));
        graph.installReducer(*layer, nda);
      }
      r.topLevel(graph, sp);
      ASTNode out = graph.exportRoot();
      if (out.GetKind() == AND)
        out = fz.mgr.defaultNodeFactory->CreateNode(AND, out.GetChildren());
      if (withSR)
      {
        nda.forgetMutable();
        out = sr.finish(out, nda);
      }
      std::string why;
      if (!graph.checkInvariant(&why))
        throw std::runtime_error("graph invariant broken after the pass: " + why);
      return out;
    };
    fz.mgr.UserFlags.propagate_equalities = true;
    PropagateEqualities pe1(&fz.simp, fz.mgr.defaultNodeFactory, &fz.mgr);
    RemoveUnconstrained r1(fz.mgr);
    if (withSR && !shared)
      r1.withStrengthReduction(&sr1, &nda1);
    if (withPE)
      r1.withEqualities(&pe1);
    const ASTNode result = shared ? runShared(r1, sr1, nda1, f, &fz.simp)
                                  : r1.topLevel(f, &fz.simp);
    if (withSR)
    {
      // How often the reductions change what the pass alone would give:
      // the measure that the mode exercises them at all.
      SubstitutionMap smPlain(&fz.mgr);
      Simplifier simpPlain(&fz.mgr, &smPlain);
      RemoveUnconstrained plain(fz.mgr);
      if (plain.topLevel(f, &simpPlain) != result)
        reduced++;
    }

    // Idempotence. A run that made an image constraint is the known
    // exception: the constraint joins the formula after the graph is
    // exported, so the next run sees the fresh variable as free and
    // finishes the job (category A of the idempotence report). Counted,
    // not asserted, until the constraint is spliced into the graph.
    // The pipeline rebuilds the pass's output through the simplifier's
    // substitution before the next pass sees it; with the rules run where
    // the pass edited, that rebuild changes nothing. The second run gets
    // its own simplifier, so the definitions it records do not pollute
    // the first run's map, which the soundness check below reads.
    const ASTNode rebuilt = fz.simp.applySubstitutionMap(result);
    ASSERT_EQ(rebuilt, result) << "the simplifier's rebuild changed the result, seed "
                               << s << " image vars " << imageVars << "\nformula " << f
                               << "\nresult " << result << "\nrebuilt " << rebuilt;
    SubstitutionMap sm2(&fz.mgr);
    Simplifier simp2(&fz.mgr, &sm2);
    NodeDomainAnalysis nda2(&fz.mgr);
    StrengthReduction sr2(fz.mgr.defaultNodeFactory, &fz.mgr.UserFlags);
    PropagateEqualities pe2(&simp2, fz.mgr.defaultNodeFactory, &fz.mgr);
    RemoveUnconstrained r2(fz.mgr);
    if (withSR && !shared)
      r2.withStrengthReduction(&sr2, &nda2);
    if (withPE)
      r2.withEqualities(&pe2);
    const ASTNode again = shared ? runShared(r2, sr2, nda2, result, &simp2)
                                 : r2.topLevel(result, &simp2);
    if (r1.imageConstraintCount() > 0 && again != result)
      imageConstrained++;
    else
      ASSERT_EQ(again, result) << "second pass changed the result, seed " << s
                               << " image vars " << imageVars << "\nformula " << f
                               << "\nresult " << result << "\nagain " << again;

    // Soundness.
    ASTNode back;
    std::string why;
    ASSERT_TRUE(fz.backSubstitute(f, back, why)) << why << ", seed " << s;
    const bool ok = imageVars ? fz.checkEquisat(f, back, result, why)
                              : fz.checkEquivalent(back, result, why);
    if (!ok && why == "skip")
    {
      skipped++;
      continue;
    }
    ASSERT_TRUE(ok) << why << ", seed " << s << " image vars " << imageVars
                    << "\nformula " << f << "\nresult " << result;
  }
  std::cerr << "seeds " << seeds << ", skipped (too many assignments) " << skipped
            << ", trivial " << trivial
            << ", not idempotent after an image constraint " << imageConstrained
            << ", changed by strength reduction " << reduced << "\n";
}

TEST(RemoveUnconstrainedFuzz, PointwiseIdentityAndIdempotence)
{
  runSeeds(false);
}

TEST(RemoveUnconstrainedFuzz, EquisatWithImageVariables)
{
  runSeeds(true);
}
} // namespace

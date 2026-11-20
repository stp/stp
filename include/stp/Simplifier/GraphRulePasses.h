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

/*
 * The sharing-aware rewriting, flattening and common-factor extraction as
 * GraphRulePass rule sets, selected by --passes-on-graph. Each has the
 * topLevel of the rebuilding pass it stands in for (Rewriting, Flatten,
 * CommonFactor), takes only the manager since it builds through its
 * graph's factory, and carries its own copy of that pass's rules, reading the
 * graph's live parent counts where the original reads a share count of
 * its input. Each also runs over a graph handed to it, so the three run on
 * one graph with one import and one export (STP::sizeReducingOnGraph). The duplication is for measuring the two against each other;
 * the one that loses goes.
 */

#ifndef GRAPHRULEPASSES_H_
#define GRAPHRULEPASSES_H_

#include "stp/Simplifier/GraphRulePass.h"
#include <unordered_map>

namespace stp
{
class Simplifier;

class GraphRewriting : public GraphRulePass
{
  unsigned narrowedBitwise = 0;
  void stats();
  // Every rule of Rewriting.cpp, in order, over one node. Each rule sees
  // what the rules before it produced.
  virtual ASTNode applyRules(const ASTNode& c) override;

public:
  GraphRewriting(const GraphRewriting&) = delete;
  GraphRewriting& operator=(const GraphRewriting&) = delete;
  explicit GraphRewriting(STPMgr* stp_) : GraphRulePass(stp_)
  {
  }
  ASTNode topLevel(ASTNode& n);
  void topLevel(MutableGraph& graph);
};

// A node of an associative, commutative kind absorbs a child of the same
// kind when that child has no other parent, so the child dies with the
// merge and nothing is duplicated; conjuncts of the root AND are absorbed
// whatever their sharing. The sweep runs parents before children, so the
// top of a same-kind chain absorbs the whole chain in one application and
// the absorbed nodes are out of the formula by the time it reaches them.
class GraphFlatten : public GraphRulePass
{
  unsigned removed = 0;
  unsigned topRemoved = 0;
  void stats();

  static bool flattenable(Kind k);
  virtual ASTNode applyRules(const ASTNode& c) override;
  virtual bool caresAbout(Kind k) override { return flattenable(k); }
  virtual bool topDown() override { return true; }

public:
  GraphFlatten(const GraphFlatten&) = delete;
  GraphFlatten& operator=(const GraphFlatten&) = delete;
  explicit GraphFlatten(STPMgr* stp_) : GraphRulePass(stp_)
  {
  }
  ASTNode topLevel(ASTNode& n);
  void topLevel(MutableGraph& graph);
};

// CommonFactor.h says what the extraction is and why it is sharing-aware.
class GraphCommonFactor : public GraphRulePass
{
  // Multiplications removed, counting the one spent on each extracted
  // factor.
  long saved = 0;
  void stats();

  struct Addend
  {
    ASTNode product;
    bool negated = false;
  };
  bool productOf(const ASTNode& addend, Addend& out) const;
  ASTNode without(const Addend& a, const ASTNode& factor, unsigned width);
  ASTNode sumOf(const ASTVec& addends, unsigned width);
  bool extractOne(ASTVec& addends, unsigned width);
  bool extract(ASTVec& addends, unsigned width);

  // A sum with a factor to take out becomes the factored sum.
  virtual ASTNode applyRules(const ASTNode& c) override;
  // The guards are on the products and their negations.
  virtual bool caresAbout(Kind k) override
  {
    return k == BVMULT || k == BVUMINUS;
  }

public:
  GraphCommonFactor(const GraphCommonFactor&) = delete;
  GraphCommonFactor& operator=(const GraphCommonFactor&) = delete;
  explicit GraphCommonFactor(STPMgr* stp_) : GraphRulePass(stp_)
  {
  }
  ASTNode topLevel(const ASTNode& n);
  long multipliesSaved() const { return saved; }
  void topLevel(MutableGraph& graph);
};

// MergeSame's rules over the root conjunction: a shared disjunct factored
// out of two two-way ORs, a negated AND turned into an OR so it can take
// part, the XOR pair recognised.
class GraphMergeSame : public GraphRulePass
{
  unsigned replaced = 0;
  void merge(ASTVec& conjuncts, unsigned firstIndex, unsigned secondIndex);
  virtual ASTNode applyRules(const ASTNode& c) override;
  virtual bool caresAbout(Kind k) override
  {
    (void)k;
    return false;
  }

public:
  GraphMergeSame(const GraphMergeSame&) = delete;
  GraphMergeSame& operator=(const GraphMergeSame&) = delete;
  explicit GraphMergeSame(STPMgr* stp_) : GraphRulePass(stp_) {}
  ASTNode topLevel(ASTNode& n);
  void topLevel(MutableGraph& graph);
};

// FindPureLiterals on the graph: polarities over the current formula, and
// a Boolean symbol of one polarity is substituted by the constant that
// satisfies it and defined so in the substitution map, for the model.
class GraphFindPureLiterals
{
  STPMgr* bm;
  typedef char polarity_type;
  static constexpr polarity_type truePolarity = 1;
  static constexpr polarity_type falsePolarity = 2;
  static constexpr polarity_type bothPolarity = 3;
  typedef std::unordered_map<ASTNode, polarity_type, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      Polarities;
  void build(const ASTNode& root, Polarities& out);

public:
  GraphFindPureLiterals(const GraphFindPureLiterals&) = delete;
  GraphFindPureLiterals& operator=(const GraphFindPureLiterals&) = delete;
  explicit GraphFindPureLiterals(STPMgr* bm_) : bm(bm_) {}
  // How many symbols were set.
  unsigned topLevel(MutableGraph& graph, Simplifier* simp);
  // Standalone: import, run, export.
  ASTNode topLevel(const ASTNode& n, Simplifier* simp);
};

// SplitExtracts on the graph. The question is which symbols are read only
// through extracts and over what ranges, which is the symbol's parents;
// the rewrite substitutes the symbol by a concatenation of fresh pieces
// and records that as its definition, as the original does.
class GraphSplitExtracts
{
  STPMgr& bm;
  unsigned extractsFound = 0;
  unsigned introduced = 0;

public:
  GraphSplitExtracts(const GraphSplitExtracts&) = delete;
  GraphSplitExtracts& operator=(const GraphSplitExtracts&) = delete;
  explicit GraphSplitExtracts(STPMgr& bm_) : bm(bm_) {}
  void topLevel(MutableGraph& graph, Simplifier* simp);
  // Standalone: pending definitions applied, import, run, export.
  ASTNode topLevel(const ASTNode& n, Simplifier* simp);
  unsigned getIntroduced() const { return introduced; }
};
}
#endif

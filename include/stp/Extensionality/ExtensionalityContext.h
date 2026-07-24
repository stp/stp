/********************************************************************
 * AUTHORS: Andrew V. Jones
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
 * The registry of abstracted array equalities for the lemmas-on-demand
 * decision procedure for the extensional theory of arrays
 * (Brummayer & Biere, JSAT 6 (2010)).
 *
 * Whenever the feature is enabled, every equality between array terms
 * is replaced at node-creation time by a fresh Boolean abstraction
 * variable (the paper's formula abstraction, section 5), together with
 * the witness constraints of preprocessing step 1 (section 4). The
 * solving side of the procedure builds on this registry in later
 * commits.
 *
 * Lifetime: one context per STPMgr, created lazily the first time an
 * array equality is built with --array-equality enabled. The registry
 * lives as long as the query AST: its abstraction variables are
 * embedded in the user's formula.
 */

#ifndef EXTENSIONALITYCONTEXT_H
#define EXTENSIONALITYCONTEXT_H

#include "stp/AST/AST.h"
#include <map>
#include <set>
#include <vector>

namespace stp
{

class STPMgr;

class ExtensionalityContext
{
public:
  // One abstracted array equality. The construction operands are the
  // array terms as they were when the equality was built; because STP
  // simplifies and substitutes before solving, the current (canonical)
  // form of each operand is recovered at solve time from the record's
  // anchor equations, which travel through the same rewriting as the
  // rest of the formula.
  struct Record
  {
    size_t id;
    ASTNode proxy;             // ordinary Boolean SYMBOL
    ASTNode constructionLeft;
    ASTNode constructionRight;
    ASTNode canonicalLeft;     // per-solve, set at preparation time
    ASTNode canonicalRight;    // per-solve, set at preparation time
    ASTNode lambda;            // fresh witness index symbol
    ASTNode nameL, nameR;      // scalar names of the witness reads
    // Constraint bundle conjoined at the start of every solve. The
    // last conjunct is preprocessing step 1 of the paper -- the witness
    // for array inequality, a != b -> read(a,l) != read(b,l) -- and the
    // two defining equations name the virtual reads so they stay in
    // the formula (and therefore in the bit-blast) in every case:
    //   nameL = read(constructionLeft, lambda)
    //   nameR = read(constructionRight, lambda)
    //   proxy OR nameL != nameR
    ASTNode anchorL, anchorR, witnessClause;
  };

  explicit ExtensionalityContext(STPMgr* bm);

  //--------------------------------------------------------------------
  // Registry (persistent for the query AST lifetime)
  //--------------------------------------------------------------------

  // The formula abstraction of an array equality (paper section 5):
  // called from the shared node-creation funnel for every well-typed
  // equality between array terms while the feature is enabled, instead
  // of building an EQ node. Returns the fresh (or, for a repeated
  // operand pair, reused) Boolean abstraction variable; reflexive
  // requests fold to true. Mixed index/element widths are an error.
  ASTNode makeEquality(const ASTNode& a, const ASTNode& b);

  bool enabled() const;
  // The decision procedure participates in a solve exactly when the
  // feature is on and at least one array equality was abstracted.
  bool active() const { return enabled() && !records.empty(); }

  const std::vector<Record>& getRecords() const { return records; }

  // Symbols the decision procedure depends on: abstraction variables,
  // witness indices and witness-read names, and the scalar names given
  // to lemma leaves. STP's substitution passes must not eliminate them
  // -- each must still be present when the formula is bit-blasted so
  // that refinement lemmas can be encoded over its SAT variables.
  bool isProtected(const ASTNode& s) const
  {
    return protectedSymbols.find(s) != protectedSymbols.end();
  }

  // Conservative over-approximation of the arrays the checker may
  // reason about (every array symbol reachable from any registry
  // operand), used to stop the substitution pass from deleting
  // read-equals-constant equations whose reads the checker needs to
  // observe.
  bool mayBeConeArray(const ASTNode& arraySymbol) const
  {
    return possibleConeSymbols.find(arraySymbol) != possibleConeSymbols.end();
  }

private:
  STPMgr* bm;

  std::vector<Record> records;
  std::map<std::pair<ASTNode, ASTNode>, size_t> keyToRecord;
  std::map<ASTNode, size_t> proxyToRecord;
  std::set<ASTNode> protectedSymbols;
  std::set<ASTNode> possibleConeSymbols;

  void collectPossibleConeSymbols(const ASTNode& n);
};

} // namespace stp

#endif // EXTENSIONALITYCONTEXT_H

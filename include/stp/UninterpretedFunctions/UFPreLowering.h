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

/********************************************************************
 * Top-level equalities, propagated through uninterpreted applications
 * before lowering replaces them by scalars.
 ********************************************************************/
#ifndef STP_UFPRELOWERING_H
#define STP_UFPRELOWERING_H

#include "stp/AST/AST.h"
#include <cstddef>

namespace stp
{

class STPMgr;

struct DLL_PUBLIC UFPreLoweringStats
{
  // Facts the Boolean skeleton forced and the pass conjoined to the root
  // before reading its equalities; see SkeletonPreproc.
  size_t skeletonFacts = 0;
  // The skeleton alone refuted the query, in which case the pass returns
  // false and nothing below ran.
  bool skeletonUnsat = false;
  // Symbols the pass replaced by what a top-level equality says they equal.
  size_t symbolSubstitutions = 0;
  // Applications replaced by the constant a top-level equality pins them to.
  size_t applicationSubstitutions = 0;
  // Rewrite rounds until the root stopped changing.
  size_t rounds = 0;
  // Distinct applications left in the root once the pass is done.
  size_t applicationsRemaining = 0;
};

// Lowering turns every application into a fresh symbol and then has to keep
// that symbol -- and every symbol the application takes as an argument --
// out of the simplifier's hands, because a congruence lemma is later encoded
// over exactly those symbols' SAT bits. The price is that a fact the query
// states at the top level, `x = 5` or `a = (f y)` or `(f 3) = 0`, cannot be
// pushed through an application: `(f x)` and `(f 5)` stay two applications
// that only a lemma can relate, and a term built on `a` never learns it is
// `(f y)`.
//
// This pass runs on the completed root before lowering, while an application
// is still an ordinary term, and does what that ordinary term allows: it
// reads the conjuncts of the root and rewrites every other conjunct under
// them. A symbol equated with a term becomes that term; an application
// equated with a constant becomes that constant; a Boolean symbol or
// application asserted outright becomes true or false. Hash-consing then
// makes `(f x)` and `(f y)` one application when `x = y` was asserted, which
// is exactly the structural merge an e-graph solver gets at internalisation.
//
// The defining conjunct is kept, so the pass changes no model: every fact it
// used still constrains the symbol it was used on, and the ordinary
// preprocessing that follows lowering eliminates that symbol through the
// substitution map as it always did -- it is simply no longer an argument of
// any application, so nothing protects it any more.
class DLL_PUBLIC UFPreLowering final
{
public:
  explicit UFPreLowering(STPMgr* manager);

  UFPreLowering(const UFPreLowering&) = delete;
  UFPreLowering& operator=(const UFPreLowering&) = delete;

  // `root` is a completed root: DISTINCT already lowered, no ARRAY_EQ yet
  // lowered, applications still in place. Returns a root equivalent to it.
  //
  // With `skeleton` set, the Boolean skeleton is asked first what it forces
  // and those facts are conjoined to the root, where the rewrite can read
  // them: a query that states `x = 5` only inside an implication the
  // structure resolves still gets `(f x)` sent to `(f 5)`. This is the one
  // point at which a skeleton fact can reach an application, since lowering
  // hides the arguments from everything that runs later.
  //
  // `handleAliases`, when given, receives one entry for every application of
  // the original root that the rewrite turned into a different application:
  // (f x) under x = 7 becomes (f 7), and it is (f 7) that lowering sees and
  // the solve certifies. A caller holding the original handle -- get-value,
  // the C API's value accessor -- reads it through this map.
  ASTNode propagate(const ASTNode& root, UFPreLoweringStats* stats = NULL,
                    bool skeleton = false, ASTNodeMap* handleAliases = NULL);

  // Prints the stats under -s, in the same shape as the rest of the UF
  // reporting.
  void report(const UFPreLoweringStats& stats) const;

private:
  STPMgr* const manager_;
};

} // namespace stp

#endif

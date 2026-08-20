/********************************************************************
 * AUTHORS: Andrew Teylu
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

// Replace a fully symmetric distinct with a strict chain.

#ifndef STP_DISTINCTORDERING_H
#define STP_DISTINCTORDERING_H

#include "stp/AST/AST.h"
#include <vector>

namespace stp
{

class STPMgr;
struct DistinctGroup;

// If the operands of a recorded distinct (see STPMgr::distinctGroups) are
// variables that occur nowhere else, every permutation of them maps the
// formula to itself, so requiring them to be strictly increasing loses no
// models up to that symmetry -- and n-1 comparisons replace n(n-1)/2
// disequalities.
//
// The gain is not marginal. Three hundred unconstrained 32-bit variables
// under one distinct take 172s pairwise and 0.2s chained (RelWithDebInfo,
// CaDiCaL), because the pairwise form asks a bit-blaster to discover an
// ordering that the chain simply states.
//
// Returns `root` unchanged unless it rewrote something, and reports through
// `ordered` how many groups it took. Sound in the direction that matters
// unconditionally: the chain implies the distinct, so every model of the
// result is a model of `root` and published models never need qualifying --
// which is also why only positive occurrences are taken. The converse -- that
// rewriting cannot turn satisfiable into unsatisfiable -- is what the
// occurrence guard buys, and it is checked against `root` itself rather than
// assumed from the parse.
ASTNode applyDistinctOrdering(STPMgr* manager, const ASTNode& root,
                              const std::vector<DistinctGroup>& groups,
                              size_t* ordered = NULL);

} // namespace stp

#endif

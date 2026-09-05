// -*- c++ -*-
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

#ifndef ARRAYREADREFINEMENTPROGRESS_H_
#define ARRAYREADREFINEMENTPROGRESS_H_

#include "stp/AST/AST.h"
#include "stp/ToSat/ToSATBase.h"

#include <array>
#include <map>
#include <set>
#include <vector>

namespace stp
{

// Logical progress for one array-read refinement transaction.
//
// getEquals() creates a fresh comparison circuit every time it is called, so
// SAT variable or clause growth cannot distinguish a new congruence axiom from
// re-encoding one the solver already has. This object instead remembers the
// logical (index0,index1,value0,value1) axioms emitted during ONE check-sat.
// Its check-local lifetime is deliberate: the incremental backend and its
// node-to-variable binding are stable throughout a check, while a backend
// rebuild starts a new check with an empty transaction. Batch solving passes
// no transaction and retains its existing zero-memo path.
//
// Leaf bindings are interned once per symbol rather than copied into every
// pair. A changed or missing binding within a transaction is an integration
// error: suppressing the old axiom would lose a constraint, while continually
// re-emitting against changing variables would merely disguise the livelock.
class ArrayReadRefinementProgress
{
  typedef std::array<ASTNode, 4> AxiomKey;

  struct AxiomKeyLess
  {
    bool operator()(const AxiomKey& a, const AxiomKey& b) const
    {
      for (size_t i = 0; i < a.size(); ++i)
      {
        if (a[i].GetNodeNum() != b[i].GetNodeNum())
          return a[i].GetNodeNum() < b[i].GetNodeNum();
      }
      return false;
    }
  };

  std::set<AxiomKey, AxiomKeyLess> emitted;
  std::map<ASTNode, std::vector<unsigned>, ExprLess> stableBindings;

  void verifyStableBinding(
      const ASTNode& leaf,
      const ToSATBase::ASTNodeToSATVar& currentBindings);

public:
  // Returns true exactly once for an axiom under this check's stable SAT
  // binding. A true result authorizes the caller to emit its CNF.
  bool claim(const ASTNode& index0, const ASTNode& index1,
             const ASTNode& value0, const ASTNode& value1,
             const ToSATBase::ASTNodeToSATVar& currentBindings);

  size_t emittedAxiomCount() const { return emitted.size(); }
};

} // namespace stp

#endif

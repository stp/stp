/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: December, 2011
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

#ifndef PROPAGATEEQUALITIES_H_
#define PROPAGATEEQUALITIES_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/NodeSimplifier.h"

/* 
  Finds formulae asserted at the top level, and removes the variables, e.g:
  (= SYMBOL BVCONST), 
  (IFF SYMBOL TRUE), 
  (IFF SYMBOL FALSE), 
  (IFF SYMBOL SYMBOL), 
  (=SYMBOL SYMBOL)
or (=SYMBOL BVCONST).  
 */

namespace stp
{

class PropagateEqualities : public NodeSimplifier
{
  Simplifier* simp;
  NodeFactory* nf;
  STPMgr* bm;
  const ASTNode ASTTrue, ASTFalse;
  const bool always_true;

  std::unordered_set<uint64_t> alreadyVisited;

  typedef std::unordered_set<uint64_t> IdSet;
  typedef std::unordered_map<uint64_t, std::tuple <ASTNode, ASTNode, IdSet > > MapToNodeSet;


  void buildCandidateList(const ASTNode& a);
  void replaceIfPossible(int line, ASTNode& output, const ASTNode& lhs, const ASTNode& rhs);
  void buildXORCandidates(const ASTNode a, bool negated);
  
  //ASTNode AndPropagate(const ASTNode& a, ArrayTransformer* at);

  void addCandidate(const ASTNode a, const ASTNode b);
  bool isSymbol(ASTNode c);

  std::vector < std::pair<ASTNode, ASTNode> > candidates;

  void processCandidates();

  MapToNodeSet buildMapOfLHStoVariablesInRHS(const IdSet&);

  uint64_t todo=0;

  void countToDo(ASTNode n);

public:
  PropagateEqualities(Simplifier* simp_, NodeFactory* nf_, STPMgr* bm_)
 : ASTTrue(bm_->ASTTrue), ASTFalse(bm_->ASTFalse),
   always_true(bm_->UserFlags.enable_always_true)
  {
    simp = simp_;
    nf = nf_;
    bm = bm_;
  }


  virtual ~PropagateEqualities() override 
  {}
  
  virtual ASTNode topLevel(const ASTNode& a) override;

};
}

#endif

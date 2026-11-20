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
#include "stp/Simplifier/NodeSimplifier.h"
#include <set>
#include <ankerl/unordered_dense.h>

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
class MutableGraph;

class PropagateEqualities : public NodeSimplifier
{
  Simplifier* simp;
  NodeFactory* nf;
  STPMgr* bm;
  const ASTNode ASTTrue, ASTFalse;

public:
  // The same substitutions applied on a MutableGraph instead of through
  // the substitution map's rebuild: candidates are read off the graph's
  // root conjunction and decided exactly as processCandidates decides
  // them (its merged variable sets are what make the loop check cheap
  // over tens of thousands of candidates); each chosen symbol is then
  // forwarded to its term as the graph has it. The definitions still go
  // into the substitution map, for the model. Returns how many were
  // applied. `untouchable`: symbols that must keep their defining
  // constraint (an image-constrained fresh symbol's lives outside the
  // graph).
  size_t applyOnGraph(MutableGraph& g, const std::set<ASTNode>* untouchable);

  // Flat open-addressing set: the sets are hot (closure folds, membership
  // probes), and only their *contents* matter to the algorithm, never their
  // iteration order.
  using IdSet = ankerl::unordered_dense::set<uint64_t>;

  struct CandidateInfo
  {
    ASTNode lhs;
    ASTNode rhs;
    IdSet vars;  // candidate-LHS variables in rhs, with replacements folded in
    int id;      // insertion order; priority-queue tie-break for determinism
    size_t upTo; // how many replacements have been folded into vars
  };
  using MapToNodeSet = std::unordered_map<uint64_t, CandidateInfo>;

private:
  IdSet alreadyVisited;

  void buildCandidateList(const ASTNode& a);
  bool buildCandidateListNode(const ASTNode& a);
  void buildXORCandidates(const ASTNode a, bool negated);
  

  void addCandidate(const ASTNode a, const ASTNode b);
  ASTNode resolveFpLiteral(const ASTNode& n);
  bool isSymbol(ASTNode c);

  std::vector < std::pair<ASTNode, ASTNode> > candidates;

  // Decides and records the substitutions. With a graph, each is also
  // applied to it (the symbol forwarded to its term as the graph has it)
  // and symbols in `untouchable` are skipped. Returns how many.
  size_t processCandidates(bool preserveDefaultGrammar, MutableGraph* g = NULL,
                           const std::set<ASTNode>* untouchable = NULL);

  MapToNodeSet buildMapOfLHStoVariablesInRHS(const IdSet&);

  uint64_t todo=0;

  void countToDo(ASTNode n);


  bool speculative=false;

public:
  PropagateEqualities(Simplifier* simp_, NodeFactory* nf_, STPMgr* bm_)
 : ASTTrue(bm_->ASTTrue), ASTFalse(bm_->ASTFalse)
  {
    simp = simp_;
    nf = nf_;
    bm = bm_;
  }


  // Speculative rules might increase the number of nodes, because
  // they add uminus nodes. Perhaps should be moved into the speculative part.
  void setSpeculativeOn()
  {
    speculative = true;
  }


  virtual ~PropagateEqualities() override 
  {}
  
  virtual ASTNode topLevel(const ASTNode& a) override;

};
}

#endif

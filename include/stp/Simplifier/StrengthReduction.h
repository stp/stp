/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2011
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
 *  Takes the result of an analysis and uses it to simplify, for example,
 *  if both operands of a signed division have the same MSB, it can be converted
 *  to an unsigned division, instead. This does the replacements both for fixed bits 
 *  and the unsigned intervals.
 */

#ifndef STRENGTHREDUCTION_H_
#define STRENGTHREDUCTION_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"

#include <unordered_map>
#include <string>

namespace stp
{
using std::string;
using simplifier::constantBitP::FixedBits;

class StrengthReduction
{
  unsigned replaceWithConstant =0;
  unsigned replaceWithSimpler =0;
  unsigned writesSkipped =0;
  unsigned writesDropped =0;

  // Set by the chase when it meets a read over a write. The chain pass
  // below has nothing to do otherwise, and skipping it keeps its walk and
  // rebuild off every array-free query.
  bool sawReadOverWrite = false;

  CBV littleOne;
  NodeFactory* nf;
  UserDefinedFlags* uf;

  // How many places refer to a node, by node number. Only built for the
  // write-chain pass, which needs to know whether rebuilding a chain
  // shortens it or merely copies it.
  std::unordered_map<uint64_t, uint32_t> shareCount;
  void buildShareCount(const ASTNode& n);

  // A special version that handles the lhs appearing in the rhs of the fromTo
  // map.

  ASTNode visit(const ASTNode& n, stp::NodeDomainAnalysis& nda, ASTNodeMap& fromTo);

  ASTNode strengthReduction(const ASTNode& n, const NodeToFixedBitsMap& visited);
  ASTNode strengthReduction(const ASTNode& n, const NodeToUnsignedIntervalMap& visited);
  ASTNode strengthReduction(const ASTNode& n, const NodeToValueSetMap& visited);

  // Moves a READ down the WRITE chain below it, past every write whose
  // index provably differs from the read's. Unlike the node factory's own
  // chase, which has only the syntactic tests, this one asks the domains.
  ASTNode chaseReadPastWrites(const ASTNode& n, NodeDomainAnalysis& nda);

  // The same disequality, applied to writes the chase cannot reach because
  // a write that might alias sits above them. Deletes them from the chain
  // rather than moving the read, so it needs the share count.
  ASTNode dropShadowedWrites(const ASTNode& top, NodeDomainAnalysis& nda);
  ASTNode filterWriteChain(const ASTNode& n, NodeDomainAnalysis& nda);

public:

  // The domain-map types come from NodeDomainAnalysis.h (the owner of the
  // data); duplicating them here previously shadowed those definitions.

  StrengthReduction(NodeFactory *nf, UserDefinedFlags *uf);
  
  StrengthReduction(const StrengthReduction&) = delete;
  StrengthReduction& operator=(const StrengthReduction&) = delete;
  
  ~StrengthReduction();

  //TODO merge these toplevel funtions, they do the same thing..
  //Replace nodes with simpler nodes.
  ASTNode topLevel(const ASTNode& top, const NodeToFixedBitsMap& visited);
  ASTNode topLevel(const ASTNode& top, const NodeToUnsignedIntervalMap& visited);
  ASTNode topLevel(const ASTNode& top, const NodeToValueSetMap& visited);

  // New style invocation.
  ASTNode topLevel(const ASTNode& top, NodeDomainAnalysis& nda);

 
    
  void stats(string name = "StrengthReduction");
};
}

#endif

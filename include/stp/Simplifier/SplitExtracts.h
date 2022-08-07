/********************************************************************
 *
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

#ifndef SPLITEXTRACTS_H
#define SPLITEXTRACTS_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include <map>

namespace stp
{


class SplitExtracts 
{
  STPMgr& bm;
  ASTNode ASTUndefined;

  unsigned extractsFound =0;
  unsigned introduced =0;

  using Ranges = std::vector < std::tuple<ASTNode, uint64_t, uint64_t> >;
  // Node is the extract, then high of the extract, then low of the extract.
  using NodeToExtractsMap = std::unordered_map<ASTNode, Ranges, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;
  
  void buildMap(const ASTNode & n, std::unordered_set<uint64_t> &visited, NodeToExtractsMap& nodeToExtracts);

public:

  virtual ~SplitExtracts()
  {}

	SplitExtracts(STPMgr& _bm ) : bm(_bm)
	{
	  ASTUndefined = bm.CreateNode(stp::UNDEFINED);
	}

	virtual ASTNode topLevel(const ASTNode& n);

	auto getIntroduced()
	{
		return introduced;
	}
};
}


#endif


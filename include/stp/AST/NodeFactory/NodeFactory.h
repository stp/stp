/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb, 2010
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

// Abstract base class for all the node factories.
#ifndef NODEFACTORY_H
#define NODEFACTORY_H

#include <vector>
#include "stp/AST/ASTKind.h"

namespace BEEV
{
class ASTNode;
typedef std::vector<ASTNode> ASTVec;
extern ASTVec _empty_ASTVec;
class STPMgr;
typedef unsigned int * CBV;
}

using BEEV::ASTNode;
using BEEV::Kind;
using BEEV::ASTVec;
using BEEV::_empty_ASTVec;

class NodeFactory //not copyable
{
protected:
        BEEV::STPMgr& bm;

public:
        NodeFactory(BEEV::STPMgr& bm_) : bm(bm_){}

	virtual ~NodeFactory();

	virtual BEEV::ASTNode CreateTerm(Kind kind, unsigned int width,
				const BEEV::ASTVec &children) =0;

	virtual BEEV::ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width,
				const BEEV::ASTVec &children);

	virtual BEEV::ASTNode CreateNode(Kind kind,
			const BEEV::ASTVec& children) =0;

	ASTNode CreateSymbol(const char * const name, unsigned indexWidth, unsigned valueWidth);

	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTVec &children = _empty_ASTVec);
	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTVec &children = _empty_ASTVec);
	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTNode& child2,
			const ASTVec &children = _empty_ASTVec);

	ASTNode CreateNode(Kind kind, const ASTNode& child0,
			const ASTVec & back_children = _empty_ASTVec);
	ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
			const ASTVec & back_children = _empty_ASTVec);
	ASTNode	CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
			const ASTNode& child2, const ASTVec & back_children =
			_empty_ASTVec);


	ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTNode& child2,
			const ASTVec &children = _empty_ASTVec);

	ASTNode getTrue();
	ASTNode getFalse();

	ASTNode CreateConstant(BEEV::CBV cbv, unsigned width);

	virtual std::string getName()=0;
};

#endif

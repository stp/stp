/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
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

#include "stp/AST/NodeFactory/TypeChecker.h"
#include "stp/AST/AST.h"

BEEV::ASTNode TypeChecker::CreateTerm(BEEV::Kind kind, unsigned int width, const BEEV::ASTVec &children)
{
	BEEV::ASTNode r = f.CreateTerm(kind,width,children);
	BVTypeCheck(r);
	return r;
}

//virtual BEEV::ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children);
BEEV::ASTNode TypeChecker::CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children)
{
	BEEV::ASTNode r = f.CreateNode(kind,children);
	BVTypeCheck(r);
	return r;
}

BEEV::ASTNode TypeChecker::CreateArrayTerm(Kind kind, unsigned int index,
		unsigned int width, const BEEV::ASTVec &children)
{
	ASTNode r = f.CreateTerm(kind, width, children);
	r.SetIndexWidth(index);
	BVTypeCheck(r);
	return r;
}


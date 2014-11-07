/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: May, 2010
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

#ifndef SMTLIBPRINTERS_H_
#define SMTLIBPRINTERS_H_

#include "stp/Printer/printers.h"

namespace printer
{

	//Map from ASTNodes to LetVars
	extern BEEV::ASTNodeMap NodeLetVarMap;

	//This is a vector which stores the Node to LetVars pairs. It
	//allows for sorted printing, as opposed to NodeLetVarMap
	extern std::vector<std::pair<ASTNode, ASTNode> > NodeLetVarVec;

	//a partial Map from ASTNodes to LetVars. Needed in order to
	//correctly print shared subterms inside the LET itself
	extern BEEV::ASTNodeMap NodeLetVarMap1;

	std::string functionToSMTLIBName(const Kind k, bool smtlib1);

	void LetizeNode(const ASTNode& n, BEEV::ASTNodeSet& PLPrintNodeSet, bool smtlib1);

	ostream& SMTLIB_Print(ostream &os, const ASTNode n, const int indentation, void (*SMTLIB_Print1)(ostream&, const ASTNode , int , bool ), bool smtlib1);

	bool containsAnyArrayOps(const ASTNode& n);
}

#endif

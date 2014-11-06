// -*- c++ -*-
/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#include "stp/ToSat/ASTNode/ClauseList.h"
#include "stp/AST/AST.h"

namespace BEEV
{

// inplace PRODUCT of "this".
void ClauseList::appendToAllClauses(const ASTNode* n) {
	ClauseContainer::iterator it1 = cont.begin();
	for (; it1 != cont.end(); it1++)
		(*it1)->push_back(n);
}

// expects varphi2 to be just a single clause.
void ClauseList::INPLACE_PRODUCT(const ClauseList& varphi2) {
	assert(1 == varphi2.size());
	ClauseList& varphi1 = *this;

	ClauseContainer::iterator it1 = varphi1.cont.begin();
	ClauseContainer::iterator this_end = varphi1.cont.end();
	const ClauseNoPtr::const_iterator& insert_end =
			varphi2.cont.front()->end();
	const ClauseNoPtr::const_iterator& insert_begin =
			varphi2.cont.front()->begin();

	for (; it1 != this_end; it1++) {
		ClausePtr p = *it1;
		p->insert(p->end(), insert_begin, insert_end);
	}
}


}

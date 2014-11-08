// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jan, 2012
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


#ifndef NODEITERATOR_H_
#define NODEITERATOR_H_

#include "stp/AST/ASTNode.h"
#include "stp/STPManager/STPManager.h"
#include <stack>

namespace BEEV
{
    // Returns each node once, then returns the sentinel.
    // NB if the sentinel is contained in the node that's passed, then it'll be wrong.
    class NodeIterator //not copyable
    {
        std::stack<ASTNode> toVisit;

        const ASTNode& sentinel;
        uint8_t iteration;


    public:
        NodeIterator(const ASTNode &n, const ASTNode &_sentinel, STPMgr& stp) :
                sentinel(_sentinel), iteration(stp.getNextIteration())
        {
            toVisit.push(n);
        }

        ASTNode
        next()
        {
            ASTNode result = sentinel;

            while (true)
                {
                    if (toVisit.empty())
                        return sentinel;

                    result = toVisit.top();
                    toVisit.pop();

                    if (!ok(result))
                        continue; // Not OK to investigate.

                    if (result.getIteration() != iteration)
                        break; // not visited, DONE!
                }

            if (result == sentinel)
                return result;

            result.setIteration(iteration);

            const ASTVec& c = result.GetChildren();
            ASTVec::const_iterator itC = c.begin();
            ASTVec::const_iterator itendC = c.end();
            for (; itC != itendC; itC++)
                {
                    if (itC->getIteration() == iteration)
                        continue; // already examined.
                    toVisit.push(*itC);
                }
            return result;
        }

        ASTNode
        end()
        {
            return sentinel;
        }

        virtual bool
        ok(const ASTNode n)
        {
            return true;
        }
    };

    // Iterator that omits return atoms.
    class NonAtomIterator : public NodeIterator
    {
        virtual bool
        ok(const ASTNode& n)
        {
            return !n.isAtom();
        }

    public:
        NonAtomIterator(const ASTNode &n, const ASTNode &uf, STPMgr& stp) :
                NodeIterator(n, uf, stp)
        {
        }
    };
}

#endif /* NODEITERATOR_H_ */

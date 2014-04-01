#ifndef NODEITERATOR_H_
#define NODEITERATOR_H_

#include <stack>
#include <boost/utility.hpp>

namespace BEEV
{
    // Returns each node once, then returns the sentinel.
    // NB if the sentinel is contained in the node that's passed, then it'll be wrong.
    class NodeIterator : boost::noncopyable
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
};
#endif /* NODEITERATOR_H_ */

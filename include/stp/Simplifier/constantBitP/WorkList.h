// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2010
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

#ifndef WORKLIST_H_
#define WORKLIST_H_

namespace simplifier
{
  namespace constantBitP
  {
    using std::cerr;
    using std::endl;

    class WorkList
    {
      /* Rough worklist. Constraint Programming people have lovely structures to do this
       * The set (on my machine), is implemented by red-black trees. Deleting just from one end may unbalance the tree??
       */

    private:

      // select nodes from the cheap_worklist first.
      set<BEEV::ASTNode> cheap_workList; // Nodes to work on.
      set<BEEV::ASTNode> expensive_workList; // Nodes to work on.

      WorkList(const WorkList&); // Shouldn't needed to copy or assign.
      WorkList&
      operator=(const WorkList&);

      // We add to the worklist any node that immediately depends on a constant.
       void
       addToWorklist(const ASTNode& n, ASTNodeSet& visited)
       {
         if (n.isConstant())
             return;

         if (visited.find(n) != visited.end())
           return;

         visited.insert(n);

         bool alreadyAdded = false;

         for (unsigned i = 0; i < n.GetChildren().size(); i++)
           {
             if (!alreadyAdded && n[i].isConstant())
               {
                 alreadyAdded = true;
                 push(n);
               }
             addToWorklist(n[i], visited);
           }
       }

    public:
      // Add to the worklist any node that immediately depends on a constant.

      WorkList(const ASTNode& top)
      {
        initWorkList(top);
      }

      int size()
      {
        return cheap_workList.size() + expensive_workList.size();
      }

      void
      initWorkList(const ASTNode&n)
      {
        ASTNodeSet visited;
        addToWorklist(n, visited);
      }


      void
      push(const BEEV::ASTNode& n)
      {
        if (n.isConstant()) // don't ever add constants to the worklist.
          return;

        //cerr << "WorkList Inserting:" << n.GetNodeNum() << endl;
        if (n.GetKind() == BVMULT || n.GetKind() == BVPLUS || n.GetKind() == BVDIV)
          expensive_workList.insert(n);
        else
          cheap_workList.insert(n);

      }

      BEEV::ASTNode
      pop()
      {
        assert(!isEmpty());
        if (cheap_workList.size() > 0)
          {
            ASTNode ret = *cheap_workList.begin();
            cheap_workList.erase(cheap_workList.begin());
            return ret;
          }
        else
          {
            assert (expensive_workList.size() > 0);
            ASTNode ret = *expensive_workList.begin();
            expensive_workList.erase(expensive_workList.begin());
            return ret;
          }
      }

      bool
      isEmpty()
      {
        return cheap_workList.empty() && expensive_workList.empty();
      }

      void
      print()
      {
        cerr << "+Worklist" << endl;
        set<BEEV::ASTNode>::const_iterator it = cheap_workList.begin();
        while (it != cheap_workList.end())
          {
            cerr << *it << " ";
            it++;
          }

        it = expensive_workList.begin();
        while (it != expensive_workList.end())
          {
            cerr << *it << " ";
            it++;
          }

        cerr << "-Worklist" << endl;

      }
    };
  }
}

#endif /* WORKLIST_H_ */

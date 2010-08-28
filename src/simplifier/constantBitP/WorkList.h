#ifndef WORKLIST_H_
#define WORKLIST_H_

namespace simplifier
{
  namespace constantBitP
  {

    class WorkList
    {
      /* Rough worklist. Constraint Programming people have lovely structures to do this
       * The set (on my machine), is implemented by red-black trees. Deleting just from one end may unbalance the tree??
       */

    private:

      set<BEEV::ASTNode> workList; // Nodes to work on.
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
        workList.insert(n);
      }

      BEEV::ASTNode
      pop()
      {
        assert(!isEmpty());
        ASTNode ret = *workList.begin();
        workList.erase(workList.begin());
        return ret;
      }

      bool
      isEmpty()
      {
        return workList.empty();
      }

      void
      print()
      {
        cerr << "+Worklist" << endl;
        set<BEEV::ASTNode>::const_iterator it = workList.begin();
        while (it != workList.end())
          {
            cerr << *it << " ";
            it++;
          }
        cerr << "-Worklist" << endl;

      }
    };
  };
};

#endif /* WORKLIST_H_ */

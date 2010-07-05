#ifndef WORKLIST_H_
#define WORKLIST_H_

namespace simplifier
{
  namespace constantBitP
  {

    class WorkList
    {
      /* Rough worklist. Constraint Programming people probably have lovely structures to do this
       * The set (on my machine), is implemented by red-black trees. Deleting just from one end may unbalance the tree??
       */

    private:

      set<BEEV::ASTNode> workList; // Nodes to work on.
      WorkList(const WorkList&); // Shouldn't needed to copy or assign.
      WorkList&
      operator=(const WorkList&);

    public:
      WorkList()
      {
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

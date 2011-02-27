/*
  *    Descend through ITEs keeping a stack of what must be true/false.
  *    For instance. In the following:
  *        (ite (or a b) (not (or a b)) c )
  *
  *       In the lhs of the ITE, we know that a or b are true, so, we can rewrite it to:
  *       (ite (or a b) false c)
  *
 */

#ifndef UseITEContext_H_
#define UseITEContext_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
  class UseITEContext
  {
    NodeFactory *nf;
    RunTimes *runtimes;
    ASTNode ASTTrue, ASTFalse;

    void addToContext(const ASTNode&n , ASTNodeSet& context)
    {
      if (n.GetKind() == NOT && n[0].GetKind() == OR)
        {
          ASTVec flat = FlattenKind(OR, n[0].GetChildren());
          for (int i = 0; i < flat.size(); i++)
            context.insert(nf->CreateNode(NOT, flat[i]));
        }
      else if (n.GetKind() == AND)
        {
          ASTVec flat = FlattenKind(AND, n.GetChildren());
          context.insert(flat.begin(), flat.end());
        }
      else
        context.insert(n);

        //ASTNodeSet::iterator it = context.begin();
        //cout << "NEW CONTEXT";
        //while(it!=context.end())
        //  {
         //   cout << *it;
         //   it++;
         // }
    }

    ASTNode
    visit(const ASTNode &n, ASTNodeSet& visited, ASTNodeSet& context)
    {
      if (n.isConstant())
        return n;

      ASTNodeSet::iterator it;
      if (context.size() == 0 && ((it = visited.find(n)) != visited.end()))
        return n;

      if (context.find(n) != context.end())
        return ASTTrue;

      if (context.find(nf->CreateNode(NOT,n)) != context.end())
        return ASTFalse;

      if (n.isAtom())
        return n;

      ASTVec new_children;

      if (n.GetKind() == ITE)
        {
            ASTNodeSet lhsContext(context), rhsContext(context);
            addToContext(n[0],lhsContext);
            addToContext(nf->CreateNode(NOT,n[0]),rhsContext);
            new_children.push_back(visit(n[0], visited,context));
            new_children.push_back(visit(n[1], visited,lhsContext));
            new_children.push_back(visit(n[2], visited,rhsContext));
        }
      else
        {
          for (int i = 0; i < n.GetChildren().size(); i++)
            new_children.push_back(visit(n[i], visited, context));
        }

      ASTNode result;
      if (new_children != n.GetChildren())
          if (n.GetType() == BOOLEAN_TYPE)
              result =  nf->CreateNode(n.GetKind(), new_children);
            else
               result =  nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), new_children);
      else
        result = n;

      visited.insert(n);
      return result;

    }

  public:

    ASTNode
    topLevel(const ASTNode& n)
    {
      runtimes->start(RunTimes::UseITEContext);
      ASTNodeSet visited;
      ASTNodeSet context;
      ASTNode result= visit(n,visited,context);
      runtimes->stop(RunTimes::UseITEContext);
      cout << "from" << n << "to" << result;
      return result;
    }

    UseITEContext(STPMgr *bm)
    {
      runtimes = bm->GetRunTimes();
      nf = new SimplifyingNodeFactory(*(bm->hashingNodeFactory) ,*bm);
      ASTTrue = bm->ASTTrue;
      ASTFalse = bm->ASTFalse;
    }

    ~UseITEContext()
    {
      delete nf;
    }
  };
}
;

#endif

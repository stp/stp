/*
 * MutableASTNode.h
 *
 *  This is mutable unlike the normal ASTNode. It can be converted lazily to a ASTNode.
 */

#ifndef MUTABLEASTNODE_H_
#define MUTABLEASTNODE_H_
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "simplifier.h"

namespace BEEV
{
  class MutableASTNode
  {
    static vector<MutableASTNode*> all;

    typedef set<MutableASTNode *> ParentsType;
    ParentsType parents;


    MutableASTNode(const MutableASTNode&); // No definition
    MutableASTNode&
    operator=(const MutableASTNode &); // No definition

    MutableASTNode(const ASTNode& n_) :
      n(n_)
    {
      dirty = false;
    }

    // Make a mutable ASTNode graph like the ASTNode one, but with pointers back up too.
    // It's convoluted because we want a post order traversal. The root node of a sub-tree
    // will be created after its children.
    static MutableASTNode *
    build(ASTNode n, map<ASTNode, MutableASTNode *> & visited)
    {
      if (visited.find(n) != visited.end())
        {
          return visited.find(n)->second;
        }

      vector<MutableASTNode *> tempChildren;
      tempChildren.reserve(n.Degree());

      for (int i = 0; i < n.Degree(); i++)
        tempChildren.push_back(build(n[i], visited));

      MutableASTNode * mut = createNode(n);

      for (int i = 0; i < n.Degree(); i++)
        tempChildren[i]->parents.insert(mut);

      mut->children.insert(mut->children.end(),tempChildren.begin(),tempChildren.end());
      visited.insert(make_pair(n, mut));
      return mut;
    }

    bool dirty;

  public:

  MutableASTNode&  getParent()
    {
      assert (parents.size() == 1);
      return **(parents.begin());
    }

    ASTNode
    toASTNode(NodeFactory *nf)
    {
      if (!dirty)
        return n;

      if (children.size() == 0)
        return n;

      ASTVec newChildren;
      for (int i = 0; i < children.size(); i++)
        newChildren.push_back(children[i]->toASTNode(nf));

      if (n.GetType() == BOOLEAN_TYPE)
        {
          n = nf->CreateNode(n.GetKind(), newChildren);
        }
      else if (n.GetType() == BITVECTOR_TYPE)
        {
          n = nf->CreateTerm(n.GetKind(), n.GetValueWidth(), newChildren);
        }
      else
        {
          n = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), newChildren);
        }
      dirty = false;
      return n;
    }

    ASTNode n;
    vector<MutableASTNode *> children;

    static MutableASTNode *
    createNode(ASTNode n)
    {
      MutableASTNode * result = new MutableASTNode(n);
      all.push_back(result);
      return result;
    }

    bool
    isSymbol() const
    {
      bool result = n.GetKind() == SYMBOL;
      if (result)
        {
          assert(children.size() == 0);
        }
      return result;
    }

    static MutableASTNode *
    build(ASTNode n)
    {
      map<ASTNode, MutableASTNode *> visited;
      return build(n, visited);
    }

    void
    propagateUpDirty()
    {
      if (dirty)
        return;

      dirty = true;
      for (ParentsType::iterator it = parents.begin(); it != parents.end() ; it++)
        (*it)->propagateUpDirty();
    }

    void
    replaceWithVar(ASTNode newV, vector<MutableASTNode*>& variables)
    {
      assert(newV.GetKind() == SYMBOL);
      n = newV;
      removeChildren(variables);
      children.clear();
      assert(isSymbol());
      if (parents.size() == 1)
        variables.push_back(this);
      propagateUpDirty();
    }

    void
    removeChildren(vector<MutableASTNode*>& variables)
    {
      for (unsigned i = 0; i < children.size(); i++)
        {
          MutableASTNode * child = children[i];
          ParentsType& children_parents = child->parents;
          children_parents.erase(this);

          if (children_parents.size() == 0)
            {
              child->removeChildren(variables);
            }

          if (child->isUnconstrained())
            {
              variables.push_back(child);
            }
        }
    }

    // Visit the parent before children. So that we hopefully prune parts of the
    // tree. Ie given  ( F(x_1,... x_10000) = v), where v is unconstrained,
    // we don't spend time exploring F(..), but chop it out.
    void
    getAllUnconstrainedVariables(vector<MutableASTNode*> & result)
    {
      const int size = all.size();
      for (int i = size-1; i >=0 ; i--)
        {
          if (all[i]->isUnconstrained())
            result.push_back(all[i]);
        }
      return;
    }

    bool
    isUnconstrained()
    {
      if (!isSymbol())
        return false;

      return parents.size() == 1;
    }

    static void
    cleanup()
    {
      for (int i = 0; i < all.size(); i++)
        delete all[i];
      all.clear();
    }
  };

};

#endif /* MUTABLEASTNODE_H_ */


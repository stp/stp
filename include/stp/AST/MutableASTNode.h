/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb 14, 2011
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

/*
 *  This is mutable unlike the normal ASTNode. It can be converted lazily to a
 * ASTNode.
 */

#ifndef MUTABLEASTNODE_H_
#define MUTABLEASTNODE_H_
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <deque>

namespace stp
{
class MutableASTNode
{
  static THREAD_LOCAL_IE vector<MutableASTNode*> all;

  // Symbols that must never be reported unconstrained, however few
  // occurrences they have in this graph. The active array-equality solve
  // uses them as proxy/witness/name anchors or as leaves of future
  // refinement lemmas, whose meanings and SAT variables must survive this
  // pass.
  // A caller that rewrites the graph on the strength of
  // isUnconstrained() would delete such a definition, and the
  // substitution map's refusal to record the replacement comes too
  // late to undo it. Installed for the duration of a pass; NULL means
  // no restriction.
  static THREAD_LOCAL_IE const std::set<ASTNode>* untouchable;

public:
  // Scoped installer for the untouchable set; restores the previous
  // value so passes cannot leak the restriction into each other.
  class UntouchableScope
  {
    const std::set<ASTNode>* saved;

  public:
    explicit UntouchableScope(const std::set<ASTNode>* s) : saved(untouchable)
    {
      untouchable = s;
    }
    ~UntouchableScope() { untouchable = saved; }
    UntouchableScope(const UntouchableScope&) = delete;
    UntouchableScope& operator=(const UntouchableScope&) = delete;
  };

  static bool isUntouchable(const ASTNode& n)
  {
    return untouchable != NULL && untouchable->find(n) != untouchable->end();
  }

  typedef std::unordered_set<MutableASTNode*> ParentsType;
  ParentsType parents;

  MutableASTNode(const MutableASTNode&) = delete;  
  MutableASTNode& operator=(const MutableASTNode&) = delete;

private:

  MutableASTNode(const ASTNode& n_) : n(n_) { dirty = false; }

  /* Make a mutable ASTNode graph like the ASTNode one, but with pointers back
   * up too. It's convoluted because we want a post order traversal. The root
   * node of a sub-tree will be created after its children.
   */

  // The walk keeps its frames on the heap. How deeply a formula nests is the
  // input's choice, and deeply nested ones exist, so a call per level of the
  // DAG exhausts the stack: unconstrained-variable elimination builds this
  // graph for every query, and a 30,000-deep alternation of NOT and AND died
  // here. See DeepDag_Test.cpp.
  //
  // A node is answered from `visited` or it is built. A parent waiting for a
  // new child consumes the returned pointer directly; shared children that
  // were already built are still answered from `visited`.
  struct Frame
  {
    ASTNode n;
    size_t i = 0;
    bool waiting = false;
    vector<MutableASTNode*> tempChildren;

    Frame(const ASTNode& node) : n(node)
    {
      tempChildren.reserve(node.Degree());
    }
  };

public:
  static MutableASTNode* build(const ASTNode& n,
                               std::unordered_map<uint64_t, MutableASTNode*>& visited)
  {
    MutableASTNode* result = NULL;

    // What the recursive version answered without a call.
    auto known = [&visited, &result](const ASTNode& node) {
      const auto it = visited.find(node.GetNodeNum());
      if (it == visited.end())
        return false;
      result = it->second;
      return true;
    };

    if (known(n))
      return result;

    // A deque, so descending never moves the frames above it: `current`
    // stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n);

    while (true)
    {
      Frame& current = stack.back();

      if (current.waiting)
      {
        current.waiting = false;
        current.tempChildren.push_back(result);
        current.i++;
      }

      bool descended = false;
      while (current.i < current.n.Degree())
      {
        if (known(current.n[current.i]))
        {
          current.tempChildren.push_back(result);
          current.i++;
          continue;
        }

        // Nothing above may be read after this push.
        current.waiting = true;
        stack.emplace_back(current.n[current.i]);
        descended = true;
        break;
      }

      if (descended)
        continue;

      // Same order as the recursion: every child built, then the node, then
      // the parent links, then the entry that makes it answerable.
      MutableASTNode* mut = createNode(current.n);

      for (size_t i = 0; i < current.tempChildren.size(); i++)
      {
        current.tempChildren[i]->parents.insert(mut);
      }

      // The temporary already has exactly the representation the mutable
      // node needs. Transfer its allocation instead of allocating a second
      // pointer array and copying every child into it.
      mut->children = std::move(current.tempChildren);
      visited.insert(std::make_pair(current.n.GetNodeNum(), mut));

      result = mut;
      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }

private:
  bool dirty;

public:
  bool checkInvariant()
  {
    struct CheckFrame
    {
      MutableASTNode* node;
      size_t nextChild = 0;
      bool entered = false;
      bool waitingForChild = false;
    };

    std::deque<CheckFrame> stack;
    stack.push_back({this});
    while (!stack.empty())
    {
      CheckFrame& frame = stack.back();
      MutableASTNode* current = frame.node;

      if (!frame.entered)
      {
        // Symbols have no children.
        if (current->n.GetKind() == SYMBOL)
          assert(current->children.empty());

        // All my parents have me as a child.
        for (MutableASTNode* parent : current->parents)
        {
          // Only consumed by the assert, which an NDEBUG build compiles out.
          [[maybe_unused]] bool found = false;
          for (MutableASTNode* child : parent->children)
          {
            assert(child != NULL);
            if (child == current)
              found = true;
          }
          assert(found);
        }
        frame.entered = true;
      }

      if (frame.waitingForChild)
      {
        [[maybe_unused]] MutableASTNode* child =
            current->children[frame.nextChild];
        assert(child->parents.find(current) != child->parents.end());
        frame.nextChild++;
        frame.waitingForChild = false;
        continue;
      }

      if (frame.nextChild < current->children.size())
      {
        frame.waitingForChild = true;
        stack.push_back({current->children[frame.nextChild]});
        continue;
      }

      stack.pop_back();
    }

    return true; // ignored.
  }

  MutableASTNode& getParent()
  {
    assert(parents.size() == 1);
    return **(parents.begin());
  }

  ASTNode toASTNode(stp::STPMgr* stpMgr)
  {
    if (!dirty)
      return n;

    if (children.empty())
      return n;

    struct RebuildFrame
    {
      MutableASTNode* node;
      size_t nextChild = 0;
    };
    static_assert(sizeof(RebuildFrame) <= 2 * sizeof(void*),
                  "mutable rebuild frames must not own child buffers");

    std::vector<RebuildFrame> stack;
    stack.push_back({this});
    ASTVec newChildren;

    while (true)
    {
      RebuildFrame& frame = stack.back();
      MutableASTNode* current = frame.node;

      if (frame.nextChild < current->children.size())
      {
        MutableASTNode* child = current->children[frame.nextChild++];
        if (!child->dirty || child->children.empty())
          continue;

        stack.push_back({child});
        continue;
      }

      // Every child owns its rebuilt AST answer, so only the node currently
      // being recreated needs a child-handle buffer. Reuse one allocation
      // across the whole post-order walk instead of one vector per depth.
      newChildren.clear();
      newChildren.reserve(current->children.size());
      for (MutableASTNode* child : current->children)
        newChildren.push_back(child->n);

      // Don't use the simplifying node factory here. Imagine CreateNode
      // simplified (= 1 (ite x 1 0)) down to x. This object would become a
      // symbol while retaining the equality's children.
      if (current->n.GetType() == BOOLEAN_TYPE)
      {
        current->n = stpMgr->hashingNodeFactory->CreateNode(
            current->n.GetKind(), newChildren);
      }
      else if (current->n.GetType() == BITVECTOR_TYPE)
      {
        current->n = stpMgr->hashingNodeFactory->CreateTerm(
            current->n.GetKind(), current->n.GetValueWidth(),
            newChildren);
      }
      else
      {
        current->n = stpMgr->hashingNodeFactory->CreateArrayTerm(
            current->n.GetKind(), current->n.GetIndexWidth(),
            current->n.GetValueWidth(), newChildren);
      }

      current->dirty = false;
      stack.pop_back();
      if (stack.empty())
        return current->n;
    }
  }

  ASTNode n;
  vector<MutableASTNode*> children;

  static MutableASTNode* createNode(ASTNode n)
  {
    MutableASTNode* result = new MutableASTNode(n);
    all.push_back(result);
    return result;
  }

  bool isSymbol() const
  {
    bool result = n.GetKind() == SYMBOL;
    if (result)
    {
      assert(children.size() == 0);
    }
    return result;
  }

  static MutableASTNode* build(ASTNode n)
  {
    std::unordered_map<uint64_t, MutableASTNode*> visited;
    return build(n, visited);
  }

  void propagateUpDirty()
  {
    if (dirty)
      return;

    struct ParentFrame
    {
      MutableASTNode* node;
      ParentsType::const_iterator next;

      explicit ParentFrame(MutableASTNode* n)
          : node(n), next(n->parents.begin())
      {
      }
    };
    static_assert(sizeof(ParentFrame) <= 2 * sizeof(void*),
                  "dirty-walk frames must contain only traversal state");

    dirty = true;
    if (parents.empty())
      return;

    // Retain the parent-set continuation at each active level rather than
    // enqueueing every parent on the traversal frontier at once.
    vector<ParentFrame> path;
    path.emplace_back(this);
    while (!path.empty())
    {
      ParentFrame& frame = path.back();
      if (frame.next == frame.node->parents.end())
      {
        path.pop_back();
        continue;
      }

      MutableASTNode* parent = *frame.next++;
      if (parent->dirty)
        continue;

      parent->dirty = true;
      if (!parent->parents.empty())
        path.emplace_back(parent);
    }
  }

  void replaceWithAnotherNode(MutableASTNode* newN)
  {
    n = newN->n;
    vector<MutableASTNode*> vars;
    removeChildren(vars); // ignore the result
    children.clear();
    children.insert(children.begin(), newN->children.begin(),
                    newN->children.end());
    for (size_t i = 0; i < children.size(); i++)
      children[i]->parents.insert(this);

    propagateUpDirty();
    assert(newN->parents.size() == 0); // we don't copy 'em in you see.
    newN->removeChildren(vars);
  }

  void replaceWithVar(ASTNode newV, vector<MutableASTNode*>& variables)
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

  void removeChildren(vector<MutableASTNode*>& variables)
  {
    if (children.empty())
      return;

    struct RemoveFrame
    {
      MutableASTNode* node;
      size_t nextChild = 0;
      MutableASTNode* returningChild = NULL;
    };

    std::deque<RemoveFrame> stack;
    stack.push_back({this});
    while (!stack.empty())
    {
      RemoveFrame& frame = stack.back();
      if (frame.returningChild != NULL)
      {
        if (frame.returningChild->isUnconstrained())
          variables.push_back(frame.returningChild);
        frame.returningChild = NULL;
        continue;
      }

      if (frame.nextChild == frame.node->children.size())
      {
        stack.pop_back();
        continue;
      }

      MutableASTNode* child = frame.node->children[frame.nextChild++];
      // `parents` records unique parents, not edge multiplicity. If this
      // parent names the same child more than once, the first edge removes
      // the whole parent relationship. Following a later duplicate merely
      // because the child's parent set is already empty would tear the same
      // orphaned DAG down once per path -- exponentially for a layered DAG
      // whose nodes use the same child twice.
      if (child->parents.erase(frame.node) == 0)
        continue;

      frame.returningChild = child;
      if (child->parents.empty())
        stack.push_back({child});
    }
  }

  // Visit the parent before children. So that we hopefully prune parts of the
  // tree. Ie given  ( F(x_1,... x_10000) = v), where v is unconstrained,
  // we don't spend time exploring F(..), but chop it out.
  static void getAllUnconstrainedVariables(vector<MutableASTNode*>& result)
  {
    const int size = all.size();
    for (int i = size - 1; i >= 0; i--)
    {
      if (all[i]->isUnconstrained())
        result.push_back(all[i]);
    }
    return;
  }

  void getAllVariablesRecursively(vector<MutableASTNode*>& result,
                                  std::unordered_set<MutableASTNode*>& visited)
  {
    if (!visited.insert(this).second)
      return;

    if (isSymbol())
      result.push_back(this);

    if (children.empty())
      return;

    struct ChildFrame
    {
      MutableASTNode* node;
      size_t nextChild = 0;
    };
    static_assert(sizeof(ChildFrame) <= 2 * sizeof(void*),
                  "variable-walk frames must contain only traversal state");

    // A continuation per active ancestor retains the old left-to-right DFS
    // result order without retaining all unvisited siblings on the frontier.
    vector<ChildFrame> path;
    path.push_back({this});
    while (!path.empty())
    {
      ChildFrame& frame = path.back();
      if (frame.nextChild == frame.node->children.size())
      {
        path.pop_back();
        continue;
      }

      MutableASTNode* current = frame.node->children[frame.nextChild++];
      if (!visited.insert(current).second)
        continue;

      if (current->isSymbol())
        result.push_back(current);

      if (!current->children.empty())
        path.push_back({current});
    }
  }

  bool isUnconstrained()
  {
    if (!isSymbol())
      return false;

    // A protected symbol is never free to be given a value here, no
    // matter how it occurs; see the untouchable declaration above.
    if (isUntouchable(n))
      return false;

    return parents.size() == 1;
  }

  static void cleanup()
  {
    for (size_t i = 0; i < all.size(); i++)
      delete all[i];
    all.clear();
  }
};
}

#endif /* MUTABLEASTNODE_H_ */

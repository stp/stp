/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#ifndef DAGWALK_H_
#define DAGWALK_H_

#include "stp/AST/ASTNode.h"
#include <cstddef>
#include <utility>
#include <vector>

namespace stp
{

// Visit an immutable AST in left-to-right pre-order. `enter` is called once
// for each occurrence the walk reaches and returns whether that occurrence's
// children should be traversed. This lets a caller apply its own DAG memo or
// prune at a kind-specific boundary.
//
// Keep only the current node inline and suspended ancestors in `parents`.
// A wide node whose children are leaves or pruned needs no allocation, and
// the auxiliary memory of every other shape is O(depth), not O(frontier).
template <class Enter>
void walkPreOrder(const ASTNode& top, Enter enter)
{
  if (!enter(top) || top.Degree() == 0)
    return;

  struct Frame
  {
    const ASTNode* node;
    size_t nextChild = 0;
  };

  Frame current{&top};
  std::vector<Frame> parents;

  while (true)
  {
    if (current.nextChild < current.node->Degree())
    {
      const ASTNode* child = &(*current.node)[current.nextChild++];
      if (!enter(*child) || child->Degree() == 0)
        continue;

      parents.push_back(current);
      current = Frame{child};
      continue;
    }

    if (parents.empty())
      return;
    current = parents.back();
    parents.pop_back();
  }
}

// Rebuild a DAG bottom up, without putting the walk on the call stack.
//
// How deeply a formula nests is the input's choice, and inputs that nest
// thousands deep exist, so a pass that recurses once per level dies on them.
// This is the shape most of those passes have: visit a node's children, hand
// the node and its rebuilt children to `combine`, and use what comes back in
// place of the node. Frames live on the heap, so depth costs memory rather
// than stack.
//
// `combine(node, children)` returns the replacement for `node`. It is called
// once per node, after all of that node's children have been combined, and in
// left-to-right order, so it sees exactly what the equivalent recursive
// function saw and may call the node factory freely.
//
// `cache` maps a node to its replacement. A node reached twice is combined
// once, and a cache that outlives the call carries answers between calls. It
// needs find(), end() and insert(pair), which both ASTNodeMap and
// DenseNodeMap provide. Leaves have nothing to rebuild: they are returned as
// they are and are not cached.
//
// `combine` is a template parameter rather than a std::function so that it
// inlines: this runs once per node, and an indirect call per node would be a
// real cost on ordinary shallow input.
template <class Cache, class Combine>
ASTNode postOrderRebuild(const ASTNode& top, Cache& cache, Combine combine)
{
  // One node's progress: where its children begin in the shared LIFO arena,
  // and how far along its own child list it has got. Keeping an ASTVec in
  // every suspended frame allocated once per level on ordinary inputs.
  struct Frame
  {
    ASTNode n;
    size_t childrenBegin;
    size_t i = 0;
    bool waiting = false; // a child is being combined below.

    Frame(const ASTNode& node, const size_t begin)
        : n(node), childrenBegin(begin)
    {
    }
  };

  ASTNode result;

  // Results already collected by every suspended frame. A child frame owns
  // the suffix beginning at childrenBegin; when it completes, that suffix is
  // moved through one reusable vector for combine and then replaced by the
  // child's single result in its parent.
  ASTVec activeChildren;
  ASTVec combinedChildren;

  // Answers that need no frame, which is what the recursive form answered
  // without a call.
  auto known = [&cache, &result](const ASTNode& n) -> bool {
    if (n.Degree() == 0)
    {
      result = n;
      return true;
    }

    const auto it = cache.find(n);
    if (it != cache.end())
    {
      result = it->second;
      return true;
    }
    return false;
  };

  if (known(top))
    return result;

  // A deque, so descending never moves the frames above it: `current` stays
  // valid across a push.
  std::deque<Frame> stack;
  stack.emplace_back(top, activeChildren.size());

  while (true)
  {
    Frame& current = stack.back();

    if (current.waiting)
    {
      current.waiting = false;
      activeChildren.push_back(result);
      current.i++;
    }

    bool descended = false;
    while (current.i < current.n.Degree())
    {
      if (known(current.n[current.i]))
      {
        activeChildren.push_back(result);
        current.i++;
        continue;
      }

      // Nothing above may be read after this push.
      current.waiting = true;
      stack.emplace_back(current.n[current.i], activeChildren.size());
      descended = true;
      break;
    }

    if (descended)
      continue;

    assert(activeChildren.size() - current.childrenBegin ==
           current.n.Degree());
    combinedChildren.clear();
    combinedChildren.insert(
        combinedChildren.end(),
        std::make_move_iterator(activeChildren.begin() +
                                current.childrenBegin),
        std::make_move_iterator(activeChildren.end()));
    activeChildren.resize(current.childrenBegin);

    result = combine(current.n, combinedChildren);
    combinedChildren.clear();
    cache.insert({current.n, result});

    stack.pop_back();
    if (stack.empty())
      return result;
  }
}
}

#endif /* DAGWALK_H_ */

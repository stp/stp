/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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

#include "stp/Simplifier/Flatten.h"
#include "stp/Util/DagWalk.h"
#include <deque>
#include <limits>
#include <list>
#include <vector>

namespace stp
{

  ASTNode Flatten::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    
    removed=0;
    top_removed = 0;

    buildShareCount(n);
    

    // If the top level is an AND, we want to flatten it irrespective of sharing.
    ASTNode result = flatten(n, (AND == n.GetKind()));
    
    if (stpMgr->UserFlags.stats_flag)
    {
      std::cerr << "{Flatten} Internal nodes removed:" << removed << std::endl;
      std::cerr << "{Flatten} Top nodes removed:" << top_removed << std::endl;
    }

    shareCount.clear();
    fromTo.clear();

    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    return result;
  }

  // counter is 1 if the node has one reference in the tree.
  //
  // Iterative for the same reason as Rewriting::buildShareCount, which this
  // mirrors: the input decides the depth, so a call per level of the DAG
  // exhausts the stack. The continuation walk holds only suspended ancestors
  // rather than every sibling in a wide frontier.
  void Flatten::buildShareCount(const ASTNode& n)
  {
    walkPreOrder(n, [&](const ASTNode& current) {
      if (current.Degree() == 0)
        return false;

      if (shareCount[current.GetNodeNum()]++ > 0) // 0 first time, 1 second.
        return false;
      return true;
    });
  }

  // A leaf, or a node already flattened: answered without a frame, exactly
  // as the recursive version answered it without a call.
  bool Flatten::alreadyKnown(const ASTNode& n, ASTNode& answer)
  {
    if (n.Degree() == 0)
    {
      answer = n;
      return true;
    }

    const auto it = fromTo.find(n.GetNodeNum());
    if (it != fromTo.end())
    {
      answer = it->second;
      return true;
    }
    return false;
  }

  // The walk one node is part-way through. Everything here was a local of
  // the recursive flatten(); it lives on the heap because the input decides
  // how many of them are live at once.
  struct Flatten::Frame
  {
    ASTNode n;
    Kind k;
    bool top;
    bool flattenable;
    bool changed = false;

    ASTChildren children;
    unsigned it0 = 0; // original children consumed
    unsigned i = 0;   // position in nextChildren

    // The vectors and set are only needed after this node changes. Keeping
    // an index here makes the common unchanged frame small; flatten() lends
    // the actual storage from a LIFO scratch pool.
    static constexpr unsigned noScratch =
        std::numeric_limits<unsigned>::max();
    unsigned scratch = noScratch;

    // Set while this node waits for a child's flatten() to come back.
    ASTNode pending;
    bool waiting = false;

    Frame(const ASTNode& n_, bool top_)
        : n(n_), k(n_.GetKind()), top(top_),
          flattenable(OR == k || AND == k || XOR == k || BVXOR == k ||
                      BVOR == k || BVAND == k || BVPLUS == k || BVMULT == k),
          children(n_.GetChildren())
    {
    }
  };

  ASTNode Flatten::flatten(const ASTNode& n, bool top)
  {
    static_assert(sizeof(Frame) <= 80,
                  "Flatten frames must stay cheap at deep DAG depths");

    ASTNode result;
    if (alreadyKnown(n, result))
      return result;

    // A deque, so that descending into a child never moves the frames
    // above it: `current` below stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n, top);

    struct Scratch
    {
      ASTVec newChildren;
      ASTVec nextChildren;
      std::unordered_set<uint64_t> seen;
      // Entries merged into this frame instead of kept as children; balances
      // the rebuild bookkeeping check below.
      size_t flattenedIn = 0;

      void clear()
      {
        newChildren.clear();
        nextChildren.clear();
        seen.clear();
        flattenedIn = 0;
      }
    };

    // Scratch slots are acquired and released in traversal order: an active
    // child's slot is always above its parent's. Reusing them retains vector
    // and hash-table capacity without carrying that state in every frame.
    std::vector<Scratch> scratches;
    unsigned scratchesInUse = 0;

    auto scratchFor = [&](Frame& f) -> Scratch&
    {
      if (f.scratch == Frame::noScratch)
      {
        assert(scratchesInUse <= scratches.size());
        assert(scratchesInUse < Frame::noScratch);
        f.scratch = scratchesInUse++;
        if (f.scratch == scratches.size())
          scratches.emplace_back();
      }
      return scratches[f.scratch];
    };

    auto releaseScratch = [&](Frame& f)
    {
      if (f.scratch == Frame::noScratch)
        return;
      assert(f.scratch + 1 == scratchesInUse);
      scratches[f.scratch].clear();
      --scratchesInUse;
    };

    // Copy on write.
    auto fill = [&](Frame& f)
    {
      assert(0 == f.i);

      Scratch& scratch = scratchFor(f);
      scratch.newChildren.reserve(f.children.size());
      scratch.newChildren.insert(scratch.newChildren.end(),
                                 f.children.begin(),
                                 f.children.begin() + (f.it0 - 1));
      f.changed = true;
    };

    while (true)
    {
      Frame& current = stack.back();

      // Pick up the child this frame descended for. `result` is what its
      // flatten() returned.
      if (current.waiting)
      {
        if (result != current.pending && !current.changed)
          fill(current);
        if (current.changed)
          scratches[current.scratch].newChildren.push_back(result);
        current.waiting = false;
      }

      bool descended = false;

      while (current.it0 < current.children.size() ||
             (current.scratch != Frame::noScratch &&
              current.i < scratches[current.scratch].nextChildren.size()))
      {
        // By value: the flattening branch below appends to nextChildren,
        // which can move what a reference into it points at.
        const ASTNode c = (current.it0 < current.children.size())
                              ? current.children[current.it0++]
                              : scratches[current.scratch]
                                    .nextChildren[current.i++];

        if (current.flattenable && c.GetKind() == current.k &&
            (current.top || shareCount[c.GetNodeNum()] == 1))
        {
          assert(c.Degree() > 1);
          if (!current.changed)
            fill(current);
          Scratch& scratch = scratches[current.scratch];

          if (current.top)
            top_removed++;
          else
            removed++;
          scratch.flattenedIn++;

          for (const auto& e : c.GetChildren())
          {
            if (BVAND == current.k || AND == current.k || BVOR == current.k ||
                OR == current.k)
            {
              if (!scratch.seen.insert(e.GetNodeNum()).second)
                continue;
            }
            scratch.nextChildren.push_back(e);
          }
          shareCount[c.GetNodeNum()]--;
        }
        else
        {
          ASTNode r;
          if (alreadyKnown(c, r))
          {
            if (r != c && !current.changed)
              fill(current);
            if (current.changed)
              scratches[current.scratch].newChildren.push_back(r);
            continue;
          }

          // Where the recursive version called flatten(c). Nothing above
          // may be read after the push.
          current.pending = c;
          current.waiting = true;
          stack.emplace_back(c, false);
          descended = true;
          break;
        }
      }

      if (descended)
        continue;

      Frame& done = stack.back();
      result = done.n;

      if (done.changed)
      {
        Scratch& scratch = scratches[done.scratch];
        // Every consumed entry either landed in newChildren or was flattened
        // in, adding its children to nextChildren minus what the AND/OR
        // duplicate filter dropped. The filter means newChildren can end up
        // *smaller* than the original degree, so the check is this balance,
        // not `Degree() <= newChildren.size()`.
        assert(scratch.newChildren.size() + scratch.flattenedIn ==
               done.n.Degree() + scratch.nextChildren.size());

        if (done.n.GetType() == BOOLEAN_TYPE)
          result = nf->CreateNode(done.k, scratch.newChildren);
        else
          result = nf->CreateArrayTerm(done.k, done.n.GetIndexWidth(),
                                       done.n.GetValueWidth(),
                                       scratch.newChildren);

        shareCount[result.GetNodeNum()]++; // I'm guessing it's unusal, but we might make a node we already have.
      }

      if (shareCount[done.n.GetNodeNum()] > 1)
        fromTo.insert({done.n.GetNodeNum(), result});

      releaseScratch(done);
      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }
}

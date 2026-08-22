/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
 *
 * BEGIN DATE: November, 2005
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

#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Simplifier/Simplifier.h"
#include <vector>

namespace stp
{
using std::endl;
using std::make_pair;
using std::set;
using std::cout;

DLL_PUBLIC SubstitutionMap::~SubstitutionMap()
{
  delete SolverMap;
}

// if a is READ(Arr,const) and b is BVCONST then return 1.
// if a is a symbol SYMBOL, return 1.
// if b is READ(Arr,const) and a is BVCONST then return -1
// if b is a symbol return -1.
//
// else return 0 by default
int TermOrder(const ASTNode& a, const ASTNode& b)
{
  const Kind k1 = a.GetKind();
  const Kind k2 = b.GetKind();

  if (k1 == SYMBOL)
    return 1;

  if (k2 == SYMBOL)
    return -1;

  // a is of the form READ(Arr,const), and b is const, or
  if ((k1 == READ && a[0].GetKind() == SYMBOL && a[1].GetKind() == BVCONST &&
       (k2 == BVCONST)))
    return 1;

  // b is of the form READ(Arr,const), and a is const, or
  // b is of the form var, and a is const
  if ((k1 == BVCONST) &&
      ((k2 == READ && b[0].GetKind() == SYMBOL && b[1].GetKind() == BVCONST)))
    return -1;

  return 0;
}

// idempotent.
ASTNode SubstitutionMap::applySubstitutionMap(const ASTNode& n)
{
  bm->GetRunTimes()->start(RunTimes::ApplyingSubstitutions);
  DenseNodeMap cache;
  ASTNode result = replace(n, *SolverMap, cache, bm->defaultNodeFactory, false, false);

  bm->GetRunTimes()->stop(RunTimes::ApplyingSubstitutions);
  return result;
}

// Must be called on top level other wise not rewritten through properly.
ASTNode SubstitutionMap::applySubstitutionMapAtTopLevel(const ASTNode& topLevel)
{
  if (!hasUnappliedSubstitutions())
    return topLevel;

  ASTNode result = applySubstitutionMap(topLevel);
  
  haveAppliedSubstitutionMap();

  return result;
}


// not always idempotent.
ASTNode SubstitutionMap::applySubstitutionMapUntilArrays(const ASTNode& n)
{
  DenseNodeMap cache;
  return applySubstitutionMapUntilArrays(n, cache);
}

// not always idempotent.
ASTNode SubstitutionMap::applySubstitutionMapUntilArrays(const ASTNode& n, DenseNodeMap& cache)
{
  bm->GetRunTimes()->start(RunTimes::ApplyingSubstitutions);
  ASTNode result = replace(n, *SolverMap, cache, bm->defaultNodeFactory, true, false);
  bm->GetRunTimes()->stop(RunTimes::ApplyingSubstitutions);
  return result;
}


template <class NodeMapType>
ASTNode SubstitutionMap::replace(const ASTNode& n, NodeMapType& fromTo,
                                 NodeMapType& cache, NodeFactory* nf)
{
  if (0 == fromTo.size())
    return n;
  else
    return replace(n, fromTo, cache, nf, false, false);
}

// NOTE the fromTo map is changed as we traverse downwards.
// We call replace on each of the things in the fromTo map aswell.
// This is in case we have a fromTo map: (x maps to y), (y maps to 5),
// and pass the replace() function the node "x" to replace, then it
// will return 5, rather than y.

// NB: You can't use this to map from "5" to the symbol "x" say.
// It's optimised for the symbol to something case.

// The walk keeps its frames on the heap. Input decides how deeply a formula
// nests, and deeply nested ones exist, so a call per level of the DAG
// exhausts the stack. See DeepDag_Test.cpp.
template <class NodeMapType>
ASTNode SubstitutionMap::replace(const ASTNode& n, NodeMapType& fromTo,
                                 NodeMapType& cache, NodeFactory* nf,
                                 bool stopAtArrays, bool preventInfinite)
{
  // One node's progress. `phase` says what a value arriving from below is:
  // the recursive version called itself from three places -- following a
  // chain of substitutions, replacing a child, and running again over a
  // node it had just rebuilt -- and a frame has to know which it awaits.
  struct Frame
  {
    ASTNode n;
    Kind k;
    unsigned int indexWidth;
    unsigned int valueWidth;

    enum Phase
    {
      AwaitingChain,
      AwaitingChild,
      AwaitingRemap
    };
    Phase phase;

    ASTNode chainTarget; // what n maps to, for AwaitingChain
    ASTNode remapped;    // the rebuilt node, for AwaitingRemap
    bool started = false;

    ASTChildren children;
    ASTVec newChildren;
    bool changed = false;
    unsigned i = 0; // the child being worked on
    bool waiting = false;
  };

  ASTNode result;

  // The head of the recursive version, in its order -- in particular the
  // fromTo test before the SYMBOL test, which is what makes substituting
  // for a symbol work at all. Either the answer needs no frame and lands in
  // `result`, or `frame` is prepared for the walk below it.
  auto prepare = [&](const ASTNode& node, Frame& frame) -> bool
  {
    const Kind k = node.GetKind();
    if (k == BVCONST || k == TRUE || k == FALSE)
    {
      result = node;
      return false;
    }

    typename NodeMapType::const_iterator it;

    if ((it = cache.find(node)) != cache.end())
    {
      result = it->second;
      return false;
    }

    if ((it = fromTo.find(node)) != fromTo.end())
    {
      // By value, not by reference: the walk below inserts into and erases
      // from fromTo, and a DenseNodeMap moves its elements when that
      // happens -- a reference here would dangle.
      frame.chainTarget = it->second;
      assert(frame.chainTarget.GetIndexWidth() == node.GetIndexWidth());
      frame.phase = Frame::AwaitingChain;

      if (preventInfinite)
        cache.insert(make_pair(node, frame.chainTarget));
    }
    // These can't be created like regular nodes are
    else if (k == SYMBOL)
    {
      result = node;
      return false;
    }
    else if (stopAtArrays && node.GetIndexWidth() > 0) // is an array.
    {
      result = node;
      return false;
    }
    // Floating-point special constants (NaN, +/-oo, +/-zero) are nullary
    // leaves that the BVCONST/TRUE/FALSE test above does not cover, so they
    // reach here with no children. They are values: there is nothing to
    // substitute into.
    else if (node.Degree() == 0)
    {
      result = node;
      return false;
    }
    else
    {
      frame.phase = Frame::AwaitingChild;
      frame.children = node.GetChildren();
      assert(frame.children.size() > 0);
      // Should have no leaves left here.
    }

    frame.n = node;
    frame.k = k;
    frame.indexWidth = node.GetIndexWidth();
    frame.valueWidth = node.GetValueWidth();
    return true;
  };

  // Answer settled roots before constructing the stack, so constants, leaves,
  // stopped arrays and cache hits pay for no traversal storage.
  Frame top;
  if (!prepare(n, top))
    return result;

  // Most substitution walks are only a few frames deep. Keep those frames in
  // one compact allocation instead of a deque's map and fixed-size blocks.
  // A push may move every frame, so callers of descend must not retain or use
  // a Frame reference after descend returns true.
  std::vector<Frame> stack;
  stack.push_back(std::move(top));

  auto descend = [&](const ASTNode& node, Frame* waitingParent = nullptr) -> bool
  {
    Frame frame;
    if (!prepare(node, frame))
      return false;
    if (waitingParent != nullptr)
      waitingParent->waiting = true;
    stack.push_back(std::move(frame));
    return true;
  };

  // Copy on write, one child at a time.
  auto foldChild = [](Frame& f, const ASTNode& newNode)
  {
    const ASTNode& child = f.children[f.i];
    if (!f.changed && newNode != child)
    {
      f.newChildren.reserve(f.children.size());
      f.newChildren.insert(f.newChildren.end(), f.children.begin(),
                           f.children.begin() + f.i);
      f.changed = true;
    }
    if (f.changed)
      f.newChildren.push_back(newNode);
    f.i++;
  };

  // The answer for a rebuilt node, cached and handed back up.
  auto finish = [&](Frame& f, const ASTNode& value)
  {
    assert(value.GetValueWidth() == f.valueWidth);
    assert(value.GetIndexWidth() == f.indexWidth);

    // If there is already an "n" element in the cache, the maps semantics
    // are to ignore the next insertion.
    if (preventInfinite)
      cache.erase(f.n);

    cache.insert(make_pair(f.n, value));
    result = value;
    stack.pop_back();
  };

  while (true)
  {
    Frame& current = stack.back();

    // We call replace on each of the things in the fromTo map aswell.
    // This is in case we have a fromTo map: (x maps to y), (y maps to 5),
    // and pass the replace() function the node "x" to replace, then it
    // will return 5, rather than y.
    if (current.phase == Frame::AwaitingChain)
    {
      if (!current.started)
      {
        current.started = true;
        if (descend(current.chainTarget))
          continue;
      }

      const ASTNode replaced = result; // replace(chainTarget)
      if (replaced != current.chainTarget)
      {
        fromTo.erase(current.n);
        fromTo[current.n] = replaced;
      }

      if (preventInfinite)
        cache.erase(current.n);

      cache.insert(make_pair(current.n, replaced));
      result = replaced;
      stack.pop_back();

      if (stack.empty())
        return result;
      continue;
    }

    if (current.phase == Frame::AwaitingRemap)
    {
      if (!current.started)
      {
        current.started = true;
        if (descend(current.remapped))
          continue;
      }

      finish(current, result); // replace(remapped)
      if (stack.empty())
        return result;
      continue;
    }

    if (current.waiting)
    {
      current.waiting = false;
      foldChild(current, result);
    }

    bool descended = false;
    while (current.i < current.children.size())
    {
      // descend installs the continuation only when it will push, and does
      // so before vector growth can move `current`.
      if (descend(current.children[current.i], &current))
      {
        descended = true;
        break;
      }
      foldChild(current, result);
    }
    if (descended)
      continue;

    assert(current.newChildren.size() == 0 ||
           (current.newChildren.size() == current.children.size()));

    // This code short-cuts if the children are the same. Nodes with the same
    // children,
    // won't have necessarily given the same node if the simplifyingNodeFactory is
    // enabled
    // now, but wasn't enabled when the node was created. Shortcutting saves lots
    // of time.
    if (current.newChildren.size() == 0)
    {
      cache.insert(make_pair(current.n, current.n));
      result = current.n;
      stack.pop_back();

      if (stack.empty())
        return result;
      continue;
    }

    ASTNode built;
    if (current.valueWidth == 0) // n.GetType() == BOOLEAN_TYPE
    {
      built = nf->CreateNode(current.k, current.newChildren);
    }
    else
    {
      // If the index and value width aren't saved, they are reset sometimes (??)
      built = nf->CreateArrayTerm(current.k, current.indexWidth,
                                  current.valueWidth, current.newChildren);
    }

    // We may have created something that should be mapped. For instance,
    // if n is READ(A, x), and the fromTo is: {x==0, READ(A,0) == 1}, then
    // by here the result will be READ(A,0). Which needs to be mapped again..
    // I hope that this makes it idempotent.

    if (fromTo.find(built) != fromTo.end())
    {
      // map n->result, if running replace() on result gives us 'n', it will
      // not infinite loop.
      // This is only currently required for the bitblast equivalence stuff.
      if (preventInfinite)
        cache.insert(make_pair(current.n, built));

      current.phase = Frame::AwaitingRemap;
      current.remapped = built;
      current.started = false;
      continue;
    }

    finish(current, built);
    if (stack.empty())
      return result;
  }
}

// The two map types replace() runs over: the SolverMap paths use
// DenseNodeMap; external callers pass ASTNodeMaps.
template ASTNode SubstitutionMap::replace<ASTNodeMap>(const ASTNode&,
    ASTNodeMap&, ASTNodeMap&, NodeFactory*);
template ASTNode SubstitutionMap::replace<ASTNodeMap>(const ASTNode&,
    ASTNodeMap&, ASTNodeMap&, NodeFactory*, bool, bool);
template ASTNode SubstitutionMap::replace<DenseNodeMap>(const ASTNode&,
    DenseNodeMap&, DenseNodeMap&, NodeFactory*);
template ASTNode SubstitutionMap::replace<DenseNodeMap>(const ASTNode&,
    DenseNodeMap&, DenseNodeMap&, NodeFactory*, bool, bool);

// Adds to the dependency graph that n0 depends on the variables in n1.
// It's not the transitive closure of the dependencies. Just the variables in
// the expression "n1".
// This is only needed as long as all the substitution rules haven't been
// written through.
void SubstitutionMap::buildDepends(const ASTNode& n0, const ASTNode& n1)
{
  if (n0.GetKind() != SYMBOL)
    return;

  if (n1.isConstant())
    return;

  vector<Symbols*> av;
  vars.VarSeenInTerm(vars.getSymbol(n1), rhs_visited, rhs, av);

  sort(av.begin(), av.end());
  for (size_t i = 0; i < av.size(); i++)
  {
    if (i != 0 && av[i] == av[i - 1])
      continue; // Treat it like a set of Symbol* in effect.

    ASTNodeSet* sym = (vars.TermsAlreadySeenMap.find(av[i])->second);
    if (rhsAlreadyAdded.find(sym) != rhsAlreadyAdded.end())
      continue;
    rhsAlreadyAdded.insert(sym);

    // cout << loopCount++ << " ";
    // cout << "initial" << rhs.size() << " Adding: " <<sym->size();
    rhs.insert(sym->begin(), sym->end());
    // cout << "final:" << rhs.size();
    // cout << "added:" << sym << endl;
  }

  assert(dependsOn.find(n0) == dependsOn.end());
  dependsOn.insert(make_pair(n0, vars.getSymbol(n1)));
}

// Take the transitive closure of the varsToCheck. Storing the result in
// visited.
void SubstitutionMap::loops_helper(const set<ASTNode>& varsToCheck,
                                   set<ASTNode>& visited)
{
  set<ASTNode>::const_iterator visitedIt = visited.begin();

  set<ASTNode> toVisit;
  vector<ASTNode> visitedN;

  // for each variable.
  for (set<ASTNode>::const_iterator varIt = varsToCheck.begin();
       varIt != varsToCheck.end(); varIt++)
  {
    while (visitedIt != visited.end() && *visitedIt < *varIt)
      visitedIt++;

    if ((visitedIt != visited.end()) && *visitedIt == *varIt)
      continue;

    visitedN.push_back(*varIt);
    DependsType::iterator it;
    if ((it = dependsOn.find(*varIt)) != dependsOn.end())
    {
      Symbols* s = it->second;
      bool destruct;
      ASTNodeSet* varsSeen = vars.SetofVarsSeenInTerm(s, destruct);
      toVisit.insert(varsSeen->begin(), varsSeen->end());

      if (destruct)
        delete varsSeen;
    }
  }

  visited.insert(visitedN.begin(), visitedN.end());

  visitedN.clear();

  if (toVisit.size() != 0)
    loops_helper(toVisit, visited);
}

// If n0 is replaced by n1 in the substitution map. Will it cause a loop?
// i.e. will the dependency graph be an acyclic graph still.
// For example, if we have x = F(y,z,w), it would make the substitutionMap loop
// if there's already z = F(x).
bool SubstitutionMap::loops(const ASTNode& n0, const ASTNode& n1)
{
  if (n0.GetKind() != SYMBOL)
    return false; // sometimes this function is called with constants on the
                  // lhs.

  if (n1.isConstant())
    return false; // constants contain no variables. Can't loop.

  // We are adding an edge FROM n0, so unless there is already an edge TO n0,
  // there is no change it can loop. Unless adding this would add a TO and FROM
  // edge.
  if (rhs.find(n0) == rhs.end())
  {
    return vars.VarSeenInTerm(n0, n1);
  }

  if (n1.GetKind() == SYMBOL && dependsOn.find(n1) == dependsOn.end())
    return false; // The rhs is a symbol and doesn't appear.

  if (debug_substn)
    cout << loopCount++ << endl;

  bool destruct = true;
  ASTNodeSet* dependN = vars.SetofVarsSeenInTerm(n1, destruct);

  if (debug_substn)
  {
    cout << n0 << " "
         << n1.GetNodeNum(); //<< " Expression size:" << bm->NodeSize(n1,true);
    cout << "Variables in expression: " << dependN->size() << endl;
  }

  set<ASTNode> depend(dependN->begin(), dependN->end());

  if (destruct)
    delete dependN;

  set<ASTNode> visited;
  loops_helper(depend, visited);

  bool loops = visited.find(n0) != visited.end();

  if (debug_substn)
    cout << "Visited:" << visited.size() << "Loops:" << loops << endl;

  return (loops);
}

// Two obligations while array equality is active, with two different
// shapes. Callers pass the substitution oriented: "key" is what gets
// replaced and whose defining equation leaves the formula.
//
// Protected symbols -- equality abstraction variables, witness indices
// and witness-read names, lemma-leaf names -- must survive to the
// bit-blast, because their SAT variables carry the refinement lemmas
// and the witness-read equations are how each equality operand's
// current form is recovered afterwards. A protected symbol is refused
// on whichever side it appears: as a key it would vanish outright, and
// keeping the check symmetric costs nothing, since there are only a
// handful of them.
//
// Reads are different, and only one orientation is dangerous. With the
// checker owning the complete array graph, an access it never sees is
// an access it cannot catch a disagreement at. TermOrder makes a READ
// the key in exactly one situation, READ(Arr, const) against a
// constant; that substitution deletes the read from the formula and
// bakes its value in, so a second read of the same cell across a true
// array equality would have nothing left to conflict with. Refuse it.
//
// The other orientation, "v |-> READ(A, i)", deletes nothing: the read
// is copied to wherever v occurred and reaches the checker from there,
// and if v occurred nowhere else then the read constrained nothing to
// begin with. Refusing that one as well -- which is what a bare
// "either side is a READ" test does -- suppressed BVSolver over every
// read in the query, connected to an equality or not, and cost more
// than the whole decision procedure on array-heavy input.
bool SubstitutionMap::theoryProtected(const ASTNode& key,
                                      const ASTNode& value) const
{
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->activeInSolve())
  {
    if (key.GetKind() == SYMBOL && ext->isProtected(key))
      return true;
    if (value.GetKind() == SYMBOL && ext->isProtected(value))
      return true;
    // The equation-deleting orientation: the read itself is the key.
    if (key.GetKind() == READ)
      return true;
  }

  UFContext* uf = bm->getUFContextIfAny();
  if (uf != NULL && uf->activeInSolve())
  {
    if (key.GetKind() == SYMBOL && uf->isProtected(key))
      return true;
    if (value.GetKind() == SYMBOL && uf->isProtected(value))
      return true;
  }
  return false;
}

bool SubstitutionMap::UpdateSubstitutionMap(const ASTNode& e0,
                                            const ASTNode& e1)
{
  int i = TermOrder(e0, e1);
  if (0 == i)
    return false;

  // TermOrder has already chosen which side is the key: e0 when it
  // returned 1, e1 when it returned -1. theoryProtected needs
  // that orientation, because only a read in key position deletes an
  // access. The later "i = -1" flip below cannot change the answer:
  // it applies only when both sides are symbols.
  if (theoryProtected(1 == i ? e0 : e1, 1 == i ? e1 : e0))
    return false;

  assert(e0 != e1);
  // A substituted pair must agree as bitvectors/arrays AND as floats. The
  // format check is trivially true for non-floats (both report (0, 0)); for
  // floats the widths agree whenever the formats do, since a float's value
  // width is exp_width + sig_width. These used to be a disjunction, which
  // any two non-float nodes satisfied through the vacuous format arm.
  assert(e0.GetValueWidth() == e1.GetValueWidth() &&
         e0.GetIndexWidth() == e1.GetIndexWidth());
  assert(e0.GetExpWidth() == e1.GetExpWidth() &&
         e0.GetSigWidth() == e1.GetSigWidth());

  if (e0.GetKind() == SYMBOL)
  {
    if (InsideSubstitutionMap(e0))
    {
      // e0 and e1 might both be variables, e0 is already substituted for,
      // but maybe not e1.
      if (e1.GetKind() == SYMBOL)
        i = -1;
      else
        return false; // already in the map.
    }

    if (loops(e0, e1))
      return false; // loops.
  }

  if (e1.GetKind() == SYMBOL)
  {
    if (InsideSubstitutionMap(e1))
      return false; // already in the map.

    if (loops(e1, e0))
      return false; // loops
  }

  // e0 is of the form READ(Arr,const), and e1 is const, or
  // e0 is of the form var, and e1 is a function.
  if (1 == i && !InsideSubstitutionMap(e0))
  {
    buildDepends(e0, e1);
    (*SolverMap)[e0] = e1;
    return true;
  }

  // e1 is of the form READ(Arr,const), and e0 is const, or
  // e1 is of the form var, and e0 is const
  if (-1 == i && !InsideSubstitutionMap(e1))
  {
    buildDepends(e1, e0);
    (*SolverMap)[e1] = e0;
    return true;
  }

  return false;
}
} //namespace stp

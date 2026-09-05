/********************************************************************
 * AUTHORS: Trevor Hansen
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

#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/AST/AST.h"
// FIXME: External library
#include "extlib-constbv/constantbv.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include <algorithm>
#include <iostream>
#include <vector>

using std::endl;
using std::make_pair;
using std::pair;

using namespace stp;

/*
 *	Propagates known fixed 0 or 1 bits, as well as TRUE/FALSE values through the
 *formula.
 *
 *	Our approach differs from others because the transfer functions are (mostly)
 *optimally precise.
 *
 *	FixedBits stores booleans in 1 bit-bitvectors.
 */

namespace simplifier
{
namespace constantBitP
{

// If the bits are totally fixed, then return a new matching ASTNode.
ASTNode ConstantBitPropagation::bitsToNode(NodeFactory* nf,
                                           const ASTNode& node,
                                           const FixedBits& bits)
{
  ASTNode result;

  assert(bits.isTotallyFixed());
  assert(!node.isConstant()); // Peformance. Shouldn't waste time calling it on
                              // constants.

  if (node.GetType() == BOOLEAN_TYPE)
  {
    if (bits.getValue(0))
    {
      result = nf->getTrue();
    }
    else
    {
      result = nf->getFalse();
    }
  }
  else if (node.GetType() == BITVECTOR_TYPE)
  {
    result = nf->CreateConstant(bits.GetBVConst(), node.GetValueWidth());
  }
  else
    FatalError("sadf234s");

  assert(result.isConstant());
  return result;
}

// Put anything that's entirely fixed into a from->to map.
ASTNodeMap ConstantBitPropagation::getAllFixed()
{
  NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it, itEnd;

  ASTNodeMap toFrom;

  // iterates through all the pairs of node->fixedBits.
  for (it = fixedMap->map->begin(), itEnd = fixedMap->map->end(); it != itEnd;
       ++it)
  {
    const ASTNode& node = (it->first);
    const FixedBits& bits = *it->second;

    // Don't constrain nodes we already know all about.
    if (node.isConstant())
      continue;

    // Concat doesn't change the fixings. Ignore it.
    if (BVCONCAT == node.GetKind())
      continue;

    // Constant-bit propagation only reasons about Boolean and bit-vector
    // values. A floating-point node has value width zero, so it is given a
    // placeholder FixedBits that does not describe its packed contents; it must
    // never be turned back into a constant here.
    if (node.GetType() != BOOLEAN_TYPE && node.GetType() != BITVECTOR_TYPE)
      continue;

    if (bits.isTotallyFixed())
    {
      toFrom.insert(make_pair(node, bitsToNode(nf, node, bits)));
    }
  }

  return toFrom;
}

void ConstantBitPropagation::setNodeToTrue(const ASTNode& top)
{
  assert(!topFixed);
  topFixed = true;

  FixedBits& topFB = *getCurrentFixedBits(top);
  topFB.setFixed(0, true);
  topFB.setValue(0, true);
  workList->push(top);
}

// Propagates. No writing in of values. Doesn't assume the top is true.
ConstantBitPropagation::ConstantBitPropagation(stp::STPMgr* mgr_,
                                               stp::Simplifier* _sm,
                                               NodeFactory* _nf,
                                               const ASTNode& top)
{
  assert(BOOLEAN_TYPE == top.GetType());
  //assert(mgr->UserFlags.bitConstantProp_flag);

  mgr = mgr_;

  status = NO_CHANGE;
  simplifier = _sm;
  nf = _nf;
  fixedMap = new NodeToFixedBitsMap(1000); // better to use the function that
                                           // returns the number of nodes..
                                           // whatever that is.
  workList = new WorkList(top);
  dependents = new Dependencies(top); // List of the parents of a node.
  msm = new MultiplicationStatsMap();

  // not fixing the topnode.
  propagate();

  topFixed = false;
}

// Rewrite the children of "n" with the map, then rebuild "n" on top of
// them. Starting one level down means an entry for "n" itself in the map
// can't fire: a node is never its own descendant, so the map can safely
// hold a fact about "n" while "n"'s fact is being rebuilt.
static ASTNode replaceChildren(const ASTNode& n, ASTNodeMap& fromTo,
                               ASTNodeMap& cache, NodeFactory* nf)
{
  const ASTChildren originals = n.GetChildren();

  ASTVec children;
  children.reserve(n.Degree());
  for (const auto& c : originals)
    children.push_back(SubstitutionMap::replace(c, fromTo, cache, nf));

  if (std::equal(children.begin(), children.end(), originals.begin(),
                 originals.end()))
    return n;

  if (BOOLEAN_TYPE == n.GetType())
    return nf->CreateNode(n.GetKind(), children);

  return nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
}

// Both way propagation. Initialising the top to "true".
// The hardest thing to understand is the two cases:
// 1) If we get the fixed bits of a node, without assuming the top node is true,
//    then we can replace that node by its fixed bits.
// 2) But if we assume the top node is true, then get the bits, we need to
// conjoin it.

// NB: This expects that the constructor was called with the same node. Sorry.
ASTNode ConstantBitPropagation::topLevelBothWays(const ASTNode& top,
                                                 bool setTopToTrue,
                                                 bool conjoinToTop)
{
  //assert(mgr->UserFlags.bitConstantProp_flag);
  assert(BOOLEAN_TYPE == top.GetType());

  propagate();
  status = NO_CHANGE;

  // Determine what must always be true.
  ASTNodeMap fromTo = getAllFixed();
  {
    ASTNodeMap::iterator it = fromTo.begin();
    while (it != fromTo.end())
    {
      // I don't think there should be a constant in here ever.
      assert(it->first.GetKind() != SYMBOL);
      it++;
    }
  }

  if (setTopToTrue)
    setNodeToTrue(top);

  propagate();

  // propagate may have stopped with a conflict.
  if (CONFLICT == status)
    return nf->getFalse();

  ASTVec toConjoin;

  // For each entirely fixed node: replace the node by its constant inside
  // "top", and conjoin a fact that pins the node down, so the constraint
  // isn't lost.
  //
  // Every fact is rewritten with every other fact's constant, so the
  // constants discharge into the facts that pin them down. (The top-level
  // conjuncts themselves are always fixed to true; without the rewriting,
  // each conjunct would be erased by the replacement and then restored
  // verbatim by its conjoined fact, putting the input back together.)
  // All the rewriting shares one map and one cache: a fact's own map entry
  // can't erase the fact, because the rewrite starts at the node's
  // children, and a node is never its own descendant.

  struct Fact
  {
    ASTNode node;
    ASTNode constant;
  };
  std::vector<Fact> facts;

  NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it, itEnd;

  // iterates through all the pairs of node->fixedBits.
  for (it = fixedMap->map->begin(), itEnd = fixedMap->map->end(); it != itEnd;
       ++it)
  {
    const FixedBits& bits = *it->second;
    const ASTNode& node = (it->first);

    if (!bits.isTotallyFixed())
      continue;

    // Don't constrain nodes we already know all about.
    if (node.isConstant())
      continue;

    // other nodes will contain the same information (the extract doesn't change
    // the fixings).
    if (BVEXTRACT == node.GetKind() || BVCONCAT == node.GetKind())
      continue;

    // If it is already contained in the fromTo map, then it's one of the
    // values that have fully been determined (previously). Not conjoined.
    if (fromTo.find(node) != fromTo.end())
      continue;

    // Only Boolean and bit-vector nodes can be replaced by a constant here; a
    // floating-point node's FixedBits is a placeholder (see getAllFixed()).
    if (node.GetType() != BOOLEAN_TYPE && node.GetType() != BITVECTOR_TYPE)
      continue;

    ASTNode constNode = bitsToNode(nf, node, bits);

    if (SYMBOL == node.GetKind())
    {
      // Symbols the array-equality procedure depends on refuse substitution;
      // conjoin the derived fixing instead, so the information is kept and the
      // symbol stays in the formula.
      if (!simplifier->UpdateSubstitutionMap(node, constNode) && conjoinToTop)
      {
        if (BOOLEAN_TYPE == node.GetType())
          toConjoin.push_back(bits.getValue(0) ? node
                                               : nf->CreateNode(NOT, node));
        else
          toConjoin.push_back(nf->CreateNode(EQ, node, constNode));
      }
    }
    else if (conjoinToTop && node != top)
    {
      assert(node.GetType() == BOOLEAN_TYPE ||
             ((unsigned)bits.getWidth()) == node.GetValueWidth());

      fromTo.insert(make_pair(node, constNode));
      facts.push_back({node, constNode});
    }
  }

  ASTNodeMap cache;

  for (const auto& fact : facts)
  {
    const ASTNode rebuilt = replaceChildren(fact.node, fromTo, cache, nf);

    ASTNode prop;
    if (BOOLEAN_TYPE == fact.node.GetType())
      prop = (nf->getTrue() == fact.constant) ? rebuilt
                                              : nf->CreateNode(NOT, rebuilt);
    else
      prop = nf->CreateNode(EQ, rebuilt, fact.constant);

    // A fact that rewrites to true is implied by the others.
    if (nf->getTrue() != prop)
      toConjoin.push_back(prop);
  }

  // The fixedMap iteration order isn't defined; sort for determinism.
  SortByExprNum(toConjoin);
  toConjoin.erase(std::unique(toConjoin.begin(), toConjoin.end()),
                  toConjoin.end());

  // Write the constants into the main graph.
  ASTNode result = SubstitutionMap::replace(top, fromTo, cache, nf);

  if (0 != toConjoin.size())
  {
    // It doesn't happen very often. But the "toConjoin" might contain a
    // variable
    // that was added to the substitution map (because the value was determined
    // just now
    // during propagation.
    ASTNode conjunct =
        (1 == toConjoin.size()) ? toConjoin[0] : nf->CreateNode(AND, toConjoin);
    conjunct = simplifier->applySubstitutionMap(conjunct);

    result =
        nf->CreateNode(AND, result, conjunct); // conjoin the new conditions.
  }

  assert(BVTypeCheck(result));
  assert(status != CONFLICT); // conflict should have been seen earlier.
  return result;
}

// add to the work list any nodes that take the result of the "n" node.
void ConstantBitPropagation::scheduleUp(const ASTNode& n)
{
  for (const auto &it : dependents->getDependents(n))
    workList->push(it);
}

void ConstantBitPropagation::scheduleNode(const ASTNode& n)
{
  workList->push(n);
}

bool ConstantBitPropagation::checkAtFixedPoint(const ASTNode& n,
                                               ASTNodeSet& visited)
{
  if (status == CONFLICT)
    return true; // can't do anything.

  if (visited.find(n) != visited.end())
    return true;

  visited.insert(n);

  // get the current for the children.
  vector<FixedBits> childrenFixedBits;
  childrenFixedBits.reserve(n.GetChildren().size());

  // get a copy of the current fixing from the cache.
  for (size_t i = 0, size = n.GetChildren().size(); i < size; ++i)
  {
    childrenFixedBits.push_back(*getCurrentFixedBits(n[i]));
  }

  FixedBits current = *getCurrentFixedBits(n);
  FixedBits newBits = *getUpdatedFixedBits(n);

  assert(FixedBits::equals(newBits, current));

  for (size_t i = 0; i < n.Degree(); i++)
  {
    if (!FixedBits::equals(*getUpdatedFixedBits(n[i]), childrenFixedBits[i]))
    {
      std::cerr << "Not fixed point";
      assert(false);
    }

    checkAtFixedPoint(n[i], visited);
  }
  return true;
}

void ConstantBitPropagation::propagate()
{
  if (CONFLICT == status)
    return;

  assert(NULL != fixedMap);

  while (!workList->isEmpty())
  {
    // get the next node from the worklist.
    const ASTNode& n = workList->pop();

    assert(!n.isConstant());    // shouldn't get into the worklist..
    assert(CONFLICT != status); // should have stopped already.

    // Fetch each FixedBits from the map once per visit; the map lookups
    // dominate the cost of propagation on large problems.
    FixedBits* nBits = getCurrentFixedBits(n);
    int previousTop = nBits->countFixed();

    const unsigned degree = n.GetChildren().size();
    childrenBits.clear();
    previousChildrenFixedCount.clear();

    // get a copy of the current fixing from the cache.
    for (unsigned i = 0; i < degree; i++)
    {
      FixedBits* cb = getCurrentFixedBits(n[i]);
      childrenBits.push_back(cb);
      previousChildrenFixedCount.push_back(cb->countFixed());
    }

    // derive the new ones. (As getUpdatedFixedBits, but reusing the
    // already-fetched FixedBits.)
    if (SYMBOL != n.GetKind())
    {
      assert(status != CONFLICT);
      status = dispatchToTransferFunctions(mgr, n.GetKind(), childrenBits,
                                           *nBits, n, msm);
      assert(((unsigned)nBits->getWidth()) == n.GetValueWidth() ||
             nBits->getWidth() == 1);
    }
    int newCount = nBits->countFixed();

    if (CONFLICT == status)
      return;

    // Not all transfer function update the status. But if they report
    // NO_CHANGE. There really is no change.
    if (status != NO_CHANGE)
    {
      if (newCount != previousTop) // has been a change.
      {
        assert(newCount >= previousTop);
        scheduleUp(n); // schedule everything that depends on n.
      }

      for (unsigned i = 0; i < degree; i++)
      {
        if (childrenBits[i]->countFixed() != previousChildrenFixedCount[i])
        {
          assert(!n[i].isConstant());

          // All the immediate parents of this child need to be
          // rescheduled - except 'n' itself: the transfer function that
          // just ran left 'n' at its fixed point for exactly these child
          // values, so an immediate revisit derives nothing.
          for (const auto& parent : dependents->getDependents(n[i]))
            if (!(parent == n))
              workList->push(parent);

          // Scheduling the child updates all the values that feed into it.
          workList->push(n[i]);
        }
      }
    }
  }
}

FixedBits* ConstantBitPropagation::makeInitialFixedBits(const ASTNode& n)
{
  int bw;
  if (0 == n.GetValueWidth())
  {
    bw = 1;
  }
  else
  {
    bw = n.GetValueWidth();
  }

  FixedBits* output = new FixedBits(bw, (BOOLEAN_TYPE == n.GetType()));

  if (BVCONST == n.GetKind() || BITVECTOR == n.GetKind())
  {
    // the CBV doesn't leak. it is a copy of the cbv inside the node.
    CBV cbv = n.GetBVConst();

    for (unsigned int j = 0; j < n.GetValueWidth(); j++)
    {
      output->setFixed(j, true);
      output->setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
    }
  }
  else if (TRUE == n.GetKind())
  {
    output->setFixed(0, true);
    output->setValue(0, true);
  }
  else if (FALSE == n.GetKind())
  {
    output->setFixed(0, true);
    output->setValue(0, false);
  }

  return output;
}

// No value is in the map yet, so make a new one. The lookup that discovered
// the miss is inlined into getCurrentFixedBits.
FixedBits* ConstantBitPropagation::createFixedBits(const ASTNode& n)
{
  FixedBits* output = makeInitialFixedBits(n);
  fixedMap->map->insert(pair<ASTNode, FixedBits*>(n, output));
  return output;
}

// For the given node, update which bits are fixed.

FixedBits* ConstantBitPropagation::getUpdatedFixedBits(const ASTNode& n)
{
  FixedBits* output = getCurrentFixedBits(n);
  const Kind k = n.GetKind();

  if (n.isConstant())
  {
    assert(output->isTotallyFixed());
    return output;
  }

  if (SYMBOL == k)
    return output; // No transfer functions for these.

  vector<FixedBits*> children;
  const int numberOfChildren = n.GetChildren().size();
  children.reserve(numberOfChildren);

  for (int i = 0; i < numberOfChildren; i++)
  {
    children.push_back(getCurrentFixedBits(n.GetChildren()[i]));
  }

  assert(status != CONFLICT);
  status = dispatchToTransferFunctions(mgr, k, children, *output, n, msm);
  // result = dispatchToMaximallyPrecise(k, children, *output, n,msm);

  assert(((unsigned)output->getWidth()) == n.GetValueWidth() ||
         output->getWidth() == 1);

  return output;
}

Result ConstantBitPropagation::dispatchToTransferFunctions(
    stp::STPMgr* mgr, const Kind k, vector<FixedBits*>& children,
    FixedBits& output, const ASTNode n, MultiplicationStatsMap* msm)
{
  Result result = NO_CHANGE;

  assert(!n.isConstant());

  Result (*transfer)(vector<FixedBits*>&, FixedBits&);

  switch (k)
  {
    case READ:
    case WRITE:
      // do nothing. Seems difficult to track properly.
      return NO_CHANGE;

#define MAPTFN(caseV, FN)                                                      \
  case caseV:                                                                  \
    transfer = FN;                                                             \
    break;

      // Shifting
      MAPTFN(BVLEFTSHIFT, bvLeftShiftBothWays)
      MAPTFN(BVRIGHTSHIFT, bvRightShiftBothWays)
      MAPTFN(BVSRSHIFT, bvArithmeticRightShiftBothWays)

      // Unsigned Comparison.
      MAPTFN(BVLT, bvLessThanBothWays)
      MAPTFN(BVLE, bvLessThanEqualsBothWays)
      MAPTFN(BVGT, bvGreaterThanBothWays)
      MAPTFN(BVGE, bvGreaterThanEqualsBothWays)

      // Signed Comparison.
      MAPTFN(BVSLT, bvSignedLessThanBothWays)
      MAPTFN(BVSGT, bvSignedGreaterThanBothWays)
      MAPTFN(BVSLE, bvSignedLessThanEqualsBothWays)
      MAPTFN(BVSGE, bvSignedGreaterThanEqualsBothWays)

      // Logic.
      MAPTFN(XOR, bvXorBothWays)
      MAPTFN(BVXOR, bvXorBothWays)
      MAPTFN(OR, bvOrBothWays)
      MAPTFN(BVOR, bvOrBothWays)
      MAPTFN(AND, bvAndBothWays)
      MAPTFN(BVAND, bvAndBothWays)
      MAPTFN(IFF, bvEqualsBothWays)
      MAPTFN(EQ, bvEqualsBothWays)
      MAPTFN(IMPLIES, bvImpliesBothWays)
      MAPTFN(NOT, bvNotBothWays)
      MAPTFN(BVNOT, bvNotBothWays)

      // OTHER
      MAPTFN(BVZX, bvZeroExtendBothWays)
      MAPTFN(BVSX, bvSignExtendBothWays)
      MAPTFN(BVUMINUS, bvUnaryMinusBothWays)
      MAPTFN(BVEXTRACT, bvExtractBothWays)
      MAPTFN(BVPLUS, bvAddBothWays)
      MAPTFN(BVSUB, bvSubtractBothWays)
      MAPTFN(ITE, bvITEBothWays)
      MAPTFN(BVCONCAT, bvConcatBothWays)

    case BVMULT: // handled specially later.
    case BVDIV:
    case BVMOD:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
      transfer = NULL;
      break;

    default:
    {
      return NO_CHANGE;
    }
  }
#undef MAPTFN

  // safe approximation to no overflow multiplication.
  if (k == BVMULT)
  {
    MultiplicationStats ms;
    result = bvMultiplyBothWays(children, output, mgr, &ms);
    // bvMultiplyBothWays only fills in ms for two-operand multiplies; a
    // wider node would store empty stats whose NULL column arrays the
    // bit-blaster's getMS() later reads.
    if (CONFLICT != result && children.size() == 2)
      msm->map[n] = ms;
  }
  else if (k == BVDIV)
    result = bvUnsignedDivisionBothWays(children, output, mgr);
  else if (k == BVMOD)
    result = bvUnsignedModulusBothWays(children, output, mgr);
  else if (k == SBVDIV)
    result = bvSignedDivisionBothWays(children, output, mgr);
  else if (k == SBVREM)
    result = bvSignedRemainderBothWays(children, output, mgr);
  else if (k == SBVMOD)
    result = bvSignedModulusBothWays(children, output, mgr);
  else
    result = transfer(children, output);

  return result;
}
}
}

#include "../../AST/AST.h"
#include "FixedBits.h"
#include "../../extlib-constbv/constantbv.h"
#include "../../printer/printers.h"
#include <list>
#include "ConstantBitPropagation.h"
#include "NodeToFixedBitsMap.h"
#include "Dependencies.h"
#include "../../AST/NodeFactory/NodeFactory.h"
#include <map>
#include "WorkList.h"
#include "../../simplifier/simplifier.h"
#include "ConstantBitP_Utility.h"

#ifdef WITHCBITP
  #include "MultiplicationStats.h"

  #include "ConstantBitP_TransferFunctions.h"
  #include "ConstantBitP_MaxPrecision.h"
#endif

using std::endl;
using std::cout;

using namespace BEEV;

/*
 *	Propagates known fixed 0 or 1 bits, as well as TRUE/FALSE values through the formula.
 *
 *  After propagation. All the values that are completely known are conjoined at the top.
 *
 *	Our approach differs from others because the transfer functions are (mostly) optimally precise.
 *
 *	FixedBits stores vectors and booleans both in 1 bit-bitvectors.
 */

/** TODO
 *  * Size the containers appropriately at initialisation.
 *  * Reduce the number of inits() that are done during propagation.
 *  *
 */

namespace simplifier
{
  namespace constantBitP
  {

    Result status; //Whether changes have occured, and whether a conflict (bad) occurs if true is asserted.

    NodeToFixedBitsMap* PrintingHackfixedMap; // Used when debugging.

    FixedBits*
    getUpdatedFixedBits(const BEEV::ASTNode& n, NodeToFixedBitsMap* fixedMap,
        MultiplicationStatsMap * msm = NULL);
    FixedBits*
    getCurrentFixedBits(const ASTNode& n, NodeToFixedBitsMap* fixedMap);

    Result
    dispatchToTransferFunctions(const Kind k, vector<FixedBits*>& children,
        FixedBits& output, const ASTNode n, MultiplicationStatsMap *msm = NULL);
    Result
    dispatchToMaximallyPrecise(const Kind k, vector<FixedBits*>& children,
        FixedBits& output, const ASTNode n);

    void
    propagate(WorkList & workList, const Dependencies & dependents,
        NodeToFixedBitsMap* fixedMap, MultiplicationStatsMap *msm);
    ASTNode
    getGraphAfterFixing(const ASTNode& n);

    const bool debug_cBitProp_messages = false;

    ////////////////////

    void
    ConstantBitPropagation::printNodeWithFixings()
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
          fixedMap->map->begin();

      cerr << "+Nodes with fixings" << endl;

      for (/**/; it != fixedMap->map->end(); it++) // iterates through all the pairs of node->fixedBits.
        {
          cerr << (it->first).GetNodeNum() << " " << *(it->second) << endl;
        }
      cerr << "-Nodes with fixings" << endl;

    }

    // We add the the worklist any node that immediately depends on a constant.
    void
    addToWorklist(const ASTNode& n, WorkList& list, ASTNodeSet& visited)
    {
      if (visited.find(n) != visited.end())
        return;

      visited.insert(n);

      bool alreadyAdded = false;

      for (unsigned i = 0; i < n.GetChildren().size(); i++)
        {
          if (n[i].isConstant() && !alreadyAdded)
            {
              alreadyAdded = true;
              list.push(n);
            }
          addToWorklist(n[i], list, visited);
        }
    }

    // Add to the worklist any node that immediately depends on a constant.
    void
    ConstantBitPropagation::initialiseWorklist(const ASTNode& top)
    {
      ASTNodeSet visited;
      addToWorklist(top, *workList, visited);
    }

    // Used when outputting when debugging.
    // Outputs the fixed bits for a particular node.
    string
    toString(const ASTNode& n)
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
          PrintingHackfixedMap->map->find(n);
      if (it == PrintingHackfixedMap->map->end())
        return "";

      std::stringstream s;
      s << *it->second;
      return s.str();
    }

    // If the bits are totally fixed, then return a new matching ASTNode.
    ASTNode
    bitsToNode(const ASTNode& node, const FixedBits& bits)
    {
      ASTNode result;
      STPMgr & beev = *node.GetSTPMgr();

      assert (bits.isTotallyFixed());
      assert (!node.isConstant()); // Peformance. Shouldn't waste time calling it on constants.

      if (node.GetType() == BOOLEAN_TYPE)
        {
          if (bits.getValue(0))
            {
              result = beev.CreateNode(TRUE);
            }
          else
            {
              result = beev.CreateNode(FALSE);
            }
        }
      else if (node.GetType() == BITVECTOR_TYPE)
        {
          result = beev.CreateBVConst(bits.GetBVConst(), node.GetValueWidth());
        }
      else
        FatalError("sadf234s");

      return result;
    }

    // Put anything that's entirely fixed into a from->to map.
    ASTNodeMap
    getAllFixed(NodeToFixedBitsMap* fixedMap)
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it;

      ASTNodeMap toFrom;

      // iterates through all the pairs of node->fixedBits.
      for (it = fixedMap->map->begin(); it != fixedMap->map->end(); it++)
        {
          const ASTNode& node = (it->first);
          const FixedBits& bits = *it->second;

          // Don't constrain nodes we already know all about.
          if (BVCONST == node.GetKind() || TRUE == node.GetKind() || FALSE
              == node.GetKind())
            continue;

          // other nodes will contain the same information (the extract doesn't change the fixings).
          if (BVEXTRACT == node.GetKind() || BVCONCAT == node.GetKind())
            continue;

          if (bits.isTotallyFixed())
            {
              toFrom.insert(std::make_pair(node, bitsToNode(node, bits)));
            }
        }

      return toFrom;
    }

#ifdef WITHCBITP
    // Get the column counts for multiplication.
    MultiplicationStatsMap* ConstantBitPropagation::getMultiplicationStats()
      {
        assert(multiplicationStats != NULL);
        return multiplicationStats;
      }
#endif

    bool
    noNewInfo(const Kind& k)
    {
      if (k == BVCONCAT || k == BVEXTRACT)
        return true;

      return false;
    }

    // Builds and returns the fixed Map. No writing in of values.
    // Note the caller is responsibile for deleting the fixedBitMap.
    // It omits values that aren't interesting like constants, extracts and concats.
    NodeToFixedBitsMap*
    ConstantBitPropagation::getFixedMap(const ASTNode & top)
    {
      assert (NULL == fixedMap);
      //	assert (NULL == multiplicationStats);
      fixedMap = new NodeToFixedBitsMap(1000); // better to use the function that returns the number of nodes.. whatever that is.

      //multiplicationStats= new MultiplicationStatsMap();

      workList = new WorkList();
      initialiseWorklist(top);
      status = NO_CHANGE;

      FixedBits & topFB = *getCurrentFixedBits(top, fixedMap);
      topFB.setFixed(0, true);
      topFB.setValue(0, true);
      workList->push(top);

      dependents = new Dependencies(top); // List of the parents of a node.

      //propagate(*workList, *dependents, fixedMap, multiplicationStats);
      propagate(*workList, *dependents, fixedMap, NULL);

      // remove constants, and things with nothing fixed.
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
          fixedMap->map->begin();
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it_end =
          fixedMap->map->end();
      while (it != it_end)
        {
          // No constants, nothing completely unfixed.
          if ((it->first).isConstant() || (it->second)->countFixed() == 0 /*|| noNewInfo((it->first).GetKind() )*/)
            {
              delete it->second;
              // making this a reference causes reading from freed memory.
              const ASTNode n = it->first;
              it++;
              fixedMap->map->erase(n);
            }
          else
            it++;
        }
      return fixedMap;
    }

    // Both way propagation. Initialising the top to "true".
    ASTNode
    ConstantBitPropagation::topLevelBothWays(const ASTNode& top)
    {
      if (!top.GetSTPMgr()->UserFlags.bitConstantProp_flag)
        return top;

      assert (BOOLEAN_TYPE == top.GetType());
      assert (NULL == fixedMap);
      //assert (NULL == multiplicationStats);

      //Stopwatch watch;

      fixedMap = new NodeToFixedBitsMap(1000); // better to use the function that returns the number of nodes.. whatever that is.
      //multiplicationStats = new MultiplicationStatsMap();

      workList = new WorkList();
      initialiseWorklist(top);

      Dependencies * dependents = new Dependencies(top); // List of the parents of a node.
      status = NO_CHANGE;
      //propagate(*workList, *dependents, fixedMap,multiplicationStats);
      propagate(*workList, *dependents, fixedMap, NULL);

      //Determine what must always be true.
      ASTNodeMap fromTo = getAllFixed(fixedMap);

      if (debug_cBitProp_messages)
        {
          cout << "Number removed by bottom UP" << fromTo.size();
        }

      status = NO_CHANGE;

      FixedBits & topFB = *getCurrentFixedBits(top, fixedMap);
      topFB.setFixed(0, true);
      topFB.setValue(0, true);
      workList->push(top);

      if (debug_cBitProp_messages)
        {
          cout << "starting propagation" << endl;
          printNodeWithFixings();
          cout << "Initial Tree:" << endl;
          //top.NFASTPrint(0, 10, 10);
          cerr << top;
        }

      //propagate(*workList, *dependents, fixedMap, multiplicationStats);
      propagate(*workList, *dependents, fixedMap, NULL);

      if (debug_cBitProp_messages)
        {
          cerr << "ended propagation" << endl;
          printNodeWithFixings();
        }

      ASTNode result;
      ASTVec toAssert;
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it;
      STPMgr & beev = *top.GetSTPMgr();
      ASTNodeMap cache;

      ASTVec nodes;
      ASTVec replaceWith;
      ASTVec assertions;

      // propagate may have stopped with a conflict.
      if (CONFLICT == status)
        {
          result = top.GetSTPMgr()->CreateNode(FALSE);
          goto end;
        }

      // go through the fixedBits. If a node is entirely fixed.
      // "and" it onto the top. Creates redundancy. Check that the
      // node doesn't already depend on "top" directly.

      for (it = fixedMap->map->begin(); it != fixedMap->map->end(); it++) // iterates through all the pairs of node->fixedBits.

        {
          const FixedBits& bits = *it->second;

          if (!bits.isTotallyFixed())
            continue;

          const ASTNode& node = (it->first);

          // Don't constrain nodes we already know all about.
          if (BVCONST == node.GetKind() || TRUE == node.GetKind() || FALSE
              == node.GetKind())
            continue;

          // other nodes will contain the same information (the extract doesn't change the fixings).
          if (BVEXTRACT == node.GetKind() || BVCONCAT == node.GetKind())
            continue;

          // toAssign: conjoin it with the top level.
          // toReplace: replace all references to it (except the one conjoined to the top) with this.
          ASTNode propositionToAssert;
          ASTNode constantToReplaceWith;
          // skip the assigning and replacing.
          bool doAssign = true;

            {
              // If it is already contained in the fromTo map, then it's one of the values
              // that have fully been determined (previously). No need to to conjoin it to the top.

              if (fromTo.find(node) != fromTo.end())
                continue;

              if (node.GetType() == BOOLEAN_TYPE)
                {
                  if (SYMBOL == node.GetKind())
                    {
                      constantToReplaceWith
                          = bits.getValue(0) ? beev.CreateNode(TRUE)
                              : beev.CreateNode(FALSE);
                      bool r = simplifier->UpdateSolverMap(node,
                          constantToReplaceWith);
                      assert(r);
                      doAssign = false;

                    }
                  else if (bits.getValue(0))
                    {
                      propositionToAssert = node;
                      constantToReplaceWith = beev.CreateNode(TRUE);
                    }
                  else
                    {
                      propositionToAssert = nf->CreateNode(NOT, node);
                      constantToReplaceWith = beev.CreateNode(FALSE);
                    }
                }
              else if (node.GetType() == BITVECTOR_TYPE)
                {
                  ASTNode newV = beev.CreateBVConst(bits.GetBVConst(),
                      node.GetValueWidth());
                  assert(((unsigned)bits.getWidth()) == node.GetValueWidth());
                  if (SYMBOL == node.GetKind())
                    {
                      constantToReplaceWith = newV;
                      bool r = simplifier->UpdateSubstitutionMap(node,
                          constantToReplaceWith);
                      assert(r);
                      doAssign = false;
                    }
                  else
                    {
                      propositionToAssert = nf->CreateNode(EQ, node, newV);
                      constantToReplaceWith = newV;
                    }
                }
              else
                FatalError("sadf234s");
            }

          if (doAssign && top != propositionToAssert
              && !dependents->nodeDependsOn(top, propositionToAssert))
            {
              assert(!constantToReplaceWith.IsNull());
              assert(constantToReplaceWith.isConstant());
              assert(propositionToAssert.GetType() == BOOLEAN_TYPE);
              assert(node.GetValueWidth() == constantToReplaceWith.GetValueWidth());

              nodes.push_back(node);
              replaceWith.push_back(constantToReplaceWith);
              toAssert.push_back(propositionToAssert);
            }
        }

        {
          // fromTo already contains the replacements we can make with adding any additional assertions.
          for (unsigned i = 0; i < nodes.size(); i++)
            fromTo.insert(make_pair(nodes[i], replaceWith[i]));

          // Write the constants into the main graph.
          ASTNodeMap cache2;
          result = SubstitutionMap::replace(top, fromTo, cache2);
        }

      /*
       * This code attempts to simplify the additional assertions that get added into the problem.
       * Unfortunately it breaks some examples.
       */

#if 0
      assert(top.GetType() == BOOLEAN_TYPE);

      if (debug_cBitProp_messages)
        {
          PrintingHackfixedMap = fixedMap;
          printer::GDL_Print(cout, top, toString);
        }

        {
          assert(nodes.size() == replaceWith.size());
          assert(nodes.size() == toAssert.size());

          // load into fromTo2 the replacements that require assertions to be added.
          ASTNodeMap fromTo2;
          for (int i =0; i < nodes.size();i++)
            {
              fromTo2.insert(make_pair(nodes[i], replaceWith[i]));
            }

          // fromTo contains the replacements we can make with adding any additional assertions.
          ASTNodeMap::const_iterator it;
          for (it = fromTo.begin(); it != fromTo.end(); it++)
          fromTo2.insert(*it);

          // Write the constants into the main graph.
          ASTNodeMap cache2;
          result = sm->replace(top,fromTo2, cache2);
        }

        {
          ASTNodeMap n;
          // no extra assertions required.
          ASTNodeMap::const_iterator it;
          for (it = fromTo.begin(); it != fromTo.end(); it++)
          n.insert(*it);

          vector<pair<ASTNode,ASTNode > > nodeToConst;

          for (int i =0; i < nodes.size();i++)
            {
              nodeToConst.push_back(make_pair(nodes[i], replaceWith[i]));
              n.insert(nodeToConst.back());
            }

          // We want to apply all the replacements except one to every node.
          // if "n" must equal five, we don't want to apply the replacement rule n=5 to it.
          for (int i =0; i < nodes.size();i++)
            {
              n.erase(nodes[i]);
              ASTNodeMap cache2;
              toAssert[i] = sm->replace(toAssert[i], n, cache2);
              assert(toAssert[i].GetType() == BOOLEAN_TYPE);
              n.insert(nodeToConst[i]);
            }
          assert(toAssert.size() == nodes.size());
        }
#endif

      // Some of these assertions are unnecessary.
      if (0 != toAssert.size())
        {
          result = nf->CreateNode(AND, result, toAssert); // conjoin the new conditions.
          assert(BVTypeCheck(result));
        }

      end:

      //multiplicationStats->map.clear();
      //delete multiplicationStats;

      fixedMap->clear();
      delete fixedMap;
      fixedMap = NULL;

      delete dependents;
      return result;
    }

    void
    notHandled(const Kind& k)
    {
      if (READ != k && WRITE != k)
      //if (debug_cBitProp_messages)

        {
          cout << "!" << k << endl;
        }
    }

    // add to the work list any nodes that take the result of the "n" node.


    void
    scheduleUp(const ASTNode& n, WorkList & workList,
        const Dependencies & dependents)
    {
      const set<ASTNode>* toAdd = dependents.getDependents(n);
      set<ASTNode>::iterator it = toAdd->begin();
      while (it != toAdd->end())
        {
          workList.push(*it);
          it++;
        }
    }

    void
    ConstantBitPropagation::scheduleUp(const ASTNode& n)
    {
      const set<ASTNode>* toAdd = dependents->getDependents(n);
      set<ASTNode>::iterator it = toAdd->begin();
      while (it != toAdd->end())
        {
          workList->push(*it);
          it++;
        }
    }

    void
    ConstantBitPropagation::scheduleDown(const ASTNode& n)
    {
      for (int i = 0; i < n.Degree(); i++)
        workList->push(n[i]);
    }

    void
    ConstantBitPropagation::schedule(const ASTNode& n)
    {
      workList->push(n);
    }

    void
    ConstantBitPropagation::checkAtFixedPoint(const ASTNode& n,
        ASTNodeSet & visited)
    {
      if (status == CONFLICT)
        return; // can't do anything.


      if (visited.find(n) != visited.end())
        return;

      visited.insert(n);

      // get the current for the children.
      vector<FixedBits> childrenFixedBits;
      childrenFixedBits.reserve(n.GetChildren().size());

      // get a copy of the current fixing from the cache.
      for (unsigned i = 0; i < n.GetChildren().size(); i++)
        {
          childrenFixedBits.push_back(*getCurrentFixedBits(n[i], fixedMap));
        }
      FixedBits current = *getCurrentFixedBits(n, fixedMap);

      //FixedBits newBits = *getUpdatedFixedBits(n, fixedMap,multiplicationStats);
      FixedBits newBits = *getUpdatedFixedBits(n, fixedMap, NULL);

      if (!FixedBits::equals(newBits, current)) // has been a change.
        {
          cerr << "Not fixed point";
          assert(false);
        }

      for (int i = 0; i < n.Degree(); i++)
        {
          if (!FixedBits::equals(*getCurrentFixedBits(n[i], fixedMap),
              childrenFixedBits[i]))
            {
              cerr << "Not fixed point";
              assert(false);
            }

          checkAtFixedPoint(n[i], visited);
        }
    }

    void
    propagate(WorkList & workList, const Dependencies & dependents,
        NodeToFixedBitsMap* fixedMap, MultiplicationStatsMap * msm)
    {
      assert(NULL != fixedMap);

      while (!workList.isEmpty())
        {
          // get the next node from the worklist.
          const ASTNode& n = workList.pop();

          if (n.isConstant())
            continue; // no propagation for these.

          if (debug_cBitProp_messages)
            {
              cerr << "working on" << n.GetNodeNum() << endl;
            }
          assert (CONFLICT != status);

          // get a copy of the current fixing from the cache.
          FixedBits current = *getCurrentFixedBits(n, fixedMap);

          // get the current for the children.
          vector<FixedBits> childrenFixedBits;
          childrenFixedBits.reserve(n.GetChildren().size());

          // get a copy of the current fixing from the cache.
          for (unsigned i = 0; i < n.GetChildren().size(); i++)
            {
              childrenFixedBits.push_back(*getCurrentFixedBits(n[i], fixedMap));
            }

          // derive the new ones.
          FixedBits newBits = *getUpdatedFixedBits(n, fixedMap, msm);

          if (CONFLICT == status)
            return;

          // Not all transfer function update the status. But if they report NO_CHANGE. There really is no change.
          if (status != NO_CHANGE)
            {
              assert(FixedBits::updateOK(current,newBits));

              if (!FixedBits::equals(newBits, current)) // has been a change.

                {
                  scheduleUp(n, workList, dependents); // schedule everything that depends on n.
                  if (debug_cBitProp_messages)
                    {
                      cerr << "Changed " << n.GetNodeNum() << "from:"
                          << current << "to:" << newBits << endl;
                    }
                }

              for (unsigned i = 0; i < n.GetChildren().size(); i++)
                {
                  assert(FixedBits::updateOK(childrenFixedBits[i], *getCurrentFixedBits(n[i],fixedMap)) );

                  if (!FixedBits::equals(*getCurrentFixedBits(n[i], fixedMap),
                      childrenFixedBits[i]))
                    {
                      if (debug_cBitProp_messages)
                        {
                          cerr << "Changed " << n[i].GetNodeNum() << " from:"
                              << childrenFixedBits[i] << "to:"
                              << *getCurrentFixedBits(n[i], fixedMap) << endl;
                        }

                      // All the immediate parents of this child need to be rescheduled.
                      scheduleUp(n[i], workList, dependents);

                      // Scheduling the child updates all the values that feed into it.
                      workList.push(n[i]);
                    }
                }
            }
        }
    }

    void
    ConstantBitPropagation::prop()
    {
      if (CONFLICT == status)
        return;
      //propagate(*workList,*dependents, fixedMap, multiplicationStats);
      propagate(*workList, *dependents, fixedMap, NULL);
    }

    // get the current value from the map. If no value is in the map. Make a new value.
    FixedBits*
    getCurrentFixedBits(const ASTNode& n, NodeToFixedBitsMap* fixedMap)
    {
      if (NULL != fixedMap)
        {
          NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
              fixedMap->map->find(n);
          if (it != fixedMap->map->end())
            {
              return it->second;
            }
        }

      int bw;
      if (0 == n.GetValueWidth())
        {
          bw = 1;
        }
      else
        {
          bw = n.GetValueWidth();
        }

      FixedBits* output = new FixedBits(bw, (0 == n.GetValueWidth()));

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

      if (NULL != fixedMap)
        {
          fixedMap->map->insert(pair<ASTNode, FixedBits*> (n, output));
        }

      return output;
    }

    // For the given node, update which bits are fixed.
    FixedBits*
    getUpdatedFixedBits(const ASTNode& n, NodeToFixedBitsMap* fixedMap,
        MultiplicationStatsMap *msm)
    {
      // If it's upwards only, then any fixedBits that have been calculated prior are still good.
      //if (NULL != fixedMap)
      //{
      //	NodeToFixedBitsMap::iterator it = fixedMap->find(n);
      //	if (it != fixedMap->end())
      //	{
      //		return it->second;
      //	}
      //}

      FixedBits & output = *getCurrentFixedBits(n, fixedMap);
      const Kind k = n.GetKind();

      if (SYMBOL == k || n.isConstant())
        return &output; // No transfer functions for these.

      vector<FixedBits*> children;
      const int numberOfChildren = n.GetChildren().size();
      children.reserve(numberOfChildren);

      for (int i = 0; i < numberOfChildren; i++)
        {
          children.push_back(getCurrentFixedBits(n.GetChildren()[i], fixedMap));
        }

      assert(status != CONFLICT);
      status = dispatchToTransferFunctions(k, children, output, n, msm);
      //result = dispatchToMaximallyPrecise(k, children, output, n);

      assert(((unsigned)output.getWidth()) == n.GetValueWidth() || output.getWidth() ==1);

      return &output;
    }

    Result
    dispatchToTransferFunctions(const Kind k, vector<FixedBits*>& children,
        FixedBits& output, const ASTNode n, MultiplicationStatsMap * msm)
    {

#ifdef WITHCBITP
      Result result = NO_CHANGE;

      Result(*transfer)(vector<FixedBits*>&, FixedBits&);

      switch (k)
        {
          case TRUE:
          output.setFixed(0, true);
          output.setValue(0, true);
          return result;

          case FALSE:
          output.setFixed(0, true);
          output.setValue(0, false);
          return result;

          case READ:
          case WRITE:
          // do nothing. Seems difficult to track properly.
          return NO_CHANGE;
          break;

#define MAPTFN(caseV, FN) case caseV: transfer = FN; break;

          // Shifting
          MAPTFN(BVLEFTSHIFT, bvLeftShiftBothWays)
          MAPTFN(BVRIGHTSHIFT, bvRightShiftBothWays)
          MAPTFN(BVSRSHIFT, bvArithmeticRightShiftBothWays)

          // Unsigned Comparison.
          MAPTFN(BVLT,bvLessThanBothWays)
          MAPTFN(BVLE,bvLessThanEqualsBothWays)
          MAPTFN(BVGT, bvGreaterThanBothWays)
          MAPTFN(BVGE, bvGreaterThanEqualsBothWays)

          // Signed Comparison.
          MAPTFN(BVSLT, bvSignedLessThanBothWays)
          MAPTFN(BVSGT,bvSignedGreaterThanBothWays)
          MAPTFN(BVSLE, bvSignedLessThanEqualsBothWays)
          MAPTFN(BVSGE, bvSignedGreaterThanEqualsBothWays)

          // Logic.
          MAPTFN(XOR,bvXorBothWays)
          MAPTFN(BVXOR, bvXorBothWays)
          MAPTFN(OR, bvOrBothWays)
          MAPTFN(BVOR, bvOrBothWays)
          MAPTFN(AND,bvAndBothWays)
          MAPTFN(BVAND,bvAndBothWays)
          MAPTFN(IMPLIES,bvImpliesBothWays)

          // OTHER
          MAPTFN(BVZX, bvZeroExtendBothWays)
          MAPTFN(BVSX, bvSignExtendBothWays)
          MAPTFN(BVUMINUS,bvUnaryMinusBothWays)
          MAPTFN(BVEXTRACT,bvExtractBothWays)
          MAPTFN(EQ, bvEqualsBothWays)
          MAPTFN(IFF, bvEqualsBothWays)
          MAPTFN(BVPLUS, bvAddBothWays)
          MAPTFN(BVSUB, bvSubtractBothWays)
          MAPTFN(NOT,bvNotBothWays)
          MAPTFN(BVNEG, bvNotBothWays)
          MAPTFN(ITE,bvITEBothWays)
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
              //	if (k == BVSRSHIFT)
              //return dispatchToMaximallyPrecise(k, children, output, n);

              notHandled(k);
              return NO_CHANGE;
              //return dispatchToMaximallyPrecise(k, children, output, n);
            }
        }
#undef MAPTFN

      // safe approximation to no overflow multiplication.
      if (k == BVMULT)
        {
          //MultiplicationStats ms;
          //result = bvMultiplyBothWays(children, output, n.GetSTPMgr(),&ms);
          result = bvMultiplyBothWays(children, output, n.GetSTPMgr());
          //		if (CONFLICT != result)
          //			msm->map[n] = ms;
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else if (k == BVDIV)
        {
          result = bvUnsignedDivisionBothWays(children, output, n.GetSTPMgr());
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else if (k == BVMOD)
        {
          result = bvUnsignedModulusBothWays(children, output, n.GetSTPMgr());
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else if (k == SBVDIV)
        {
          result = bvSignedDivisionBothWays(children, output, n.GetSTPMgr());
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else if (k == SBVREM)
        {
          result = bvSignedRemainderBothWays(children, output, n.GetSTPMgr());
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else if (k == SBVMOD)
        {
          result = bvSignedModulusBothWays(children, output, n.GetSTPMgr());
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }
      else
      result = transfer(children, output);

      return result;
#else
      return NO_CHANGE;
#endif

    }
    // compare the new fixed to the old fixed. Is it OK??
    Result
    isDifferent(const FixedBits& n, const FixedBits& o)
    {
      Result result = NO_CHANGE;
      assert(n.getWidth() == o.getWidth());
      for (int i = 0; i < n.getWidth(); i++)
        {
          if (n.isFixed(i) && o.isFixed(i))
            {
              if (n.getValue(i) != o.getValue(i))
                {
                  return CONFLICT;
                }
            }
          else if (o.isFixed(i) && !n.isFixed(i))
            {
              FatalError(LOCATION "values can't become unfixed..");
            }
          else if (n.isFixed(i) && !o.isFixed(i))
            {
              result = CHANGED;
            }
        }
      return result;
    }

#if 0
  Result dispatchToMaximallyPrecise(const Kind k, vector<FixedBits*>& children,
      FixedBits& output, const ASTNode n)
    {
      Signature signature;
      signature.kind = k;

      vector<FixedBits> childrenCopy;

      for (int i = 0; i < (int) children.size(); i++)
      childrenCopy.push_back(*(children[i]));
      FixedBits outputCopy(output);

      if (k == BVMULT)
        {
          // We've got some of multiply already implemented. So help it out by getting some done first.
          Result r = bvMultiplyBothWays(children, output, n.GetSTPMgr());
          if (CONFLICT == r)
          return CONFLICT;
        }

      bool bad = maxPrecision(children, output, k, n.GetSTPMgr());

      if (bad)
      return CONFLICT;

      if (!FixedBits::equals(outputCopy, output))
      return CHANGED;

      for (int i = 0; i < (int) children.size(); i++)
        {
          if (!FixedBits::equals(*(children[i]), childrenCopy[i]))
          return CHANGED;
        }

      return NO_CHANGE;
    }
#endif

  }

// Code to conjoin a partially specified node to the top.
#if 0
else if (bits.countFixed() > 0)
  {
    // Some are fixed. We only fix the contiguous leading and trailing fixed.

    assert(node.GetType() == BITVECTOR_TYPE);

    // Get the inside indexes of the leading and trailing sections.
    unsigned trailing = 0;
    while (bits.isFixed(trailing))
    trailing++;

    unsigned leading = bits.getWidth() - 1;
    while (bits.isFixed(leading))
    leading--;

    assert(leading >= trailing); // prior case handles totally fixed.

    //The fixed bits might not be at either end as we need them to be.
    if (trailing == 0 && (unsigned) bits.getWidth() - 1 == leading)
    continue;

    ASTNode trailingConst, leadingConst;
    bool trailingB = false;
    bool leadingB = false;
    if (trailing > 0)
      {
        trailingConst = beev.CreateBVConst(bits.GetBVConst(trailing - 1, 0), trailing);
        ASTNode extract = beev.CreateTerm(BVEXTRACT, trailing, node, beev.CreateBVConst(32,trailing-1),beev.CreateBVConst(32,0));
        assert(beev.BVTypeCheck(extract));
        toAssign = beev.CreateNode(EQ, extract, trailingConst);
        trailingB = true;
      }

    if (leading < (unsigned) bits.getWidth() - 1)
      {
        leadingConst = beev.CreateBVConst(bits.GetBVConst(bits.getWidth() - 1, leading + 1), bits.getWidth() - 1 - leading);
        ASTNode extract = beev.CreateTerm(BVEXTRACT, bits.getWidth() - leading -1, node, beev.CreateBVConst(32,bits.getWidth() -1),beev.CreateBVConst(32,leading+1));
        assert(beev.BVTypeCheck(extract));
        ASTNode equals = beev.CreateNode(EQ, extract, leadingConst);
        leadingB = true;
        if(!trailingB)
        toAssign = equals;
        else
        toAssign = beev.CreateNode(AND, equals, toAssign);
      }

    assert(trailingB || leadingB);

    if (node.GetKind() == SYMBOL)
      {
        toAssign = beev.NewVar(leading - trailing + 1);
        if (trailingB)
        toAssign = beev.CreateTerm(BVCONCAT, leading + 1, toAssign, trailingConst);
        if (leadingB)
        toAssign = beev.CreateTerm(BVCONCAT, bits.getWidth(), leadingConst, toAssign);

        assert(beev.BVTypeCheck(toAssign));
        bool r = beev.UpdateSolverMap(node, toAssign);
        assert(r);
        doAssign = false;
      }
    else
      {
        toReplace= beev.CreateTerm(BVEXTRACT, leading - trailing + 1, node, beev.CreateBVConst(32, leading), beev.CreateBVConst(32, trailing));
        assert(beev.BVTypeCheck(toAssign));
        if (trailingB)
        toReplace = beev.CreateTerm(BVCONCAT, leading + 1, toReplace, trailingConst);
        if (leadingB)
        toReplace = beev.CreateTerm(BVCONCAT, bits.getWidth(), leadingConst, toReplace);
      }

  }
#endif

#if 0
// whenever it's fixed replace it by a new constant.
// cycles in the graph would cause an infinite loop.
ASTNode ConstantBitPropagation::topLevelGetGraphAfterFixing(const ASTNode& n)
  {
    if (BEEV::disable_bitConstantProp_flag)
    return n;

    Stopwatch watch;

    assert(NULL == fixedMap);

    fixedMap = new NodeToFixedBitsMap(100);

    //n.SMTLIB_Print(cerr, 0);
    status = NO_CHANGE;

    //printer::SMTLIB_Print(cerr, n,0);

    // We start by running from the bottom to the top.
    ASTNode result = getGraphAfterFixing(n);

    //if (BOTH_WAYS == direction)

      {
        //setTopToTrue(result);

        while (true) // loop until fixed point.

          {
            cerr << "|";

            ASTNode old = result;
            result = getGraphAfterFixing(result);

            if (CONFLICT == status)
              {
                cerr << "Status bad";
                break;
              }

            if (result == old)
            break; // continue until nothing changes
          }
      }

    //printer::SMTLIB_Print(cerr, result);

    delete fixedMap;
    fixedMap = NULL;

    watch.stop();

    if (CONFLICT == status)
    return n.GetSTPMgr().CreateNode(FALSE);
    else
    return result;
  }

// Simplifies any parts of the tree that can be fixed to a constant.
ASTNode ConstantBitPropagation::getGraphAfterFixing(const ASTNode& n)
  {
    assert(NULL != fixedMap);

    if (BVCONST == n.GetKind())
    return n;

    ASTNode result;

    if (getUpdatedFixedBits(n,fixedMap)->isTotallyFixed())
      {
        BEEV::CBV cbv = getUpdatedFixedBits(n,fixedMap)->GetBVConst();

        if (BOOLEAN_TYPE == n.GetType())
          {
            if (1 == toInt(cbv))
            result = n.GetSTPMgr().CreateNode(TRUE);
            else
            result = n.GetSTPMgr().CreateNode(FALSE);

            CONSTANTBV::BitVector_Destroy(cbv);
          }
        else
          {
            // runs the deleter on cbv.
            result = n.GetSTPMgr().CreateBVConst(cbv, n.GetValueWidth());
          }
      }
    else
      {
        ASTVec changed;
        const int numberOfChildren = n.GetChildren().size();
        changed.reserve(numberOfChildren);

        for (int i = 0; i < numberOfChildren; i++)
          {
            ASTNode then = getGraphAfterFixing(n.GetChildren()[i]);
            changed.push_back(then);
          }

        bool changeFound = false;
        for (int i = 0; i < numberOfChildren; i++)
          {
            if (changed[i] != n.GetChildren()[i])
              {
                n.GetSTPMgr().BVTypeCheck(changed[i]);
                changeFound = true;
              }
          }

        if (!changeFound)
        result = n;
        else
          {
            if (BOOLEAN_TYPE == n.GetType())
            result = n.GetSTPMgr().CreateNode(n.GetKind(), changed);
            else if (BITVECTOR_TYPE == n.GetType())
            result = n.GetSTPMgr().CreateTerm(n.GetKind(), n.GetValueWidth(), changed);
            else if (ARRAY_TYPE == n.GetType())
              {
                result = n.GetBeevMgr().CreateTerm(n.GetKind(), n.GetValueWidth(), changed);
                result.SetIndexWidth(n.GetIndexWidth());
              }
            else
            FatalError("never get to here:");
          }
      }

    return result;
  }

#endif
}


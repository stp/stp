// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef BBNodeManagerAIG_H_
#define BBNodeManagerAIG_H_

#include "BBNodeAIG.h"

// cnf_short omits some stuff that doesn't compile in g++ that we don't need anyway.
#include "../../extlib-abc/aig.h"
#include "../../extlib-abc/cnf_short.h"
#include "../../extlib-abc/dar.h"
#include "../ToSATBase.h"

typedef Cnf_Dat_t_ CNFData;
typedef Aig_Obj_t AIGNode;

namespace BEEV
{
class ASTNode;
class STPMgr; // we ignore this anyway.

extern vector<BBNodeAIG> _empty_BBNodeAIGVec;

// Creates AIG nodes with ABC and wraps them in BBNodeAIG's.
class BBNodeManagerAIG
{
        Aig_Man_t *aigMgr;

        // Map from symbols to their AIG nodes.
        typedef map<ASTNode, vector<BBNodeAIG> > SymbolToBBNode;
        SymbolToBBNode symbolToBBNode;

        // AIGs can only take two parameters. This makes a log_2 height
        // tower of varadic inputs.
        Aig_Obj_t * makeTower(Aig_Obj_t * (*t)(Aig_Man_t *, Aig_Obj_t *,
                        Aig_Obj_t *), vector<BBNodeAIG>& children)
        {
                deque<Aig_Obj_t*> names;

                for (unsigned i = 0; i < children.size(); i++)
                        names.push_back(children[i].n);

                while (names.size() > 2)
                {
                        Aig_Obj_t* a = names.front();
                        names.pop_front();

                        Aig_Obj_t* b = names.front();
                        names.pop_front();

                        Aig_Obj_t* n = t(aigMgr, a, b);
                        names.push_back(n);
                }

                // last two now.
                assert(names.size() == 2);

                Aig_Obj_t* a = names.front();
                names.pop_front();

                Aig_Obj_t* b = names.front();
                names.pop_front();

                return t(aigMgr, a, b);
        }

public:

        BBNodeManagerAIG(STPMgr*& _stp)
        {
                aigMgr = Aig_ManStart(0);
                // fancier strashing.
                aigMgr->fAddStrash = 1;
        }

        ~BBNodeManagerAIG()
        {
                Aig_ManStop(aigMgr);
        }

        BBNodeAIG getTrue()
        {
                return BBNodeAIG((aigMgr->pConst1));
        }

        BBNodeAIG getFalse()
        {
                return BBNodeAIG(Aig_Not(aigMgr->pConst1));
        }

        void
        toCNF(BBNodeAIG& top, Cnf_Dat_t*& cnfData, ToSATBase::ASTNodeToVar& nodeToVar)
        {
          assert(cnfData == NULL);

          Aig_Man_t *aigMgr;

          Aig_ObjCreatePo(aigMgr, top.n);
          Aig_ManCleanup( aigMgr); // remove nodes not connected to the PO.
          Aig_ManCheck(aigMgr); // check that AIG looks ok.

          assert(Aig_ManPoNum(aigMgr) == 1);

          //cerr << "SAFDASDF";

          // copied from darScript.c: Aig_Man_t * Dar_ManRewriteDefault( Aig_Man_t * pAig )
          /*
           Dar_LibStart();
           Aig_Man_t * pTemp1, *pTemp2;
           Dar_RwrPar_t Pars, * pPars = &Pars;
           Dar_ManDefaultRwrParams( pPars );
           Dar_ManRewrite( aigMgr, pPars );
           Aig_ManCheck(aigMgr); // check that AIG looks ok.
           Dar_LibStop();
           */

          //assert(Aig_ManPoNum(aigMgr) == 1);

          //Aig_NtkReassignIds( aigMgr );
          // fix the levels
          //Aig_ManUpdateLevel( aigMgr, Aig_ManPo(aigMgr,0));
          //Aig_ManVerifyLevel( aigMgr );


          // assert(Aig_ManPoNum(aigMgr) == 1);

          //Dar_RwrPar_t  pPars;
          //Dar_ManDefaultRwrParams( &pPars );
          //Dar_ManRewrite( aigMgr, &pPars );


          // Cnf_Derive seems more advanced, but gives assertion errors sometimes.
          cnfData = Cnf_Derive(aigMgr, 0);

          BBNodeManagerAIG::SymbolToBBNode::const_iterator it;

          assert(nodeToVar.size() ==0);

          for (it = symbolToBBNode.begin(); it != symbolToBBNode.end(); it++)
            {
              const ASTNode& n = it->first;
              const vector<BBNodeAIG> &b = it->second;
              if (nodeToVar.find(n) == nodeToVar.end())
                {
                  const int width = (n.GetType() == BOOLEAN_TYPE) ? 1: n.GetValueWidth();
                  vector<unsigned> v(width, ~((unsigned) 0));
                  nodeToVar.insert(make_pair(n, v));
                }

              vector<unsigned>& v = nodeToVar[n];
              for (unsigned i = 0; i < b.size(); i++)
                {
                  v[i] = cnfData->pVarNums[b[i].n->Id];
                }
            }
          assert(cnfData != NULL);
        }

        // The same symbol always needs to return the same AIG node,
        // if it doesn't you will get the wrong answer.
        BBNodeAIG CreateSymbol(const ASTNode& n, unsigned i)
        {
                assert(n.GetKind() == SYMBOL);

                // booleans have width 0.
                const unsigned width = std::max((unsigned)1, n.GetValueWidth());

                SymbolToBBNode::iterator it;
                it = symbolToBBNode.find(n);
                if (symbolToBBNode.end() == it)
                {
                        symbolToBBNode[n] = vector<BBNodeAIG> (width);
                        it = symbolToBBNode.find(n);
                }

                assert(it->second.size() == width);
                assert(i < width);

                if (!it->second[i].IsNull())
                        return it->second[i];

                it->second[i] = BBNodeAIG(Aig_ObjCreatePi(aigMgr));

                return it->second[i];
        }

        BBNodeAIG CreateNode(Kind kind, vector<BBNodeAIG>& children)
        {
                Aig_Obj_t * pNode;

                switch (kind)
                {
                case AND:
                        assert (children.size() != 0);
                        if (children.size() == 1)
                                pNode = children[0].n;
                        else if (children.size() == 2)
                                pNode = Aig_And(aigMgr, children[0].n, children[1].n);
                        else
                                pNode = makeTower(Aig_And, children);
                        break;

                case OR:
                        if (children.size() == 2)
                                pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
                        else
                                pNode = makeTower(Aig_Or, children);
                        break;
                case NAND:
                        if (children.size() == 2)
                                pNode = Aig_And(aigMgr, children[0].n, children[1].n);
                        else
                                pNode = makeTower(Aig_And, children);
                        pNode = Aig_Not(pNode);
                        break;
                case NOT:
                        assert(children.size() ==1);
                        pNode = Aig_Not(children[0].n);
                        break;
                case NOR:
                        if (children.size() == 2)
                                pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
                        else
                                pNode = makeTower(Aig_Or, children);
                        break;
                        pNode = Aig_Not(pNode);
                        break;
                case XOR:
                        assert(children.size() ==2);
                        pNode = Aig_Exor(aigMgr, children[0].n, children[1].n);
                        break;
                case IFF:
                        assert(children.size() ==2);
                        pNode = Aig_Exor(aigMgr, children[0].n, children[1].n);
                        pNode = Aig_Not(pNode);
                        break;
                case IMPLIES:
                        assert(children.size() ==2);
                        pNode = Aig_Or(aigMgr, Aig_Not(children[0].n), children[1].n);
                        break;
                case ITE:
                        assert(children.size() ==3);
                        pNode
                                        = Aig_Mux(aigMgr, children[0].n, children[1].n,
                                                        children[2].n);
                        break;

                default:
                        cerr << "Not handled::!!" << _kind_names[kind];
                        FatalError("Never here");
                }
                return BBNodeAIG(pNode);
        }

        BBNodeAIG CreateNode(Kind kind, const BBNodeAIG& child0,
                        const vector<BBNodeAIG> & back_children = _empty_BBNodeAIGVec)
        {
                vector<BBNodeAIG> front_children;
                front_children.reserve(1 + back_children.size());
                front_children.push_back(child0);
                front_children.insert(front_children.end(), back_children.begin(),
                                back_children.end());
                return CreateNode(kind, front_children);
        }

        BBNodeAIG CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
                        const vector<BBNodeAIG> & back_children = _empty_BBNodeAIGVec)
        {
                vector<BBNodeAIG> front_children;
                front_children.reserve(2 + back_children.size());
                front_children.push_back(child0);
                front_children.push_back(child1);
                front_children.insert(front_children.end(), back_children.begin(),
                                back_children.end());
                return CreateNode(kind, front_children);

        }

        BBNodeAIG CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
                        const BBNodeAIG& child2, const vector<BBNodeAIG> & back_children =
                            _empty_BBNodeAIGVec)
        {
                vector<BBNodeAIG> front_children;
                front_children.reserve(3 + back_children.size());
                front_children.push_back(child0);
                front_children.push_back(child1);
                front_children.push_back(child2);
                front_children.insert(front_children.end(), back_children.begin(),
                                back_children.end());
                return CreateNode(kind, front_children);
        }
};

}
;

#endif /* BBNodeManagerAIG_H_ */

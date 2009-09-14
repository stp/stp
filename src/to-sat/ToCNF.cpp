/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "../AST/AST.h"
#include "../simplifier/bvsolver.h"
#include "../sat/sat.h"

namespace BEEV
{

  class CNFMgr
  {

  public:

    //########################################
    //########################################
    // constructor

    CNFMgr(BeevMgr *bmgr)
    {
      bm = bmgr;
    }

    //########################################
    //########################################
    // destructor

    ~CNFMgr()
    {
      ASTNodeToASTNodePtrMap::const_iterator it1 = store.begin();
      for (; it1 != store.end(); it1++)
        {
          delete it1->second;
        }

      store.clear();

    }

    //########################################
    //########################################
    // top-level conversion function

    BeevMgr::ClauseList* convertToCNF(const ASTNode& varphi)
    {
      varphi.GetBeevMgr().runTimes.start(RunTimes::CNFConversion);
      scanFormula(varphi, true);
      ASTNode dummy_true_var = bm->CreateSymbol("*TrueDummy*");
      BeevMgr::ClauseList* defs = SINGLETON(dummy_true_var);
      convertFormulaToCNF(varphi, defs);
      BeevMgr::ClauseList* top = info[varphi]->clausespos;
      defs->insert(defs->begin() + 1, top->begin(), top->end());

      cleanup(varphi);
      varphi.GetBeevMgr().runTimes.stop(RunTimes::CNFConversion);
      return defs;
    }

    void DELETE(BeevMgr::ClauseList* varphi)
    {
      BeevMgr::ClauseList::const_iterator it = varphi->begin();
      for (; it != varphi->end(); it++)
        {
          delete *it;
        }

      delete varphi;
    }

  private:

    //########################################
    //########################################
    // data types

    // for the meaning of control bits, see "utilities for contol bits".
    typedef struct
    {
      int control;
      BeevMgr::ClauseList* clausespos;
      union
      {
        BeevMgr::ClauseList* clausesneg;
        ASTNode* termforcnf;
      };
    } CNFInfo;

    typedef hash_map<ASTNode, CNFInfo*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTNodeToCNFInfoMap;

    typedef hash_map<ASTNode, ASTNode*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTNodeToASTNodePtrMap;

    //########################################
    //########################################
    // this is the data

    BeevMgr *bm;
    ASTNodeToCNFInfoMap info;
    ASTNodeToASTNodePtrMap store;

    //########################################
    //########################################
    // utility predicates

    bool isAtom(const ASTNode& varphi)
    {
      bool result;

      Kind k = varphi.GetKind();
      switch (k)
        {
        case TRUE:
          {
            result = true;
            break;
          }
        case FALSE:
          {
            result = true;
            break;
          }
        case SYMBOL:
          {
            result = true;
            break;
          }
        case BVCONST:
          {
            result = true;
            break;
          }
        default:
          {
            result = false;
            break;
          }
        }

      return result;
    }

    bool isPred(const ASTNode& varphi)
    {
      bool result;

      Kind k = varphi.GetKind();
      switch (k)
        {
        case BVLT:
          {
            result = true;
            break;
          }
        case BVLE:
          {
            result = true;
            break;
          }
        case BVGT:
          {
            result = true;
            break;
          }
        case BVGE:
          {
            result = true;
            break;
          }
        case BVSLT:
          {
            result = true;
            break;
          }
        case BVSLE:
          {
            result = true;
            break;
          }
        case BVSGT:
          {
            result = true;
            break;
          }
        case BVSGE:
          {
            result = true;
            break;
          }
        case EQ:
          {
            result = true;
            break;
          }
        default:
          {
            result = false;
            break;
          }
        }

      return result;
    }

    bool isITE(const ASTNode& varphi)
    {
      bool result;

      Kind k = varphi.GetKind();
      switch (k)
        {
        case ITE:
          {
            result = true;
            break;
          }
        default:
          {
            result = false;
            break;
          }
        }

      return result;
    }

    bool onChildDoPos(const ASTNode& varphi, unsigned int idx)
    {
      bool result = true;

      Kind k = varphi.GetKind();
      switch (k)
        {
        case NOT:
          {
            result = false;
            break;
          }
        case NAND:
          {
            result = false;
            break;
          }
        case NOR:
          {
            result = false;
            break;
          }
        case IMPLIES:
          {
            if (idx == 0)
              {
                result = false;
              }
            break;
          }
        default:
          {
            break;
          }
        }

      return result;
    }

    bool onChildDoNeg(const ASTNode& varphi, unsigned int idx)
    {
      bool result = false;

      Kind k = varphi.GetKind();
      switch (k)
        {
        case NOT:
          {
            result = true;
            break;
          }
        case NAND:
          {
            result = true;
            break;
          }
        case NOR:
          {
            result = true;
            break;
          }
        case XOR:
          {
            result = true;
            break;
          }
        case IFF:
          {
            result = true;
            break;
          }
        case IMPLIES:
          {
            if (idx == 0)
              {
                result = true;
              }
            break;
          }
        case ITE:
          {
            if (idx == 0)
              {
                result = true;
              }
            break;
          }
        default:
          {
            break;
          }
        }

      return result;
    }

    //########################################
    //########################################
    //utilities for control bits.

    void initializeCNFInfo(CNFInfo& x)
    {
      x.control = 0;
      x.clausespos = NULL;
      x.clausesneg = NULL;
    }

    void incrementSharesPos(CNFInfo& x)
    {
      x.control += ((x.control & 3) < 2) ? 1 : 0;
    }

    int sharesPos(CNFInfo& x)
    {
      return (x.control & 3);
    }

    void incrementSharesNeg(CNFInfo& x)
    {
      x.control += ((x.control & 12) < 8) ? 4 : 0;
    }

    int sharesNeg(CNFInfo& x)
    {
      return ((x.control & 12) >> 2);
    }

    void setControlBit(CNFInfo& x, unsigned int idx)
    {
      x.control |= (1 << idx);
    }

    bool getControlBit(CNFInfo& x, unsigned int idx)
    {
      bool result = false;

      if (x.control & (1 << idx))
        {

          result = true;
        }

      return result;
    }

    void setIsTerm(CNFInfo& x)
    {
      setControlBit(x, 4);
    }

    bool isTerm(CNFInfo& x)
    {
      return getControlBit(x, 4);
    }

    void setDoRenamePos(CNFInfo& x)
    {
      setControlBit(x, 5);
    }

    bool doRenamePos(CNFInfo& x)
    {
      return getControlBit(x, 5);
    }

    void setWasRenamedPos(CNFInfo& x)
    {
      setControlBit(x, 6);
    }

    bool wasRenamedPos(CNFInfo& x)
    {
      return getControlBit(x, 6);
    }

    void setDoRenameNeg(CNFInfo& x)
    {
      setControlBit(x, 7);
    }

    bool doRenameNeg(CNFInfo& x)
    {
      return getControlBit(x, 7);
    }

    void setWasRenamedNeg(CNFInfo& x)
    {
      setControlBit(x, 8);
    }

    bool wasRenamedNeg(CNFInfo& x)
    {
      return getControlBit(x, 8);
    }

    void setDoSibRenamingPos(CNFInfo& x)
    {
      setControlBit(x, 9);
    }

    bool doSibRenamingPos(CNFInfo& x)
    {
      return getControlBit(x, 9);
    }

    void setDoSibRenamingNeg(CNFInfo& x)
    {
      setControlBit(x, 10);
    }

    bool doSibRenamingNeg(CNFInfo& x)
    {
      return getControlBit(x, 10);
    }

    void setWasVisited(CNFInfo& x)
    {
      setControlBit(x, 11);
    }

    bool wasVisited(CNFInfo& x)
    {
      return getControlBit(x, 11);
    }

    //########################################
    //########################################
    //utilities for clause sets


    BeevMgr::ClauseList* COPY(const BeevMgr::ClauseList& varphi)
    {
      BeevMgr::ClauseList* psi = new BeevMgr::ClauseList();

      BeevMgr::ClauseList::const_iterator it = varphi.begin();
      for (; it != varphi.end(); it++)
        {
          psi->push_back(new vector<const ASTNode*> (**it));
        }

      return psi;
    }

    BeevMgr::ClauseList* SINGLETON(const ASTNode& varphi)
    {
      ASTNode* copy = ASTNodeToASTNodePtr(varphi);

      BeevMgr::ClausePtr clause = new vector<const ASTNode*> ();
      clause->push_back(copy);

      BeevMgr::ClauseList* psi = new BeevMgr::ClauseList();
      psi->push_back(clause);
      return psi;
    }

    BeevMgr::ClauseList* UNION(const BeevMgr::ClauseList& varphi1, const BeevMgr::ClauseList& varphi2)
    {

      BeevMgr::ClauseList* psi1 = COPY(varphi1);
      BeevMgr::ClauseList* psi2 = COPY(varphi2);
      psi1->insert(psi1->end(), psi2->begin(), psi2->end());
      delete psi2;

      return psi1;

    }

    void INPLACE_UNION(BeevMgr::ClauseList* varphi1, const BeevMgr::ClauseList& varphi2)
    {

      BeevMgr::ClauseList* psi2 = COPY(varphi2);
      varphi1->insert(varphi1->end(), psi2->begin(), psi2->end());
      delete psi2;
    }

    void NOCOPY_INPLACE_UNION(BeevMgr::ClauseList* varphi1, BeevMgr::ClauseList* varphi2)
    {

      varphi1->insert(varphi1->end(), varphi2->begin(), varphi2->end());
      delete varphi2;
    }

    BeevMgr::ClauseList* PRODUCT(const BeevMgr::ClauseList& varphi1, const BeevMgr::ClauseList& varphi2)
    {

      BeevMgr::ClauseList* psi = new BeevMgr::ClauseList();
      psi->reserve(varphi1.size() * varphi2.size());

      BeevMgr::ClauseList::const_iterator it1 = varphi1.begin();
      for (; it1 != varphi1.end(); it1++)
        {
          BeevMgr::ClausePtr clause1 = *it1;
          BeevMgr::ClauseList::const_iterator it2 = varphi2.begin();
          for (; it2 != varphi2.end(); it2++)
            {
              BeevMgr::ClausePtr clause2 = *it2;
              BeevMgr::ClausePtr clause = new vector<const ASTNode*> ();
              clause->reserve(clause1->size() + clause2->size());
              clause->insert(clause->end(), clause1->begin(), clause1->end());
              clause->insert(clause->end(), clause2->begin(), clause2->end());
              psi->push_back(clause);
            }
        }

      return psi;
    }

    //########################################
    //########################################
    //prep. for cnf conversion

    void scanFormula(const ASTNode& varphi, bool isPos)
    {

      CNFInfo* x;

      //########################################
      // step 1, get the info associated with this node
      //########################################

      if (info.find(varphi) == info.end())
        {
          x = new CNFInfo();
          initializeCNFInfo(*x);
          info[varphi] = x;
        }
      else
        {
          x = info[varphi];
        }

      //########################################
      // step 2, we only need to know if shares >= 2
      //########################################

      if (isPos && sharesPos(*x) == 2)
        {
          return;
        }

      if (!isPos && sharesNeg(*x) == 2)
        {
          return;
        }

      //########################################
      // step 3, set appropriate information fields
      //########################################

      if (isPos)
        {
          incrementSharesPos(*x);
        }

      if (!isPos)
        {
          incrementSharesNeg(*x);
        }

      //########################################
      // step 4, recurse over children
      //########################################

      if (isAtom(varphi))
        {
          return;
        }
      else if (isPred(varphi))
        {
          for (unsigned int i = 0; i < varphi.GetChildren().size(); i++)
            {
              scanTerm(varphi[i]);
            }
        }
      else
        {
          for (unsigned int i = 0; i < varphi.GetChildren().size(); i++)
            {
              if (onChildDoPos(varphi, i))
                {
                  scanFormula(varphi[i], isPos);
                }
              if (onChildDoNeg(varphi, i))
                {
                  scanFormula(varphi[i], !isPos);
                }
            }
        }

    }

    void scanTerm(const ASTNode& varphi)
    {

      CNFInfo* x;

      //########################################
      // step 1, get the info associated with this node
      //########################################

      if (info.find(varphi) == info.end())
        {
          x = new CNFInfo();
          initializeCNFInfo(*x);
          info[varphi] = x;
        }
      else
        {
          x = info[varphi];
        }

      //########################################
      // step 2, need two hits because of term ITEs.
      //########################################

      if (sharesPos(*x) == 2)
        {
          return;
        }

      //########################################
      // step 3, set appropriate data fields, always rename
      // term ITEs
      //########################################

      incrementSharesPos(*x);
      setIsTerm(*x);

      //########################################
      // step 4, recurse over children
      //########################################

      if (isAtom(varphi))
        {
          return;
        }
      else if (isITE(varphi))
        {
          scanFormula(varphi[0], true);
          scanFormula(varphi[0], false);
          scanTerm(varphi[1]);
          scanTerm(varphi[2]);
        }
      else
        {
          for (unsigned int i = 0; i < varphi.GetChildren().size(); i++)
            {
              scanTerm(varphi[i]);
            }
        }
    }

    //########################################
    //########################################
    // main cnf conversion function

    void convertFormulaToCNF(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      CNFInfo* x = info[varphi];

      //########################################
      // divert to special case if term (word-level cnf)

      if (isTerm(*x))
        {
          convertTermForCNF(varphi, defs);
          setWasVisited(*x);
          return;
        }

      //########################################
      // do work

      if (sharesPos(*x) > 0 && !wasVisited(*x))
        {
          convertFormulaToCNFPosCases(varphi, defs);
        }

      if (x->clausespos != NULL && x->clausespos->size() > 1)
        {
          if (doSibRenamingPos(*x) || sharesPos(*x) > 1)
            {
              doRenamingPos(varphi, defs);
            }
        }

      if (sharesNeg(*x) > 0 && !wasVisited(*x))
        {
          convertFormulaToCNFNegCases(varphi, defs);
        }

      if (x->clausesneg != NULL && x->clausesneg->size() > 1)
        {
          if (doSibRenamingNeg(*x) || sharesNeg(*x) > 1)
            {
              doRenamingNeg(varphi, defs);
            }
        }

      //########################################
      //mark that we've already done the hard work

      setWasVisited(*x);
    }

    void convertTermForCNF(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      CNFInfo* x = info[varphi];

      //########################################
      // step 1, done if we've already visited
      //########################################

      if (x->termforcnf != NULL)
        {
          return;
        }

      //########################################
      // step 2, ITE's always get renamed
      //########################################

      if (isITE(varphi))
        {
          x->termforcnf = doRenameITE(varphi, defs);
          reduceMemoryFootprintPos(varphi[0]);
          reduceMemoryFootprintNeg(varphi[0]);

        }
      else if (isAtom(varphi))
        {
          x->termforcnf = ASTNodeToASTNodePtr(varphi);
        }
      else
        {

          ASTVec psis;
          ASTVec::const_iterator it = varphi.GetChildren().begin();
          for (; it != varphi.GetChildren().end(); it++)
            {
              convertTermForCNF(*it, defs);
              psis.push_back(*(info[*it]->termforcnf));
            }

          ASTNode psi = bm->CreateNode(varphi.GetKind(), psis);
          psi.SetValueWidth(varphi.GetValueWidth());
          psi.SetIndexWidth(varphi.GetIndexWidth());
          x->termforcnf = ASTNodeToASTNodePtr(psi);
        }
    }

    //########################################
    //########################################
    // functions for renaming nodes during cnf conversion

    ASTNode* doRenameITE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      ASTNode psi;

      //########################################
      // step 1, old "RepLit" code
      //########################################

      ostringstream oss;
      oss << "cnf" << "{" << varphi.GetNodeNum() << "}";
      psi = bm->CreateSymbol(oss.str().c_str());

      //########################################
      // step 2, set widths appropriately
      //########################################

      psi.SetValueWidth(varphi.GetValueWidth());
      psi.SetIndexWidth(varphi.GetIndexWidth());

      //########################################
      // step 3, recurse over children
      //########################################

      convertFormulaToCNF(varphi[0], defs);
      convertTermForCNF(varphi[1], defs);
      ASTNode t1 = *(info[varphi[1]]->termforcnf);
      convertTermForCNF(varphi[2], defs);
      ASTNode t2 = *(info[varphi[2]]->termforcnf);

      //########################################
      // step 4, add def clauses
      //########################################

      BeevMgr::ClauseList* cl1 = SINGLETON(bm->CreateNode(EQ, psi, t1));
      BeevMgr::ClauseList* cl2 = PRODUCT(*(info[varphi[0]]->clausesneg), *cl1);
      DELETE(cl1);
      defs->insert(defs->end(), cl2->begin(), cl2->end());

      BeevMgr::ClauseList* cl3 = SINGLETON(bm->CreateNode(EQ, psi, t2));
      BeevMgr::ClauseList* cl4 = PRODUCT(*(info[varphi[0]]->clausespos), *cl3);
      DELETE(cl3);
      defs->insert(defs->end(), cl4->begin(), cl4->end());

      return ASTNodeToASTNodePtr(psi);
    }

    void doRenamingPos(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      CNFInfo* x = info[varphi];

      //########################################
      // step 1, calc new variable
      //########################################

      ostringstream oss;
      oss << "cnf" << "{" << varphi.GetNodeNum() << "}";
      ASTNode psi = bm->CreateSymbol(oss.str().c_str());

      //########################################
      // step 2, add defs
      //########################################

      BeevMgr::ClauseList* cl1;
      cl1 = SINGLETON(bm->CreateNode(NOT, psi));
      BeevMgr::ClauseList* cl2 = PRODUCT(*(info[varphi]->clausespos), *cl1);
      defs->insert(defs->end(), cl2->begin(), cl2->end());
      DELETE(info[varphi]->clausespos);
      DELETE(cl1);
      delete cl2;

      //########################################
      // step 3, update info[varphi]
      //########################################

      x->clausespos = SINGLETON(psi);
      setWasRenamedPos(*x);
    }

    void doRenamingNeg(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      CNFInfo* x = info[varphi];

      //########################################
      // step 2, calc new variable
      //########################################

      ostringstream oss;
      oss << "cnf" << "{" << varphi.GetNodeNum() << "}";
      ASTNode psi = bm->CreateSymbol(oss.str().c_str());

      //########################################
      // step 3, add defs
      //########################################

      BeevMgr::ClauseList* cl1;
      cl1 = SINGLETON(psi);
      BeevMgr::ClauseList* cl2 = PRODUCT(*(info[varphi]->clausesneg), *cl1);
      defs->insert(defs->end(), cl2->begin(), cl2->end());
      DELETE(info[varphi]->clausesneg);
      DELETE(cl1);
      delete cl2;

      //########################################
      // step 4, update info[varphi]
      //########################################

      x->clausesneg = SINGLETON(bm->CreateNode(NOT, psi));
      setWasRenamedNeg(*x);

    }

    //########################################
    //########################################
    //main switch for individual cnf conversion cases

    void convertFormulaToCNFPosCases(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      if (isPred(varphi))
        {
          convertFormulaToCNFPosPred(varphi, defs);
          return;
        }

      Kind k = varphi.GetKind();
      switch (k)
        {
        case FALSE:
          {
            convertFormulaToCNFPosFALSE(varphi, defs);
            break;
          }
        case TRUE:
          {
            convertFormulaToCNFPosTRUE(varphi, defs);
            break;
          }
        case BVGETBIT:
          {
            convertFormulaToCNFPosBVGETBIT(varphi, defs);
            break;
          }
        case SYMBOL:
          {
            convertFormulaToCNFPosSYMBOL(varphi, defs);
            break;
          }
        case NOT:
          {
            convertFormulaToCNFPosNOT(varphi, defs);
            break;
          }
        case AND:
          {
            convertFormulaToCNFPosAND(varphi, defs);
            break;
          }
        case NAND:
          {
            convertFormulaToCNFPosNAND(varphi, defs);
            break;
          }
        case OR:
          {
            convertFormulaToCNFPosOR(varphi, defs);
            break;
          }
        case NOR:
          {
            convertFormulaToCNFPosNOR(varphi, defs);
            break;
          }
        case XOR:
          {
            convertFormulaToCNFPosXOR(varphi, defs);
            break;
          }
        case IMPLIES:
          {
            convertFormulaToCNFPosIMPLIES(varphi, defs);
            break;
          }
        case ITE:
          {
            convertFormulaToCNFPosITE(varphi, defs);
            break;
          }
        default:
          {
            fprintf(stderr, "convertFormulaToCNFPosCases: doesn't handle kind %d\n", k);
            FatalError("");
          }
        }
    }

    void convertFormulaToCNFNegCases(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      if (isPred(varphi))
        {
          convertFormulaToCNFNegPred(varphi, defs);
          return;
        }

      Kind k = varphi.GetKind();
      switch (k)
        {
        case FALSE:
          {
            convertFormulaToCNFNegFALSE(varphi, defs);
            break;
          }
        case TRUE:
          {
            convertFormulaToCNFNegTRUE(varphi, defs);
            break;
          }
        case BVGETBIT:
          {
            convertFormulaToCNFNegBVGETBIT(varphi, defs);
            break;
          }
        case SYMBOL:
          {
            convertFormulaToCNFNegSYMBOL(varphi, defs);
            break;
          }
        case NOT:
          {
            convertFormulaToCNFNegNOT(varphi, defs);
            break;
          }
        case AND:
          {
            convertFormulaToCNFNegAND(varphi, defs);
            break;
          }
        case NAND:
          {
            convertFormulaToCNFNegNAND(varphi, defs);
            break;
          }
        case OR:
          {
            convertFormulaToCNFNegOR(varphi, defs);
            break;
          }
        case NOR:
          {
            convertFormulaToCNFNegNOR(varphi, defs);
            break;
          }
        case XOR:
          {
            convertFormulaToCNFNegXOR(varphi, defs);
            break;
          }
        case IMPLIES:
          {
            convertFormulaToCNFNegIMPLIES(varphi, defs);
            break;
          }
        case ITE:
          {
            convertFormulaToCNFNegITE(varphi, defs);
            break;
          }
        default:
          {
            fprintf(stderr, "convertFormulaToCNFNegCases: doesn't handle kind %d\n", k);
            FatalError("");
          }
        }
    }

    //########################################
    //########################################
    // individual cnf conversion cases

    void convertFormulaToCNFPosPred(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      ASTVec psis;

      ASTVec::const_iterator it = varphi.GetChildren().begin();
      for (; it != varphi.GetChildren().end(); it++)
        {
          convertTermForCNF(*it, defs);
          psis.push_back(*(info[*it]->termforcnf));
        }

      info[varphi]->clausespos = SINGLETON(bm->CreateNode(varphi.GetKind(), psis));
    }

    void convertFormulaToCNFPosFALSE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTNode dummy_false_var = bm->CreateNode(NOT, bm->CreateSymbol("*TrueDummy*"));
      info[varphi]->clausespos = SINGLETON(dummy_false_var);
    }

    void convertFormulaToCNFPosTRUE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTNode dummy_true_var = bm->CreateSymbol("*TrueDummy*");
      info[varphi]->clausespos = SINGLETON(dummy_true_var);
    }

    void convertFormulaToCNFPosBVGETBIT(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      info[varphi]->clausespos = SINGLETON(varphi);
    }

    void convertFormulaToCNFPosSYMBOL(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      info[varphi]->clausespos = SINGLETON(varphi);
    }

    void convertFormulaToCNFPosNOT(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      convertFormulaToCNF(varphi[0], defs);
      info[varphi]->clausespos = COPY(*(info[varphi[0]]->clausesneg));
      reduceMemoryFootprintNeg(varphi[0]);
    }

    void convertFormulaToCNFPosAND(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (pos) AND ~> UNION
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      BeevMgr::ClauseList* psi = COPY(*(info[*it]->clausespos));
      for (it++; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs);
          INPLACE_UNION(psi, *(info[*it]->clausespos));
          reduceMemoryFootprintPos(*it);
        }

      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFPosNAND(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      bool renamesibs = false;
      BeevMgr::ClauseList* clauses;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* oldpsi;

      //****************************************
      // (pos) NAND ~> PRODUCT NOT
      //****************************************

      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      clauses = info[*it]->clausesneg;
      if (clauses->size() > 1)
        {
          renamesibs = true;
        }
      psi = COPY(*clauses);
      reduceMemoryFootprintNeg(*it);

      for (it++; it != varphi.GetChildren().end(); it++)
        {
          if (renamesibs)
            {
              setDoSibRenamingNeg(*(info[*it]));
            }
          convertFormulaToCNF(*it, defs);
          clauses = info[*it]->clausesneg;
          if (clauses->size() > 1)
            {
              renamesibs = true;
            }
          oldpsi = psi;
          psi = PRODUCT(*psi, *clauses);
          reduceMemoryFootprintNeg(*it);
          DELETE(oldpsi);
        }

      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFPosOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      bool renamesibs = false;
      BeevMgr::ClauseList* clauses;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* oldpsi;

      //****************************************
      // (pos) OR ~> PRODUCT
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      clauses = info[*it]->clausespos;
      if (clauses->size() > 1)
        {
          renamesibs = true;
        }
      psi = COPY(*clauses);
      reduceMemoryFootprintPos(*it);

      for (it++; it != varphi.GetChildren().end(); it++)
        {
          if (renamesibs)
            {
              setDoSibRenamingPos(*(info[*it]));
            }
          convertFormulaToCNF(*it, defs);
          clauses = info[*it]->clausespos;
          if (clauses->size() > 1)
            {
              renamesibs = true;
            }
          oldpsi = psi;
          psi = PRODUCT(*psi, *clauses);
          reduceMemoryFootprintPos(*it);
          DELETE(oldpsi);
        }

      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFPosNOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (pos) NOR ~> UNION NOT
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      BeevMgr::ClauseList* psi = COPY(*(info[*it]->clausesneg));
      reduceMemoryFootprintNeg(*it);
      for (it++; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs);
          INPLACE_UNION(psi, *(info[*it]->clausesneg));
          reduceMemoryFootprintNeg(*it);
        }

      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFPosIMPLIES(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (pos) IMPLIES ~> PRODUCT NOT [0] ; [1]
      //****************************************
      CNFInfo* x0 = info[varphi[0]];
      CNFInfo* x1 = info[varphi[1]];
      convertFormulaToCNF(varphi[0], defs);
      if (x0->clausesneg->size() > 1)
        {
          setDoSibRenamingPos(*x1);
        }
      convertFormulaToCNF(varphi[1], defs);
      BeevMgr::ClauseList* psi = PRODUCT(*(x0->clausesneg), *(x1->clausespos));
      reduceMemoryFootprintNeg(varphi[0]);
      reduceMemoryFootprintPos(varphi[1]);
      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFPosITE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (pos) ITE ~> UNION (PRODUCT NOT [0] ; [1])
      //  ; (PRODUCT [0] ; [2])
      //****************************************
      CNFInfo* x0 = info[varphi[0]];
      CNFInfo* x1 = info[varphi[1]];
      CNFInfo* x2 = info[varphi[2]];
      convertFormulaToCNF(varphi[0], defs);
      if (x0->clausesneg->size() > 1)
        {
          setDoSibRenamingPos(*x1);
        }
      convertFormulaToCNF(varphi[1], defs);
      if (x0->clausespos->size() > 1)
        {
          setDoSibRenamingPos(*x2);
        }
      convertFormulaToCNF(varphi[2], defs);
      BeevMgr::ClauseList* psi1 = PRODUCT(*(x0->clausesneg), *(x1->clausespos));
      BeevMgr::ClauseList* psi2 = PRODUCT(*(x0->clausespos), *(x2->clausespos));
      NOCOPY_INPLACE_UNION(psi1, psi2);
      reduceMemoryFootprintNeg(varphi[0]);
      reduceMemoryFootprintPos(varphi[1]);
      reduceMemoryFootprintPos(varphi[0]);
      reduceMemoryFootprintPos(varphi[2]);

      info[varphi]->clausespos = psi1;
    }

    void convertFormulaToCNFPosXOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      for (; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs); // make pos and neg clause sets
        }
      BeevMgr::ClauseList* psi = convertFormulaToCNFPosXORAux(varphi, 0, defs);
      info[varphi]->clausespos = psi;
      ASTVec::const_iterator it2 = varphi.GetChildren().begin();
      for (; it2 != varphi.GetChildren().end(); it2++){
        reduceMemoryFootprintPos(*it2);
        reduceMemoryFootprintNeg(*it2);
      }
    }

    BeevMgr::ClauseList* convertFormulaToCNFPosXORAux(const ASTNode& varphi, unsigned int idx, BeevMgr::ClauseList* defs)
    {

      bool renamesibs;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* psi1;
      BeevMgr::ClauseList* psi2;

      if (idx == varphi.GetChildren().size() - 2)
        {
          //****************************************
          // (pos) XOR ~> UNION
          //    (PRODUCT       [idx]   ;     [idx+1])
          //  ; (PRODUCT NOT   [idx]   ; NOT [idx+1])
          //****************************************
          renamesibs = (info[varphi[idx]]->clausespos)->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingPos(*info[varphi[idx + 1]]);
            }
          renamesibs = (info[varphi[idx]]->clausesneg)->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingNeg(*info[varphi[idx + 1]]);
            }

          psi1 = PRODUCT(*(info[varphi[idx]]->clausespos), *(info[varphi[idx + 1]]->clausespos));
          psi2 = PRODUCT(*(info[varphi[idx]]->clausesneg), *(info[varphi[idx + 1]]->clausesneg));
          NOCOPY_INPLACE_UNION(psi1, psi2);

          psi = psi1;
        }
      else
        {
          //****************************************
          // (pos) XOR ~> UNION
          //    (PRODUCT       [idx] ; XOR      [idx+1..])
          //  ; (PRODUCT NOT   [idx] ; NOT XOR  [idx+1..])
          //****************************************
          BeevMgr::ClauseList* theta1;
          theta1 = convertFormulaToCNFPosXORAux(varphi, idx + 1, defs);
          renamesibs = theta1->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingPos(*info[varphi[idx]]);
            }
          BeevMgr::ClauseList* theta2;
          theta2 = convertFormulaToCNFNegXORAux(varphi, idx + 1, defs);
          renamesibs = theta2->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingNeg(*info[varphi[idx]]);
            }

          psi1 = PRODUCT(*(info[varphi[idx]]->clausespos), *theta1);
          psi2 = PRODUCT(*(info[varphi[idx]]->clausesneg), *theta2);
          DELETE(theta1);
          DELETE(theta2);
          NOCOPY_INPLACE_UNION(psi1, psi2);

          psi = psi1;
        }

      return psi;
    }

    void convertFormulaToCNFNegPred(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {

      ASTVec psis;

      ASTVec::const_iterator it = varphi.GetChildren().begin();
      for (; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs);
          psis.push_back(*(info[*it]->termforcnf));
        }

      info[varphi]->clausesneg = SINGLETON(bm->CreateNode(NOT, bm->CreateNode(varphi.GetKind(), psis)));
    }

    void convertFormulaToCNFNegFALSE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTNode dummy_true_var = bm->CreateSymbol("*TrueDummy*");
      info[varphi]->clausesneg = SINGLETON(dummy_true_var);
    }

    void convertFormulaToCNFNegTRUE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTNode dummy_false_var = bm->CreateNode(NOT, bm->CreateSymbol("*TrueDummy*"));
      info[varphi]->clausesneg = SINGLETON(dummy_false_var);
    }

    void convertFormulaToCNFNegBVGETBIT(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      BeevMgr::ClauseList* psi = SINGLETON(bm->CreateNode(NOT, varphi));
      info[varphi]->clausesneg = psi;
    }

    void convertFormulaToCNFNegSYMBOL(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      info[varphi]->clausesneg = SINGLETON(bm->CreateNode(NOT, varphi));
    }

    void convertFormulaToCNFNegNOT(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      convertFormulaToCNF(varphi[0], defs);
      info[varphi]->clausesneg = COPY(*(info[varphi[0]]->clausespos));
      reduceMemoryFootprintPos(varphi[0]);
    }

    void convertFormulaToCNFNegAND(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      bool renamesibs = false;
      BeevMgr::ClauseList* clauses;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* oldpsi;

      //****************************************
      // (neg) AND ~> PRODUCT NOT
      //****************************************

      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      clauses = info[*it]->clausesneg;
      if (clauses->size() > 1)
        {
          renamesibs = true;
        }
      psi = COPY(*clauses);
      reduceMemoryFootprintNeg(*it);

      for (it++; it != varphi.GetChildren().end(); it++)
        {
          if (renamesibs)
            {
              setDoSibRenamingNeg(*(info[*it]));
            }
          convertFormulaToCNF(*it, defs);
          clauses = info[*it]->clausesneg;
          if (clauses->size() > 1)
            {
              renamesibs = true;
            }
          oldpsi = psi;
          psi = PRODUCT(*psi, *clauses);
          reduceMemoryFootprintNeg(*it);
          DELETE(oldpsi);
        }

      info[varphi]->clausesneg = psi;
    }

    void convertFormulaToCNFNegNAND(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (neg) NAND ~> UNION
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      BeevMgr::ClauseList* psi = COPY(*(info[*it]->clausespos));
      reduceMemoryFootprintPos(*it);
      for (it++; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs);
          INPLACE_UNION(psi, *(info[*it]->clausespos));
          reduceMemoryFootprintPos(*it);
        }

      info[varphi]->clausespos = psi;
    }

    void convertFormulaToCNFNegOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (neg) OR ~> UNION NOT
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      BeevMgr::ClauseList* psi = COPY(*(info[*it]->clausesneg));
      reduceMemoryFootprintNeg(*it);
      for (it++; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs);
          INPLACE_UNION(psi, *(info[*it]->clausesneg));
          reduceMemoryFootprintNeg(*it);
        }

      info[varphi]->clausesneg = psi;
    }

    void convertFormulaToCNFNegNOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      bool renamesibs = false;
      BeevMgr::ClauseList* clauses;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* oldpsi;

      //****************************************
      // (neg) NOR ~> PRODUCT
      //****************************************
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      convertFormulaToCNF(*it, defs);
      clauses = info[*it]->clausespos;
      if (clauses->size() > 1)
        {
          renamesibs = true;
        }
      psi = COPY(*clauses);
      reduceMemoryFootprintPos(*it);

      for (it++; it != varphi.GetChildren().end(); it++)
        {
          if (renamesibs)
            {
              setDoSibRenamingPos(*(info[*it]));
            }
          convertFormulaToCNF(*it, defs);
          clauses = info[*it]->clausespos;
          if (clauses->size() > 1)
            {
              renamesibs = true;
            }
          oldpsi = psi;
          psi = PRODUCT(*psi, *clauses);
          reduceMemoryFootprintPos(*it);
          DELETE(oldpsi);
        }

      info[varphi]->clausesneg = psi;
    }

    void convertFormulaToCNFNegIMPLIES(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (neg) IMPLIES ~> UNION [0] ; NOT [1]
      //****************************************
      CNFInfo* x0 = info[varphi[0]];
      CNFInfo* x1 = info[varphi[1]];
      convertFormulaToCNF(varphi[0], defs);
      convertFormulaToCNF(varphi[1], defs);
      BeevMgr::ClauseList* psi = UNION(*(x0->clausespos), *(x1->clausesneg));
      info[varphi]->clausesneg = psi;
      reduceMemoryFootprintPos(varphi[0]);
      reduceMemoryFootprintNeg(varphi[1]);
    }

    void convertFormulaToCNFNegITE(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      //****************************************
      // (neg) ITE ~> UNION (PRODUCT NOT [0] ; NOT [1])
      //  ; (PRODUCT [0] ; NOT [2])
      //****************************************
      CNFInfo* x0 = info[varphi[0]];
      CNFInfo* x1 = info[varphi[1]];
      CNFInfo* x2 = info[varphi[2]];
      convertFormulaToCNF(varphi[0], defs);
      if (x0->clausesneg->size() > 1)
        {
          setDoSibRenamingNeg(*x1);
        }
      convertFormulaToCNF(varphi[1], defs);
      if (x0->clausespos->size() > 1)
        {
          setDoSibRenamingNeg(*x2);
        }
      convertFormulaToCNF(varphi[2], defs);
      BeevMgr::ClauseList* psi1 = PRODUCT(*(x0->clausesneg), *(x1->clausesneg));
      BeevMgr::ClauseList* psi2 = PRODUCT(*(x0->clausespos), *(x2->clausesneg));
      NOCOPY_INPLACE_UNION(psi1, psi2);
      reduceMemoryFootprintNeg(varphi[0]);
      reduceMemoryFootprintNeg(varphi[1]);
      reduceMemoryFootprintPos(varphi[0]);
      reduceMemoryFootprintNeg(varphi[2]);

      info[varphi]->clausesneg = psi1;
    }

    void convertFormulaToCNFNegXOR(const ASTNode& varphi, BeevMgr::ClauseList* defs)
    {
      ASTVec::const_iterator it = varphi.GetChildren().begin();
      for (; it != varphi.GetChildren().end(); it++)
        {
          convertFormulaToCNF(*it, defs); // make pos and neg clause sets
        }
      BeevMgr::ClauseList* psi = convertFormulaToCNFNegXORAux(varphi, 0, defs);
      info[varphi]->clausesneg = psi;
      ASTVec::const_iterator it2 = varphi.GetChildren().begin();
      for (; it2 != varphi.GetChildren().end(); it2++){
        reduceMemoryFootprintPos(*it2);
        reduceMemoryFootprintNeg(*it2);
      }
    }

    BeevMgr::ClauseList* convertFormulaToCNFNegXORAux(const ASTNode& varphi, unsigned int idx, BeevMgr::ClauseList* defs)
    {

      bool renamesibs;
      BeevMgr::ClauseList* psi;
      BeevMgr::ClauseList* psi1;
      BeevMgr::ClauseList* psi2;

      if (idx == varphi.GetChildren().size() - 2)
        {

          //****************************************
          // (neg) XOR ~> UNION
          //    (PRODUCT NOT   [idx]   ;     [idx+1])
          //  ; (PRODUCT       [idx]   ; NOT [idx+1])
          //****************************************
          convertFormulaToCNF(varphi[idx], defs);
          renamesibs = (info[varphi[idx]]->clausesneg)->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingPos(*info[varphi[idx + 1]]);
            }

          convertFormulaToCNF(varphi[idx], defs);
          renamesibs = (info[varphi[idx]]->clausespos)->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingNeg(*info[varphi[idx + 1]]);
            }

          psi1 = PRODUCT(*(info[varphi[idx]]->clausesneg), *(info[varphi[idx + 1]]->clausespos));
          psi2 = PRODUCT(*(info[varphi[idx]]->clausespos), *(info[varphi[idx + 1]]->clausesneg));
          NOCOPY_INPLACE_UNION(psi1, psi2);

          psi = psi1;
        }
      else
        {
          //****************************************
          // (neg) XOR ~> UNION
          //    (PRODUCT NOT   [idx] ; XOR      [idx+1..])
          //  ; (PRODUCT       [idx] ; NOT XOR  [idx+1..])
          //****************************************
          BeevMgr::ClauseList* theta1;
          theta1 = convertFormulaToCNFPosXORAux(varphi, idx + 1, defs);
          renamesibs = theta1->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingNeg(*info[varphi[idx]]);
            }
          convertFormulaToCNF(varphi[idx], defs);

          BeevMgr::ClauseList* theta2;
          theta2 = convertFormulaToCNFNegXORAux(varphi, idx + 1, defs);
          renamesibs = theta2->size() > 1 ? true : false;
          if (renamesibs)
            {
              setDoSibRenamingPos(*info[varphi[idx]]);
            }

          psi1 = PRODUCT(*(info[varphi[idx]]->clausesneg), *theta1);
          psi2 = PRODUCT(*(info[varphi[idx]]->clausespos), *theta2);
          DELETE(theta1);
          DELETE(theta2);
          NOCOPY_INPLACE_UNION(psi1, psi2);

          psi = psi1;
        }

      return psi;
    }

    //########################################
    //########################################
    // utilities for reclaiming memory.

    void reduceMemoryFootprintPos(const ASTNode& varphi)
    {

      CNFInfo* x = info[varphi];
      if (sharesPos(*x) == 1)
        {
          DELETE(x->clausespos);
          x->clausespos = NULL;
          if (x->clausesneg == NULL)
            {
              delete x;
              info.erase(varphi);
            }
        }
    }

    void reduceMemoryFootprintNeg(const ASTNode& varphi)
    {

      CNFInfo* x = info[varphi];
      if (sharesNeg(*x) == 1)
        {
          DELETE(x->clausesneg);
          x->clausesneg = NULL;
          if (x->clausespos == NULL)
            {
              delete x;
              info.erase(varphi);
            }
        }
    }

    //########################################
    //########################################

    ASTNode* ASTNodeToASTNodePtr(const ASTNode& varphi)
    {
      ASTNode* psi;

      if (store.find(varphi) != store.end())
        {
          psi = store[varphi];
        }
      else
        {
          psi = new ASTNode(varphi);
          store[varphi] = psi;
        }

      return psi;
    }

    //########################################
    //########################################

    void cleanup(const ASTNode& varphi)
    {
      delete info[varphi]->clausespos;
      CNFInfo* toDelete = info[varphi]; // get the thing to delete.
      info.erase(varphi);                                 // remove it from the hashtable
      delete toDelete;


      ASTNodeToCNFInfoMap::const_iterator it1 = info.begin();
      for (; it1 != info.end(); it1++)
        {
          CNFInfo* x = it1->second;
          if (x->clausespos != NULL)
            {
              DELETE(x->clausespos);
            }
          if (x->clausesneg != NULL)
            {
              if (!isTerm(*x))
                {
                  DELETE(x->clausesneg);
                }
            }
          delete x;
        }

      info.clear();
    }

  }; // end of CNFMgr class

  SOLVER_RETURN_TYPE BeevMgr::TopLevelSAT(const ASTNode& inputasserts, 
					  const ASTNode& query)
  {

    ASTNode q = CreateNode(AND, inputasserts, CreateNode(NOT, query));
    return TopLevelSATAux(q);
  }

  //############################################################
  //############################################################


  void BeevMgr::DeleteClauseList(BeevMgr::ClauseList *cllp)
  {
    BeevMgr::ClauseList::const_iterator iend = cllp->end();
    for (BeevMgr::ClauseList::const_iterator i = cllp->begin(); i < iend; i++)
      {
        delete *i;
      }
    delete cllp;
  }

  //Call the SAT solver, and check the result before returning. This
  //can return one of 3 values, SOLVER_VALID, SOLVER_INVALID or SOLVER_UNDECIDED
  SOLVER_RETURN_TYPE BeevMgr::CallSAT_ResultCheck(MINISAT::Solver& SatSolver, 
                                                  const ASTNode& modified_input,
                                                  const ASTNode& original_input)
  {
    runTimes.start(RunTimes::BitBlasting);
    ASTNode BBFormula = BBForm(modified_input);
	runTimes.stop(RunTimes::BitBlasting);

    CNFMgr* cm = new CNFMgr(this);
    ClauseList* cl = cm->convertToCNF(BBFormula);
    if (stats_flag)
      {
        cerr << "Number of clauses:" << cl->size() << endl;
      }
    //PrintClauseList(cout, *cl);
    bool sat = toSATandSolve(SatSolver, *cl);
    cm->DELETE(cl);
    delete cm;

    if (!sat)
      {
        //PrintOutput(true);
        return SOLVER_VALID;
      }
    else if (SatSolver.okay())
      {
        CounterExampleMap.clear();
        ConstructCounterExample(SatSolver);
        if (stats_flag && print_nodes_flag)
          {
            PrintSATModel(SatSolver);
          }
        //check if the counterexample is good or not
        ComputeFormulaMap.clear();
        if (counterexample_checking_during_refinement)
          bvdiv_exception_occured = false;
        ASTNode orig_result = ComputeFormulaUsingModel(original_input);
        if (!(ASTTrue == orig_result || ASTFalse == orig_result))
          FatalError("TopLevelSat: Original input must compute to "\
                     "true or false against model");

        // if the counterexample is indeed a good one, then return
        // invalid
        if (ASTTrue == orig_result)
          {
            //CheckCounterExample(SatSolver.okay());
            //PrintOutput(false);
            PrintCounterExample(SatSolver.okay());
            PrintCounterExample_InOrder(SatSolver.okay());
            return SOLVER_INVALID;
          }
        // counterexample is bogus: flag it
        else
          {
            if (stats_flag && print_nodes_flag)
              {
                cout << "Supposedly bogus one: \n";
                bool tmp = print_counterexample_flag;
                print_counterexample_flag = true;
                PrintCounterExample(true);
                print_counterexample_flag = tmp;
              }

            return SOLVER_UNDECIDED;
          }
      }
    else
      {
        //Control should never reach here
        //PrintOutput(true);
        return SOLVER_ERROR;
      }
  } //end of CALLSAT_ResultCheck

} // end namespace BEEV

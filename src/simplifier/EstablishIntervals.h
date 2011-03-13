/*
 * Performs a very basic unsigned interval analysis.
 * Currently it only has a couple of basic operations.
 */

#ifndef ESTABLISHINTERVALS_H_
#define ESTABLISHINTERVALS_H_
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "simplifier.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"


namespace BEEV
{

  class EstablishIntervals
  {
  private:

  public:
    struct IntervalType
    {
      CBV minV;
      CBV maxV;
      IntervalType(CBV _min, CBV _max)
      {
        minV = _min;
        maxV = _max;
      }

      void print()
      {
        cout << *(minV) << " " << *(maxV) << endl;
      }
    };

    vector<EstablishIntervals::IntervalType * > toDeleteLater;
    vector<CBV> likeAutoPtr;

private:

    IntervalType * freshUnsignedInterval(int width)
    {
      IntervalType *it = createInterval(makeCBV(width), makeCBV(width));
      CONSTANTBV::BitVector_Fill(it->maxV);
      return it;
    }

    IntervalType * createInterval(CBV min, CBV max)
    {
      IntervalType *it = new IntervalType(min,max);
      toDeleteLater.push_back(it);
      return it ;
    }

    CBV makeCBV(int width)
    {
        CBV result = CONSTANTBV::BitVector_Create(width, true);
        likeAutoPtr.push_back(result);
        return result;
    }


  public:
    // Replace some of the things that unsigned intervals can figure out for us.
    ASTNode topLevel_unsignedIntervals(const ASTNode&top)
    {
      bm.GetRunTimes()->start(RunTimes::IntervalPropagation);
      map<const ASTNode, IntervalType*> visited;
      visit(top,visited);
      ASTNodeMap fromTo;
      for (map<const ASTNode, IntervalType*>::const_iterator it = visited.begin(); it != visited.end(); it++)
      {
          const ASTNode& n = it->first;
          IntervalType *interval = it->second;

          if (interval == NULL)
            continue;
          if (n.isConstant())
            continue;
          if (interval->maxV == interval->minV && n.GetType() == BOOLEAN_TYPE)
            {
              if (0== CONSTANTBV::BitVector_Lexicompare(interval->maxV,littleOne))
                fromTo.insert(make_pair(n,bm.ASTTrue));
                else
                  fromTo.insert(make_pair(n,bm.ASTFalse));
            }
      }

      if (fromTo.size() > 0)
        {
          ASTNodeMap cache;
          SimplifyingNodeFactory nf(*(top.GetSTPMgr()->defaultNodeFactory), *top.GetSTPMgr());
          bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);
          return SubstitutionMap::replace(top,fromTo,cache,&nf);
        }

      bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);
      return top;
    }

  private:
    // A single pass through the problem replacing things that must be true of false.
    IntervalType* visit(const ASTNode& n, map<const ASTNode, IntervalType*> & visited)
    {
      if (visited.find(n) != visited.end())
        return visited.find(n)->second;

      vector<IntervalType* > children_intervals;
      children_intervals.reserve(n.Degree());
      for (int i=0; i < n.Degree();i++)
        {
          children_intervals.push_back(visit(n[i],visited));
        }

      IntervalType * result = NULL;

      if (BVCONST == n.GetKind() || BITVECTOR == n.GetKind())       // If it's a constant, make it.
        {
          // the CBV doesn't leak. it is a copy of the cbv inside the node.
          CBV cbv = n.GetBVConst();
          result = createInterval(cbv,cbv);
        }
      else if (BVGE == n.GetKind() && children_intervals[0] != NULL && children_intervals[1] != NULL)
        {
          if (CONSTANTBV::BitVector_Lexicompare(children_intervals[0]->minV,children_intervals[1]->maxV) >=0)
            result = createInterval(littleOne, littleOne);
        }
      else if (BVMOD == n.GetKind() && children_intervals[1] != NULL)
        {
          // When we're dividing by zero, we know nothing.
          if (!CONSTANTBV::BitVector_is_empty(children_intervals[1]->maxV))
            {
              result = freshUnsignedInterval(n.GetValueWidth());
              CONSTANTBV::BitVector_Copy(result->maxV , children_intervals[1]->maxV);
              CONSTANTBV::BitVector_decrement(result->maxV);
            }
        }

      // result will often be null (which we take to mean the maximum range).
        visited.insert(make_pair(n,result));
        return result;
    }

    STPMgr& bm;
    CBV littleOne;
    CBV littleZero;
  public:
    EstablishIntervals(STPMgr& _bm) : bm(_bm)
    {
      littleZero = makeCBV(1);
      littleOne = makeCBV(1);
      CONSTANTBV::BitVector_Fill(littleOne);
    }

    ~EstablishIntervals()
    {
      for (int i =0; i < toDeleteLater.size();i++)
        delete toDeleteLater[i];

      for (int i =0; i < likeAutoPtr.size();i++)
        CONSTANTBV::BitVector_Destroy(likeAutoPtr[i]);

      likeAutoPtr.clear();
      toDeleteLater.clear();
    }




  };
}
;
#endif /* ESTABLISHINTERVALS_H_ */

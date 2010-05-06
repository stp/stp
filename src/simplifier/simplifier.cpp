// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <cassert>
#include <cmath>
#include "simplifier.h"

namespace BEEV
{

  ASTNode Simplifier::Flatten(const ASTNode& a)
  {
    ASTNode n = a;
    while (true)
      {
        ASTNode& nold = n;
        n = FlattenOneLevel(n);
        if ((n == nold))
          break;
      }
        
    return n;
  }



  bool Simplifier::CheckMap(ASTNodeMap* VarConstMap, 
                            const ASTNode& key, ASTNode& output)
  {
    if(NULL == VarConstMap)
      {
        return false;
      }
    ASTNodeMap::iterator it;
    if ((it = VarConstMap->find(key)) != VarConstMap->end())
      {
        output = it->second;
        return true;
      }
    return false;
  }


  bool Simplifier::CheckSimplifyMap(const ASTNode& key, 
                                    ASTNode& output, 
                                    bool pushNeg, ASTNodeMap* VarConstMap)
  {
    if(NULL != VarConstMap) 
      {
        return false;
      }
    ASTNodeMap::iterator it, itend;
    it = pushNeg ? SimplifyNegMap->find(key) : SimplifyMap->find(key);
    itend = pushNeg ? SimplifyNegMap->end() : SimplifyMap->end();

    if (it != itend)
      {
        output = it->second;
        CountersAndStats("Successful_CheckSimplifyMap", _bm);
        return true;
      }

    if (pushNeg && (it = SimplifyMap->find(key)) != SimplifyMap->end())
      {
        output = 
          (ASTFalse == it->second) ? 
          ASTTrue : 
          (ASTTrue == it->second) ? 
          ASTFalse : _bm->CreateNode(NOT, it->second);
        CountersAndStats("2nd_Successful_CheckSimplifyMap", _bm);
        return true;
      }

    return false;
  }

  // Push any reference count used by the key to the value.
  void Simplifier::UpdateSimplifyMap(const ASTNode& key, 
                                     const ASTNode& value, 
                                     bool pushNeg, ASTNodeMap* VarConstMap)
  {
    if(NULL != VarConstMap)
      {
        return;
      }

    // Don't add leaves. Leaves are easy to recalculate, no need
    // to cache.
    if (0 == key.Degree())
      return;
    
    // If there are references to the key, add them to the references
    // of the value.
    ASTNodeCountMap::const_iterator itKey, itValue;
    itKey = ReferenceCount->find(key);
    if (itKey != ReferenceCount->end())
      {
        itValue = ReferenceCount->find(value);
        if (itValue != ReferenceCount->end())
          (*ReferenceCount)[value] = itValue->second + itKey->second;
        else
          (*ReferenceCount)[value] = itKey->second;
      }


    if (pushNeg)
      (*SimplifyNegMap)[key] = value;
    else
      (*SimplifyMap)[key] = value;
  }

  bool Simplifier::CheckSubstitutionMap(const ASTNode& key, ASTNode& output)
  {
    ASTNode k = key;
    ASTNodeMap::iterator it = SolverMap->find(key);
    if (it != SolverMap->end())
      {
        output = it->second;
        return true;
      }
    return false;
  }

  bool Simplifier::CheckSubstitutionMap(const ASTNode& key)
  {
    if (SolverMap->find(key) != SolverMap->end())
      return true;
    else
      return false;
  }

  bool Simplifier::UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1)
  {
    int i = TermOrder(e0, e1);
    if (0 == i)
      return false;

    assert(e0 != e1); // One side should be a variable, the other a constant.

    //e0 is of the form READ(Arr,const), and e1 is const, or
    //e0 is of the form var, and e1 is const
    if (1 == i && !CheckSubstitutionMap(e0))
      {
        assert((e1.GetKind() == TRUE) || 
               (e1.GetKind() == FALSE) || 
               (e1.GetKind() == BVCONST));
        (*SolverMap)[e0] = e1;
        return true;
      }

    //e1 is of the form READ(Arr,const), and e0 is const, or
    //e1 is of the form var, and e0 is const
    if (-1 == i && !CheckSubstitutionMap(e1))
      {
        assert((e0.GetKind() == TRUE)  || 
               (e0.GetKind() == FALSE) || 
               (e0.GetKind() == BVCONST));
        (*SolverMap)[e1] = e0;
        return true;
      }

    return false;
  }

  bool Simplifier::CheckMultInverseMap(const ASTNode& key, ASTNode& output)
  {
    ASTNodeMap::iterator it;
    if ((it = MultInverseMap.find(key)) != MultInverseMap.end())
      {
        output = it->second;
        return true;
      }
    return false;
  }

  void Simplifier::UpdateMultInverseMap(const ASTNode& key, 
                                        const ASTNode& value)
  {
    MultInverseMap[key] = value;
  }

  bool Simplifier::CheckAlwaysTrueFormMap(const ASTNode& key)
  {
    ASTNodeSet::iterator it = AlwaysTrueFormMap.find(key);
    ASTNodeSet::iterator itend = AlwaysTrueFormMap.end();

    if (it != itend)
      {
        //cerr << "found:" << *it << endl;
        CountersAndStats("Successful_CheckAlwaysTrueFormMap", _bm);
        return true;
      }

    return false;
  }

  void Simplifier::UpdateAlwaysTrueFormMap(const ASTNode& key)
  {
    AlwaysTrueFormMap.insert(key);
  }

  ASTNode 
  Simplifier::SimplifyFormula_NoRemoveWrites(const ASTNode& b, 
                                             bool pushNeg,
                                             ASTNodeMap* VarConstMap)
  {
    _bm->Begin_RemoveWrites = false;
    ASTNode out = SimplifyFormula(b, pushNeg, VarConstMap);
    return out;
  }

  void Simplifier::BuildReferenceCountMap(const ASTNode& b)
  {
    if (b.GetChildren().size() == 0)
      return;

    ASTNodeCountMap::iterator it, itend;

    it = ReferenceCount->find(b);
    if (it == ReferenceCount->end())
      {
        (*ReferenceCount)[b] = 1;
      }
    else
      {
        (*ReferenceCount)[b] = it->second + 1;
        return;
      }

    const ASTVec& c = b.GetChildren();
    ASTVec::const_iterator itC = c.begin();
    ASTVec::const_iterator itendC = c.end();
    for (; itC != itendC; itC++)
      {
        BuildReferenceCountMap(*itC);
      }
  }

  // The SimplifyMaps on entry to the topLevel functions may contain
  // useful entries.  E.g. The BVSolver calls SimplifyTerm()
  ASTNode Simplifier::SimplifyFormula_TopLevel(const ASTNode& b, 
                                               bool pushNeg, 
                                               ASTNodeMap* VarConstMap)
  {
    _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
    if (_bm->UserFlags.smtlib_parser_flag)
      BuildReferenceCountMap(b);
    ASTNode out = SimplifyFormula(b, pushNeg, VarConstMap);
    ResetSimplifyMaps();
    _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
    return out;
  }

  ASTNode Simplifier::SimplifyTerm_TopLevel(const ASTNode& b)
  {
    _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
    ASTNode out = SimplifyTerm(b);
    ResetSimplifyMaps();
    _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
    return out;
  }


  ASTNode 
  Simplifier::SimplifyFormula(const ASTNode& b, 
                              bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //     if (!optimize_flag)
    //       return b;

    Kind kind = b.GetKind();
    if (BOOLEAN_TYPE != b.GetType())
      {
        FatalError(" SimplifyFormula: "\
                   "You have input a nonformula kind: ", ASTUndefined, kind);
      }

    ASTNode a = b;
    ASTVec ca = a.GetChildren();
    if (!(IMPLIES == kind || 
          ITE == kind     || 
          FOR == kind     ||
          PARAMBOOL==kind ||
          isAtomic(kind)))
      {
        SortByArith(ca);
        a = _bm->CreateNode(kind, ca);
      }

    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    a = PullUpITE(a);
    kind = a.GetKind(); // pullUpITE can change the Kind of the node.

    switch (kind)
      {
      case AND:
      case OR:
        output = SimplifyAndOrFormula(a, pushNeg, VarConstMap);
        break;
      case NOT:
        output = SimplifyNotFormula(a, pushNeg, VarConstMap);
        break;
      case XOR:
        output = SimplifyXorFormula(a, pushNeg, VarConstMap);
        break;
      case NAND:
        output = SimplifyNandFormula(a, pushNeg, VarConstMap);
        break;
      case NOR:
        output = SimplifyNorFormula(a, pushNeg, VarConstMap);
        break;
      case IFF:
        output = SimplifyIffFormula(a, pushNeg, VarConstMap);
        break;
      case IMPLIES:
        output = SimplifyImpliesFormula(a, pushNeg, VarConstMap);
        break;
      case ITE:
        output = SimplifyIteFormula(a, pushNeg, VarConstMap);
        break;
      case FOR:
        output = SimplifyForFormula(a, pushNeg, VarConstMap);
        break;
      default:
        //kind can be EQ,NEQ,BVLT,BVLE,... or a propositional variable
        output = SimplifyAtomicFormula(a, pushNeg, VarConstMap);
        //output = pushNeg ? _bm->CreateNode(NOT,a) : a;
        break;
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode 
  Simplifier::SimplifyForFormula(const ASTNode& a, 
                                 bool pushNeg, ASTNodeMap* VarConstMap) 
  {
    //FIXME: Code this up properly later. Mainly pushing the negation
    //down
    return a;
  }

  ASTNode 
  Simplifier::SimplifyAtomicFormula(const ASTNode& a, 
                                    bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //     if (!optimize_flag)
    //       return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      {
        return output;
      }

    ASTNode left, right;
    if (a.Degree() == 2)
      {
        //cerr << "Input to simplifyterm: left: " << a[0] << endl;
        left = SimplifyTerm(a[0], VarConstMap);
        //cerr << "Output of simplifyterm:left: " << left << endl;
        //cerr << "Input to simplifyterm: right: " << a[1] << endl;
        right = SimplifyTerm(a[1], VarConstMap);
        //cerr << "Output of simplifyterm:left: " << right << endl;
      }

    Kind kind = a.GetKind();
    switch (kind)
      {
      case TRUE:
        output = pushNeg ? ASTFalse : ASTTrue;
        break;
      case FALSE:
        output = pushNeg ? ASTTrue : ASTFalse;
        break;
      case SYMBOL:
        if (!CheckSolverMap(a, output))
          {
            output = a;
          }
        output = pushNeg ? _bm->CreateNode(NOT, output) : output;
        break;
      case PARAMBOOL:
        {
          ASTNode term = SimplifyTerm(a[1], VarConstMap);
          output = _bm->CreateNode(PARAMBOOL, a[0], term);
          output = pushNeg ? _bm->CreateNode(NOT, output) : output;
          break;
        }
      case BVGETBIT:
        {
          ASTNode term = SimplifyTerm(a[0], VarConstMap);
          ASTNode thebit = a[1];
          ASTNode zero = _bm->CreateZeroConst(1);
          ASTNode one = _bm->CreateOneConst(1);
          ASTNode getthebit = 
            SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 1, term, thebit, thebit),
                         VarConstMap);
          if (getthebit == zero)
            output = pushNeg ? ASTTrue : ASTFalse;
          else if (getthebit == one)
            output = pushNeg ? ASTFalse : ASTTrue;
          else
            {
              output = _bm->CreateNode(BVGETBIT, term, thebit);
              output = pushNeg ? _bm->CreateNode(NOT, output) : output;
            }
          break;
        }
      case EQ:
        {
          output = CreateSimplifiedEQ(left, right);
          output = LhsMinusRhs(output);
          output = ITEOpt_InEqs(output);
          if (output == ASTTrue)
            output = pushNeg ? ASTFalse : ASTTrue;
          else if (output == ASTFalse)
            output = pushNeg ? ASTTrue : ASTFalse;
          else
            output = pushNeg ? _bm->CreateNode(NOT, output) : output;
          break;
        }
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
        {
          //output = _bm->CreateNode(kind,left,right);
          //output = pushNeg ? _bm->CreateNode(NOT,output) : output;
          output = CreateSimplifiedINEQ(kind, left, right, pushNeg);
          break;
        }
      default:
        FatalError("SimplifyAtomicFormula: "\
                   "NO atomic formula of the kind: ", ASTUndefined, kind);
        break;
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  } //end of SimplifyAtomicFormula()

  ASTNode Simplifier::CreateSimplifiedINEQ(Kind k, 
                                           const ASTNode& left, 
                                           const ASTNode& right, bool pushNeg)
  {
    ASTNode output;
    if (BVCONST == left.GetKind() && BVCONST == right.GetKind())
      {
        output = BVConstEvaluator(_bm->CreateNode(k, left, right));
        output = pushNeg ? (ASTFalse == output) ? ASTTrue : ASTFalse : output;
        return output;
      }

    unsigned len = left.GetValueWidth();
    ASTNode zero = _bm->CreateZeroConst(len);
    ASTNode one = _bm->CreateOneConst(len);
    ASTNode max = _bm->CreateMaxConst(len);
    switch (k)
      {
      case BVLT:
        if (right == zero)
          {
            output = pushNeg ? ASTTrue : ASTFalse;
          }
        else if (left == right)
          {
            output = pushNeg ? ASTTrue : ASTFalse;
          }
        else if (one == right)
          {
            output = CreateSimplifiedEQ(left, zero);
            output = pushNeg ? _bm->CreateNode(NOT, output) : output;
          }
        else
          {
            output = 
              pushNeg ? 
              _bm->CreateNode(BVLE, right, left) : 
              _bm->CreateNode(BVLT, left, right);
          }
        break;
      case BVLE:
        if (left == zero)
          {
            output = pushNeg ? ASTFalse : ASTTrue;
          }
        else if (left == right)
          {
            output = pushNeg ? ASTFalse : ASTTrue;
          }
        else if (max == right)
          {
            output = pushNeg ? ASTFalse : ASTTrue;
          }
        else if (zero == right)
          {
            output = CreateSimplifiedEQ(left, zero);
            output = pushNeg ? _bm->CreateNode(NOT, output) : output;
          }
        else
          {
            output = 
              pushNeg ? 
              _bm->CreateNode(BVLT, right, left) : 
              _bm->CreateNode(BVLE, left, right);
          }
        break;
      case BVGT:
        if (left == zero)
          {
            output = pushNeg ? ASTTrue : ASTFalse;
          }
        else if (left == right)
          {
            output = pushNeg ? ASTTrue : ASTFalse;
          }
        else
          {
            output = 
              pushNeg ? 
              _bm->CreateNode(BVLE, left, right) : 
              _bm->CreateNode(BVLT, right, left);
          }
        break;
      case BVGE:
        if (right == zero)
          {
            output = pushNeg ? ASTFalse : ASTTrue;
          }
        else if (left == right)
          {
            output = pushNeg ? ASTFalse : ASTTrue;
          }
        else
          {
            output = 
              pushNeg ? 
              _bm->CreateNode(BVLT, left, right) : 
              _bm->CreateNode(BVLE, right, left);
          }
        break;
      case BVSLT:
      case BVSLE:
      case BVSGE:
      case BVSGT:
        {
          output = _bm->CreateNode(k, left, right);
          output = pushNeg ? _bm->CreateNode(NOT, output) : output;
        }
        break;
      default:
        FatalError("Wrong Kind");
        break;
      }

    return output;
  }

  //Look through the AND Node for terms that contradict.
  //Should be made significantly more general..
  ASTNode Simplifier::RemoveContradictionsFromAND(const ASTNode& in)
  {
    assert(AND == in.GetKind());
    const int childrenSize = in.GetChildren().size();

    for (int i = 0; i < childrenSize; i++)
      {
        if (BVLT != in[i].GetKind())
          continue;

        for (int j = i + 1; j < childrenSize; j++)
          {
            if (BVLT != in[j].GetKind())
              continue;
            // parameters are swapped.
            if (in[i][0] == in[j][1] && in[i][1] == in[j][0])
              return ASTFalse;
          }
      }
    return in;
  }

  // turns say (bvslt (ite a b c) (ite a d e)) INTO (ite a (bvslt b d)
  // (bvslt c e)) Expensive. But makes some other simplifications
  // possible.
  ASTNode Simplifier::PullUpITE(const ASTNode& in)
  {
    if (2 != in.GetChildren().size())
      return in;
    if (ITE != in[0].GetKind())
      return in;
    if (ITE != in[1].GetKind())
      return in;
    if (in[0][0] != in[1][0]) // if the conditional is not equal.
      return in;

    // Consider equals. It takes bitvectors and returns a boolean.
    // Consider add. It takes bitvectors and returns bitvectors.
    // Consider concat. The bitwidth of each side could vary.

    ASTNode l1;
    ASTNode l2;
    ASTNode result;

    if (in.GetType() == BOOLEAN_TYPE)
      {
        l1 = _bm->CreateNode(in.GetKind(), in[0][1], in[1][1]);
        l2 = _bm->CreateNode(in.GetKind(), in[0][2], in[1][2]);
        result = _bm->CreateNode(ITE, in[0][0], l1, l2);
      }
    else
      {
        l1 = 
          _bm->CreateTerm(in.GetKind(),
                          in.GetValueWidth(), in[0][1], in[1][1]);
        l2 = 
          _bm->CreateTerm(in.GetKind(), 
                          in.GetValueWidth(), in[0][2], in[1][2]);
        result = 
          _bm->CreateTerm(ITE, 
                          in.GetValueWidth(), in[0][0], l1, l2);
      }

    assert(result.GetType() == in.GetType());
    assert(result.GetValueWidth() == in.GetValueWidth());
    assert(result.GetIndexWidth() == in.GetIndexWidth());
    assert(BVTypeCheck(result));

    return result;
  }

  //takes care of some simple ITE Optimizations in the context of equations
  ASTNode Simplifier::ITEOpt_InEqs(const ASTNode& in, ASTNodeMap* VarConstMap)
  {
    CountersAndStats("ITEOpts_InEqs", _bm);

    if (!(EQ == in.GetKind()))
      {
        return in;
      }

    ASTNode output;
    if (CheckSimplifyMap(in, output, false))
      {
        return output;
      }

    ASTNode in1 = in[0];
    ASTNode in2 = in[1];
    Kind k1 = in1.GetKind();
    Kind k2 = in2.GetKind();
    if (in1 == in2)
      {
        //terms are syntactically the same
        output = ASTTrue;
      }
    else if (BVCONST == k1 && BVCONST == k2)
      {
        //here the terms are definitely not syntactically equal but may
        //be semantically equal.
        output = ASTFalse;
      }
    else if (ITE == k1 && 
             BVCONST == in1[1].GetKind() && 
             BVCONST == in1[2].GetKind() && BVCONST == k2)
      {
        //if one side is a BVCONST and the other side is an ITE over
        //BVCONST then we can do the following optimization:
        //
        // c = ITE(cond,c,d) <=> cond
        //
        // similarly ITE(cond,c,d) = c <=> cond
        //
        // c = ITE(cond,d,c) <=> NOT(cond)
        //
        //similarly ITE(cond,d,c) = d <=> NOT(cond)
        ASTNode cond = in1[0];
        if (in1[1] == in2)
          {
            //ITE(cond, c, d) = c <=> cond
            output = cond;
          }
        else if (in1[2] == in2)
          {
            cond = SimplifyFormula(cond, true, VarConstMap);
            output = cond;
          }
        else
          {
            //last resort is to _bm->CreateNode
            output = _bm->CreateNode(EQ, in1, in2);
          }
      }
    else if (ITE == k2 && 
             BVCONST == in2[1].GetKind() && 
             BVCONST == in2[2].GetKind() && BVCONST == k1)
      {
        ASTNode cond = in2[0];
        if (in2[1] == in1)
          {
            //ITE(cond, c, d) = c <=> cond
            output = cond;
          }
        else if (in2[2] == in1)
          {
            cond = SimplifyFormula(cond, true, VarConstMap);
            output = cond;
          }
        else
          {
            //last resort is to CreateNode
            output = _bm->CreateNode(EQ, in1, in2);
          }
      }
    else
      {
        //last resort is to CreateNode
        output = _bm->CreateNode(EQ, in1, in2);
      }

    UpdateSimplifyMap(in, output, false, VarConstMap);
    return output;
  } //End of ITEOpts_InEqs()

  //Tries to simplify the input to TRUE/FALSE. if it fails, then
  //return the constructed equality
  ASTNode Simplifier::CreateSimplifiedEQ(const ASTNode& in1, const ASTNode& in2)
  {
    CountersAndStats("CreateSimplifiedEQ", _bm);
    Kind k1 = in1.GetKind();
    Kind k2 = in2.GetKind();

    // if (!optimize_flag)
    //  {
    //          return CreateNode(EQ, in1, in2);
    //  }

    if (in1 == in2)
      //terms are syntactically the same
      return ASTTrue;

    //here the terms are definitely not syntactically equal but may be
    //semantically equal.
    if (BVCONST == k1 && BVCONST == k2)
      return ASTFalse;

    //last resort is to CreateNode
    return _bm->CreateNode(EQ, in1, in2);
  }

  //accepts cond == t1, then part is t2, and else part is t3
  ASTNode Simplifier::CreateSimplifiedTermITE(const ASTNode& in0, 
                                              const ASTNode& in1, 
                                              const ASTNode& in2)
  {
    ASTNode t0 = in0;
    ASTNode t1 = in1;
    ASTNode t2 = in2;
    CountersAndStats("CreateSimplifiedITE", _bm);
    if (!_bm->UserFlags.optimize_flag)
      {
        if (t1.GetValueWidth() != t2.GetValueWidth())
          {
            cerr << "t2 is : = " << t2;
            FatalError("CreateSimplifiedTermITE: "\
                       "the lengths of the two branches don't match", t1);
          }
        if (t1.GetIndexWidth() != t2.GetIndexWidth())
          {
            cerr << "t2 is : = " << t2;
            FatalError("CreateSimplifiedTermITE: "\
                       "the lengths of the two branches don't match", t1);
          }
        return _bm->CreateTerm(ITE, t1.GetValueWidth(), t0, t1, t2);
      }

    if (t0 == ASTTrue)
      return t1;
    if (t0 == ASTFalse)
      return t2;
    if (t1 == t2)
      return t1;
    if (CheckAlwaysTrueFormMap(t0))
      {
        return t1;
      }
    if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, t0)) 
        || (NOT == t0.GetKind() 
            && CheckAlwaysTrueFormMap(t0[0])))
      {
        return t2;
      }

    return _bm->CreateTerm(ITE, t1.GetValueWidth(), t0, t1, t2);
  }

  ASTNode 
  Simplifier::
  CreateSimplifiedFormulaITE(const ASTNode& in0,
                             const ASTNode& in1, const ASTNode& in2)
  {
    ASTNode t0 = in0;
    ASTNode t1 = in1;
    ASTNode t2 = in2;
    CountersAndStats("CreateSimplifiedFormulaITE", _bm);

    if (_bm->UserFlags.optimize_flag)
      {
        if (t0 == ASTTrue)
          return t1;
        if (t0 == ASTFalse)
          return t2;
        if (t1 == t2)
          return t1;
        if (CheckAlwaysTrueFormMap(t0))
          {
            return t1;
          }
        if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, t0))
            || (NOT == t0.GetKind() 
                && CheckAlwaysTrueFormMap(t0[0])))
          {
            return t2;
          }
      }
    ASTNode result = _bm->CreateNode(ITE, t0, t1, t2);
    BVTypeCheck(result);
    return result;
  }

  ASTNode Simplifier::SimplifyAndOrFormula(const ASTNode& a, 
                                           bool pushNeg, 
                                           ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    //cerr << "input:\n" << a << endl;

    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    ASTVec c, outvec;
    c = a.GetChildren();
    ASTNode flat = Flatten(a);
    c = flat.GetChildren();
    SortByArith(c);

    Kind k = a.GetKind();
    bool isAnd = (k == AND) ? true : false;

    ASTNode annihilator = 
      isAnd ? 
      (pushNeg ? ASTTrue : ASTFalse) : 
      (pushNeg ? ASTFalse : ASTTrue);

    ASTNode identity = 
      isAnd ? 
      (pushNeg ? ASTFalse : ASTTrue) : 
      (pushNeg ? ASTTrue : ASTFalse);

    //do the work
    ASTVec::const_iterator next_it;
    for (ASTVec::const_iterator i = c.begin(), iend = c.end(); i != iend; i++)
      {
        ASTNode aaa = *i;
        next_it = i + 1;
        bool nextexists = (next_it < iend);

        aaa = SimplifyFormula(aaa, pushNeg, VarConstMap);
        if (annihilator == aaa)
          {
            //memoize
            UpdateSimplifyMap(*i, annihilator, pushNeg, VarConstMap);
            UpdateSimplifyMap(a, annihilator, pushNeg, VarConstMap);
            //cerr << "annihilator1: output:\n" << annihilator << endl;
            return annihilator;
          }
        ASTNode bbb = ASTFalse;
        if (nextexists)
          {
            bbb = SimplifyFormula(*next_it, pushNeg, VarConstMap);
          }
        if (nextexists && bbb == aaa)
          {
            //skip the duplicate aaa. *next_it will be included
          }
        else if (nextexists && ((bbb.GetKind() == NOT && bbb[0] == aaa)))
          {
            //memoize
            UpdateSimplifyMap(a, annihilator, pushNeg, VarConstMap);
            //cerr << "annihilator2: output:\n" << annihilator << endl;
            return annihilator;
          }
        else if (identity == aaa)
          {
            // //drop identites
          }
        else if ((!isAnd && !pushNeg) || (isAnd && pushNeg))
          {
            outvec.push_back(aaa);
          }
        else if ((isAnd && !pushNeg) || (!isAnd && pushNeg))
          {
            outvec.push_back(aaa);
          }
        else
          {
            outvec.push_back(aaa);
          }
      }

    switch (outvec.size())
      {
      case 0:
        {
          //only identities were dropped
          output = identity;
          break;
        }
      case 1:
        {
          output = SimplifyFormula(outvec[0], false, VarConstMap);
          break;
        }
      default:
        {
          output = 
            (isAnd) ? 
            (pushNeg ? 
             _bm->CreateNode(OR, outvec) : 
             _bm->CreateNode(AND, outvec)) : 
            (pushNeg ? 
             _bm->CreateNode(AND, outvec) : 
             _bm->CreateNode(OR,outvec));
          //output = FlattenOneLevel(output);
          break;
        }
      }

    // I haven't verified this is useful.
    //if (output.GetKind() == AND)
    //  output = RemoveContradictionsFromAND(output);

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    //cerr << "output:\n" << output << endl;
    return output;
  } //end of SimplifyAndOrFormula


  ASTNode 
  Simplifier::SimplifyNotFormula(const ASTNode& a, 
                                 bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 1 && NOT == a.GetKind()))
      FatalError("SimplifyNotFormula: input vector with more than 1 node", 
                 ASTUndefined);

    //if pushNeg is set then there is NOT on top
    unsigned int NotCount = pushNeg ? 1 : 0;
    ASTNode o = a;
    //count the number of NOTs in 'a'
    while (NOT == o.GetKind())
      {
        o = o[0];
        NotCount++;
      }

    //pushnegation if there are odd number of NOTs
    bool pn = (NotCount % 2 == 0) ? false : true;

    if (CheckAlwaysTrueFormMap(o))
      {
        output = pn ? ASTFalse : ASTTrue;
        return output;
      }

    if (CheckSimplifyMap(o, output, pn))
      {
        return output;
      }

    if (ASTTrue == o)
      {
        output = pn ? ASTFalse : ASTTrue;
      }
    else if (ASTFalse == o)
      {
        output = pn ? ASTTrue : ASTFalse;
      }
    else
      {
        output = SimplifyFormula(o, pn, VarConstMap);
      }
    //memoize
    UpdateSimplifyMap(o, output, pn, VarConstMap);
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyXorFormula(const ASTNode& a, 
                                         bool pushNeg, 
                                         ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (a.GetChildren().size() > 2)
      {
        FatalError("Simplify got an XOR with more than two children.");
      }

    ASTNode a0 = SimplifyFormula(a[0], false, VarConstMap);
    ASTNode a1 = SimplifyFormula(a[1], false, VarConstMap);
    output = 
      pushNeg ? 
      _bm->CreateNode(IFF, a0, a1) : 
      _bm->CreateNode(XOR, a0, a1);

    if (XOR == output.GetKind())
      {
        a0 = output[0];
        a1 = output[1];
        if (a0 == a1)
          output = ASTFalse;
        else if ((a0 == ASTTrue 
                  && a1 == ASTFalse) 
                 || (a0 == ASTFalse 
                     && a1 == ASTTrue))
          output = ASTTrue;
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyNandFormula(const ASTNode& a, 
                                          bool pushNeg, 
                                          ASTNodeMap* VarConstMap)
  {
    ASTNode output, a0, a1;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    //the two NOTs cancel out
    if (pushNeg)
      {
        a0 = SimplifyFormula(a[0], false, VarConstMap);
        a1 = SimplifyFormula(a[1], false, VarConstMap);
        output = _bm->CreateNode(AND, a0, a1);
      }
    else
      {
        //push the NOT implicit in the NAND
        a0 = SimplifyFormula(a[0], true, VarConstMap);
        a1 = SimplifyFormula(a[1], true, VarConstMap);
        output = _bm->CreateNode(OR, a0, a1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyNorFormula(const ASTNode& a, 
                                         bool pushNeg, 
                                         ASTNodeMap* VarConstMap)
  {
    ASTNode output, a0, a1;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    //the two NOTs cancel out
    if (pushNeg)
      {
        a0 = SimplifyFormula(a[0], false);
        a1 = SimplifyFormula(a[1], false, VarConstMap);
        output = _bm->CreateNode(OR, a0, a1);
      }
    else
      {
        //push the NOT implicit in the NAND
        a0 = SimplifyFormula(a[0], true, VarConstMap);
        a1 = SimplifyFormula(a[1], true, VarConstMap);
        output = _bm->CreateNode(AND, a0, a1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyImpliesFormula(const ASTNode& a, 
                                             bool pushNeg, 
                                             ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 2 && IMPLIES == a.GetKind()))
      FatalError("SimplifyImpliesFormula: vector with wrong num of nodes", 
                 ASTUndefined);

    ASTNode c0, c1;
    if (pushNeg)
      {
        c0 = SimplifyFormula(a[0], false, VarConstMap);
        c1 = SimplifyFormula(a[1], true, VarConstMap);
        output = _bm->CreateNode(AND, c0, c1);
      }
    else
      {
        c0 = SimplifyFormula(a[0], false, VarConstMap);
        c1 = SimplifyFormula(a[1], false, VarConstMap);
        if (ASTFalse == c0)
          {
            output = ASTTrue;
          }
        else if (ASTTrue == c0)
          {
            output = c1;
          }
        else if (c0 == c1)
          {
            output = ASTTrue;
          }
        else if (CheckAlwaysTrueFormMap(c0))
          {
            // c0 AND (~c0 OR c1) <==> c1
            //
            //applying modus ponens
            output = c1;
          }
        else if (CheckAlwaysTrueFormMap(c1) || 
                 CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, c0)) || 
                 (NOT == c0.GetKind() && CheckAlwaysTrueFormMap(c0[0])))
          {
            //(~c0 AND (~c0 OR c1)) <==> TRUE
            //
            //(c0 AND ~c0->c1) <==> TRUE
            output = ASTTrue;
          }
        else if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, c1)) || 
                 (NOT == c1.GetKind() && CheckAlwaysTrueFormMap(c1[0])))
          {
            //(~c1 AND c0->c1) <==> (~c1 AND ~c1->~c0) <==> ~c0
            //(c1 AND c0->~c1) <==> (c1 AND c1->~c0) <==> ~c0
            output = _bm->CreateNode(NOT, c0);
          }
        else
          {
            if (NOT == c0.GetKind())
              {
                output = _bm->CreateNode(OR, c0[0], c1);
              }
            else
              {
                output = _bm->CreateNode(OR, _bm->CreateNode(NOT, c0), c1);
              }
          }
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyIffFormula(const ASTNode& a, 
                                         bool pushNeg, 
                                         ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 2 && IFF == a.GetKind()))
      FatalError("SimplifyIffFormula: vector with wrong num of nodes", 
                 ASTUndefined);

    ASTNode c0 = a[0];
    ASTNode c1 = SimplifyFormula(a[1], false, VarConstMap);

    if (pushNeg)
      c0 = SimplifyFormula(c0, true, VarConstMap);
    else
      c0 = SimplifyFormula(c0, false, VarConstMap);

    if (ASTTrue == c0)
      {
        output = c1;
      }
    else if (ASTFalse == c0)
      {
        output = SimplifyFormula(c1, true, VarConstMap);
      }
    else if (ASTTrue == c1)
      {
        output = c0;
      }
    else if (ASTFalse == c1)
      {
        output = SimplifyFormula(c0, true, VarConstMap);
      }
    else if (c0 == c1)
      {
        output = ASTTrue;
      }
    else if ((NOT == c0.GetKind() 
              && c0[0] == c1) 
             || (NOT == c1.GetKind() 
                 && c0 == c1[0]))
      {
        output = ASTFalse;
      }
    else if (CheckAlwaysTrueFormMap(c0))
      {
        output = c1;
      }
    else if (CheckAlwaysTrueFormMap(c1))
      {
        output = c0;
      }
    else if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, c0)))
      {
        output = _bm->CreateNode(NOT, c1);
      }
    else if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, c1)))
      {
        output = _bm->CreateNode(NOT, c0);
      }
    else
      {
        output = _bm->CreateNode(IFF, c0, c1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode Simplifier::SimplifyIteFormula(const ASTNode& b, 
                                         bool pushNeg, 
                                         ASTNodeMap* VarConstMap)
  {
    //    if (!optimize_flag)
    //       return b;

    ASTNode output;
    if (CheckSimplifyMap(b, output, pushNeg, VarConstMap))
      return output;

    if (!(b.Degree() == 3 && ITE == b.GetKind()))
      FatalError("SimplifyIteFormula: vector with wrong num of nodes", 
                 ASTUndefined);

    ASTNode a = b;
    ASTNode t0 = SimplifyFormula(a[0], false, VarConstMap);
    ASTNode t1, t2;
    if (pushNeg)
      {
        t1 = SimplifyFormula(a[1], true, VarConstMap);
        t2 = SimplifyFormula(a[2], true, VarConstMap);
      }
    else
      {
        t1 = SimplifyFormula(a[1], false, VarConstMap);
        t2 = SimplifyFormula(a[2], false, VarConstMap);
      }

    if (ASTTrue == t0)
      {
        output = t1;
      }
    else if (ASTFalse == t0)
      {
        output = t2;
      }
    else if (t1 == t2)
      {
        output = t1;
      }
    else if (ASTTrue == t1 && ASTFalse == t2)
      {
        output = t0;
      }
    else if (ASTFalse == t1 && ASTTrue == t2)
      {
        output = SimplifyFormula(t0, true, VarConstMap);
      }
    else if (ASTTrue == t1)
      {
        output = _bm->CreateNode(OR, t0, t2);
      }
    else if (ASTFalse == t1)
      {
        output = _bm->CreateNode(AND, _bm->CreateNode(NOT, t0), t2);
      }
    else if (ASTTrue == t2)
      {
        output = _bm->CreateNode(OR, _bm->CreateNode(NOT, t0), t1);
      }
    else if (ASTFalse == t2)
      {
        output = _bm->CreateNode(AND, t0, t1);
      }
    else if (CheckAlwaysTrueFormMap(t0))
      {
        output = t1;
      }
    else if (CheckAlwaysTrueFormMap(_bm->CreateNode(NOT, t0)) || 
             (NOT == t0.GetKind() && CheckAlwaysTrueFormMap(t0[0])))
      {
        output = t2;
      }
    else
      {
        output = _bm->CreateNode(ITE, t0, t1, t2);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  //one level deep flattening
  ASTNode Simplifier::FlattenOneLevel(const ASTNode& a)
  {
    Kind k = a.GetKind();
    if (!(BVPLUS == k || AND == k || OR == k
          //|| BVAND == k
          //|| BVOR == k
          ))
      {
        return a;
      }

    ASTNode output;
    // if(CheckSimplifyMap(a,output,false)) {
    //       //check memo table
    //       //cerr << "output of SimplifyTerm Cache: " << output << endl;
    //       return output;
    //     }

    ASTVec c = a.GetChildren();
    ASTVec o;
    for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        ASTNode aaa = *it;
        if (k == aaa.GetKind())
          {
            ASTVec ac = aaa.GetChildren();
            o.insert(o.end(), ac.begin(), ac.end());
          }
        else
          o.push_back(aaa);
      }

    if (is_Form_kind(k))
      output = _bm->CreateNode(k, o);
    else
      output = _bm->CreateTerm(k, a.GetValueWidth(), o);

    //UpdateSimplifyMap(a,output,false);
    return output;
    //memoize
  } //end of flattenonelevel()

  //This function simplifies terms based on their kind
  ASTNode 
  Simplifier::SimplifyTerm(const ASTNode& actualInputterm, 
                           ASTNodeMap* VarConstMap)
  {
    ASTNode inputterm(actualInputterm); // mutable local copy.

    //cout << "SimplifyTerm: input: " << a << endl;
    // if (!optimize_flag)
    //       {
    //         return inputterm;
    //       }

    ASTNode output = inputterm;
    assert(BVTypeCheck(inputterm));
        
    //########################################
    //########################################

    if (CheckSubstitutionMap(inputterm, output))
      {
        //cout << "SolverMap:" << inputterm << " output: " << output << endl;
        return SimplifyTerm(output, VarConstMap);
      }

    if (CheckSimplifyMap(inputterm, output, false, VarConstMap))
      {
        //cerr << "SimplifierMap:" << inputterm << " output: " <<
        //output << endl;
        return output;
      }
    //########################################
    //########################################

    Kind k = inputterm.GetKind();
    if (!is_Term_kind(k))
      {
        FatalError("SimplifyTerm: You have input a Non-term", inputterm);
      }

    unsigned int inputValueWidth = inputterm.GetValueWidth();

    inputterm = PullUpITE(inputterm);
    k = inputterm.GetKind(); // pull up ITE can change the kind of the node

    switch (k)
      {
      case BVCONST:
        output = inputterm;
        break;
      case SYMBOL:
        if(CheckMap(VarConstMap, inputterm, output)) 
          {
            return output;
          }
        if (CheckSolverMap(inputterm, output))
          {
            return SimplifyTerm(output, VarConstMap);
          }
        output = inputterm;
        break;
      case BVMULT:
        {
          if (2 != inputterm.Degree())
            {
              FatalError("SimplifyTerm: We assume that BVMULT is binary",
                         inputterm);
            }

          // Described nicely by Warren, Hacker's Delight pg 135.
          // Turn sequences of one bits into subtractions.  28*x ==
          // 32x - 4x (two instructions), rather than 16x+ 8x+ 4x.
          // When fully implemented. I.e. supporting sequences of 1
          // anywhere.  Other simplifications will try to fold these
          // back in. So need to be careful about when the
          // simplifications are applied. But in this version it won't
          // be simplified down by anything else.


          // This (temporary) version only simplifies if all the left
          // most bits are set.  All the leftmost bits being set
          // simplifies very nicely down.
          const ASTNode& n0 = inputterm.GetChildren()[0];
          const ASTNode& n1 = inputterm.GetChildren()[1];

          // This implementation has two problems.  1) It causes a
          // segfault for cmu-model15,16,17 2) It doesn't count the
          // number of bits saved, so if there is a single leading bit
          // it will invert it. Even though that will take more shifts
          // and adds when it's finally done.

          // disabled.
          if (false 
              && (BVCONST == n0.GetKind()) 
              ^ (BVCONST == n1.GetKind()))
            {
              CBV constant = 
                (BVCONST == n0.GetKind()) ? 
                n0.GetBVConst() : 
                n1.GetBVConst();
              ASTNode other = 
                (BVCONST == n0.GetKind()) ? 
                n1 : 
                n0;

              int startSequence = 0;
              for (unsigned int i = 0; i < inputValueWidth; i++)
                {
                  if (!CONSTANTBV::BitVector_bit_test(constant, i))
                    startSequence = i;
                }

              if ((inputValueWidth - startSequence) > 3)
                {
                  // turn off all bits from "startSequence to the
                  // end", then add one.
                  CBV maskedPlusOne = 
                    CONSTANTBV::BitVector_Create(inputValueWidth, true);
                  for (int i = 0; i < startSequence; i++)
                    {
                      if (!CONSTANTBV::BitVector_bit_test(constant, i)) // swap
                        CONSTANTBV::BitVector_Bit_On(maskedPlusOne, i);
                    }
                  CONSTANTBV::BitVector_increment(maskedPlusOne);
                  ASTNode temp = 
                    _bm->CreateTerm(BVMULT, inputValueWidth, 
                                    _bm->CreateBVConst(maskedPlusOne, 
                                                       inputValueWidth), 
                                    other);
                  output = _bm->CreateTerm(BVNEG, inputValueWidth, temp);
                }
            }

        }
        if (output.IsNull())
          break;

      case BVPLUS:
        {
          ASTVec c = Flatten(inputterm).GetChildren();
          SortByArith(c);
          ASTVec constkids, nonconstkids;



          //go through the childnodes, and separate constant and
          //nonconstant nodes. combine the constant nodes using the
          //constevaluator. if the resultant constant is zero and k ==
          //BVPLUS, then ignore it (similarily for 1 and BVMULT).  else,
          //add the computed constant to the nonconst vector, flatten,
          //sort, and create BVPLUS/BVMULT and return
          for (ASTVec::iterator 
                 it = c.begin(), itend = c.end(); 
               it != itend; it++)
            {
              ASTNode aaa = SimplifyTerm(*it, VarConstMap);
              if (BVCONST == aaa.GetKind())
                {
                  constkids.push_back(aaa);
                }
              else
                {
                  nonconstkids.push_back(aaa);
                }
            }

          ASTNode one = _bm->CreateOneConst(inputValueWidth);
          ASTNode max = _bm->CreateMaxConst(inputValueWidth);
          ASTNode zero = _bm->CreateZeroConst(inputValueWidth);

          //initialize constoutput to zero, in case there are no elements
          //in constkids
          ASTNode constoutput = (k == BVPLUS) ? zero : one;

          if (1 == constkids.size())
            {
              //only one element in constkids
              constoutput = constkids[0];
            }
          else if (1 < constkids.size())
            {
              //many elements in constkids. simplify it
              constoutput = 
                _bm->CreateTerm(k, inputterm.GetValueWidth(), constkids);
              constoutput = BVConstEvaluator(constoutput);
            }

          if (BVMULT == k 
              && zero == constoutput)
            {
              output = zero;
            }
          else if (BVMULT == k 
                   && 1 == nonconstkids.size() 
                   && constoutput == max)
            {
              //useful special case opt: when input is BVMULT(max_const,t),
              //then output = BVUMINUS(t). this is easier on the bitblaster
              output = 
                _bm->CreateTerm(BVUMINUS, inputValueWidth, nonconstkids);
            }
          else
            {
              if (0 < nonconstkids.size())
                {
                  //nonconstkids is not empty. First, combine const and
                  //nonconstkids
                  if (BVPLUS == k && constoutput != zero)
                    {
                      nonconstkids.push_back(constoutput);
                    }
                  else if (BVMULT == k && constoutput != one)
                    {
                      nonconstkids.push_back(constoutput);
                    }

                  if (1 == nonconstkids.size())
                    {
                      //exactly one element in nonconstkids. output is exactly
                      //nonconstkids[0]
                      output = nonconstkids[0];
                    }
                  else
                    {
                      //more than 1 element in nonconstkids. create BVPLUS term
                      SortByArith(nonconstkids);
                      output = 
                        _bm->CreateTerm(k, inputValueWidth, nonconstkids);
                      output = Flatten(output);
                      output = DistributeMultOverPlus(output, true);
                      output = CombineLikeTerms(output);
                    }
                }
              else
                {
                  //nonconstkids was empty, all childnodes were constant, hence
                  //constoutput is the output.
                  output = constoutput;
                }
            }

          // propagate bvuminus upwards through multiplies.
          if (BVMULT == output.GetKind())
            {
              ASTVec d = output.GetChildren();
              int uminus = 0;
              for (unsigned i = 0; i < d.size(); i++)
                {
                  if (d[i].GetKind() == BVUMINUS)
                    {
                      d[i] = d[i][0];
                      uminus++;
                    }
                }
              if (uminus != 0)
                {
                  SortByArith(d);
                  output = _bm->CreateTerm(BVMULT, output.GetValueWidth(), d);
                  if ((uminus & 0x1) != 0) // odd, pull up the uminus.
                    {
                      output = 
                        _bm->CreateTerm(BVUMINUS, 
                                        output.GetValueWidth(), 
                                        output);
                    }
                }
            }



          if (BVMULT == output.GetKind() || BVPLUS == output.GetKind())
            {
              ASTVec d = output.GetChildren();
              SortByArith(d);
              output = 
                _bm->CreateTerm(output.GetKind(), 
                                output.GetValueWidth(), d);
            }



          break;

        }
      case BVSUB:
        {
          ASTVec c = inputterm.GetChildren();
          ASTNode a0 = SimplifyTerm(inputterm[0], VarConstMap);
          ASTNode a1 = SimplifyTerm(inputterm[1], VarConstMap);
          unsigned int l = inputValueWidth;
          if (a0 == a1)
            output = _bm->CreateZeroConst(l);
          else
            {
              //covert x-y into x+(-y) and simplify. this transformation
              //triggers more simplifications
              //
              a1 = 
                SimplifyTerm(_bm->CreateTerm(BVUMINUS, l, a1), 
                             VarConstMap);
              output = 
                SimplifyTerm(_bm->CreateTerm(BVPLUS, l, a0, a1), 
                             VarConstMap);
            }
          break;
        }
      case BVUMINUS:
        {
          //important to treat BVUMINUS as a special case, because it
          //helps in arithmetic transformations. e.g.  x + BVUMINUS(x) is
          //actually 0. One way to reveal this fact is to strip bvuminus
          //out, and replace with something else so that combineliketerms
          //can catch this fact.
          ASTNode a0 = SimplifyTerm(inputterm[0], VarConstMap);
          Kind k1 = a0.GetKind();
          unsigned int l = a0.GetValueWidth();
          ASTNode one = _bm->CreateOneConst(l);
          switch (k1)
            {
            case BVUMINUS:
              output = a0[0];
              break;
            case BVCONST:
              {
                output = BVConstEvaluator(_bm->CreateTerm(BVUMINUS, l, a0));
                break;
              }
            case BVNEG:
              {
                output = 
                  SimplifyTerm(_bm->CreateTerm(BVPLUS, l, a0[0], one), 
                               VarConstMap);
                break;
              }
            case BVMULT:
              {
                if (BVUMINUS == a0[0].GetKind())
                  {
                    output = _bm->CreateTerm(BVMULT, l, a0[0][0], a0[1]);
                  }
                else if (BVUMINUS == a0[1].GetKind())
                  {
                    output = _bm->CreateTerm(BVMULT, l, a0[0], a0[1][0]);
                  }
                else
                  {
                    // If the first argument to the multiply is a
                    // constant, push it through.  Without regard for
                    // the splitting of nodes (hmm.)  This is
                    // necessary because the bitvector solver can
                    // process -3*x, but not -(3*x).
                    if (BVCONST == a0[0].GetKind())
                      {
                        ASTNode a00 = 
                          SimplifyTerm(_bm->CreateTerm(BVUMINUS, l, a0[0]), 
                                       VarConstMap);
                        output = _bm->CreateTerm(BVMULT, l, a00, a0[1]);
                      }
                    else
                      output = _bm->CreateTerm(BVUMINUS, l, a0);
                  }
                break;
              }
            case BVPLUS:
              {
                //push BVUMINUS over all the monomials of BVPLUS. Simplify
                //along the way
                //
                //BVUMINUS(a1x1 + a2x2 + ...) <=> BVPLUS(BVUMINUS(a1x1) +
                //BVUMINUS(a2x2) + ...
                ASTVec c = a0.GetChildren();
                ASTVec o;
                for (ASTVec::iterator
                       it = c.begin(), itend = c.end(); it != itend; it++)
                  {
                    //Simplify(BVUMINUS(a1x1))
                    ASTNode aaa = 
                      SimplifyTerm(_bm->CreateTerm(BVUMINUS, l, *it), 
                                   VarConstMap);
                    o.push_back(aaa);
                  }
                //simplify the bvplus
                output = 
                  SimplifyTerm(_bm->CreateTerm(BVPLUS, l, o), 
                               VarConstMap);
                break;
              }
            case BVSUB:
              {
                //BVUMINUS(BVSUB(x,y)) <=> BVSUB(y,x)
                output = 
                  SimplifyTerm(_bm->CreateTerm(BVSUB, l, a0[1], a0[0]), 
                               VarConstMap);
                break;
              }
            case ITE:
              {
                //BVUMINUS(ITE(c,t1,t2)) <==> ITE(c,BVUMINUS(t1),BVUMINUS(t2))
                ASTNode c = a0[0];
                ASTNode t1 = 
                  SimplifyTerm(_bm->CreateTerm(BVUMINUS, l, a0[1]), 
                               VarConstMap);
                ASTNode t2 = 
                  SimplifyTerm(_bm->CreateTerm(BVUMINUS, l, a0[2]), 
                               VarConstMap);
                output = CreateSimplifiedTermITE(c, t1, t2);
                break;
              }
            default:
              {
                output = _bm->CreateTerm(BVUMINUS, l, a0);
                break;
              }
            }
          break;
        }
      case BVEXTRACT:
        {
          //it is important to take care of wordlevel transformation in
          //BVEXTRACT. it exposes oppurtunities for later simplification
          //and solving (variable elimination)
          ASTNode a0 = SimplifyTerm(inputterm[0], VarConstMap);
          Kind k1 = a0.GetKind();
          unsigned int a_len = inputValueWidth;

          //indices for BVEXTRACT
          ASTNode i = inputterm[1];
          ASTNode j = inputterm[2];
          ASTNode zero = _bm->CreateBVConst(32, 0);
          //recall that the indices of BVEXTRACT are always 32 bits
          //long. therefore doing a GetBVUnsigned is ok.
          unsigned int i_val = GetUnsignedConst(i);
          unsigned int j_val = GetUnsignedConst(j);

          // a0[i:0] and len(a0)=i+1, then return a0
          if (0 == j_val && a_len == a0.GetValueWidth())
            return a0;

          switch (k1)
            {
            case BVCONST:
              {
                //extract the constant
                output = 
                  BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, 
                                                   a_len, a0, i, j));
                break;
              }
            case BVCONCAT:
              {
                //assumes concatenation is binary
                //
                //input is of the form a0[i:j]
                //
                //a0 is the conatentation t@u, and a0[0] is t, and a0[1] is u
                ASTNode t = a0[0];
                ASTNode u = a0[1];
                unsigned int len_a0 = a0.GetValueWidth();
                unsigned int len_u = u.GetValueWidth();

                if (len_u > i_val)
                  {
                    //Apply the following rule:
                    // (t@u)[i:j] <==> u[i:j], if len(u) > i
                    //
                    output = 
                      SimplifyTerm(_bm->CreateTerm(BVEXTRACT, a_len, u, i, j), 
                                   VarConstMap);
                  }
                else if (len_a0 > i_val && j_val >= len_u)
                  {
                    //Apply the rule: (t@u)[i:j] <==>
                    // t[i-len_u:j-len_u], if len(t@u) > i >= j >=
                    // len(u)
                    i = _bm->CreateBVConst(32, i_val - len_u);
                    j = _bm->CreateBVConst(32, j_val - len_u);
                    output = 
                      SimplifyTerm(_bm->CreateTerm(BVEXTRACT, a_len, t, i, j), 
                                   VarConstMap);
                  }
                else
                  {
                    //Apply the rule:
                    // (t@u)[i:j] <==> t[i-len_u:0] @ u[len_u-1:j]
                    i = _bm->CreateBVConst(32, i_val - len_u);
                    ASTNode m = _bm->CreateBVConst(32, len_u - 1);
                    t = 
                      SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                                   i_val - len_u + 1, 
                                                   t, i, zero), 
                                   VarConstMap);
                    u = 
                      SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                                   len_u - j_val, 
                                                   u, m, j), 
                                   VarConstMap);
                    output = _bm->CreateTerm(BVCONCAT, a_len, t, u);
                  }
                break;
              }
            case BVPLUS:
            case BVMULT:
              {
                // (BVMULT(n,t,u))[i:j] <==> BVMULT(i+1,t[i:0],u[i:0])[i:j]
                //similar rule for BVPLUS
                ASTVec c = a0.GetChildren();
                ASTVec o;
                for (ASTVec::iterator 
                       jt = c.begin(), jtend = c.end(); 
                     jt != jtend; jt++)
                  {
                    ASTNode aaa = *jt;
                    aaa = 
                      SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                                   i_val + 1, 
                                                   aaa, i, zero), 
                                   VarConstMap);
                    o.push_back(aaa);
                  }
                output = _bm->CreateTerm(a0.GetKind(), i_val + 1, o);
                if (j_val != 0)
                  {
                    //add extraction only if j is not zero
                    output = _bm->CreateTerm(BVEXTRACT, a_len, output, i, j);
                  }
                break;
              }
            case BVAND:
            case BVOR:
            case BVXOR:
              {
                //assumes these operators are binary
                //
                // (t op u)[i:j] <==> t[i:j] op u[i:j]
                ASTNode t = a0[0];
                ASTNode u = a0[1];
                t = 
                  SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                               a_len, t, i, j), 
                               VarConstMap);
                u = 
                  SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                               a_len, u, i, j), 
                               VarConstMap);
                BVTypeCheck(t);
                BVTypeCheck(u);
                output = _bm->CreateTerm(k1, a_len, t, u);
                break;
              }
            case BVNEG:
              {
                // (~t)[i:j] <==> ~(t[i:j])
                ASTNode t = a0[0];
                t = 
                  SimplifyTerm(_bm->CreateTerm(BVEXTRACT, a_len, t, i, j), 
                               VarConstMap);
                output = _bm->CreateTerm(BVNEG, a_len, t);
                break;
              }
              // case BVSX:{ //(BVSX(t,n)[i:j] <==> BVSX(t,i+1), if n
              //        >= i+1 and j=0 ASTNode t = a0[0]; unsigned int
              //        bvsx_len = a0.GetValueWidth(); if(bvsx_len <
              //        a_len) { FatalError("SimplifyTerm: BVEXTRACT
              //        over BVSX:" "the length of BVSX term must be
              //        greater than extract-len",inputterm); } if(j
              //        != zero) { output =
              //        _bm->CreateTerm(BVEXTRACT,a_len,a0,i,j); }
              //        else { output =
              //        _bm->CreateTerm(BVSX,a_len,t,
              //                        _bm->CreateBVConst(32,a_len));
              //        } break; }
            case ITE:
              {
                ASTNode t0 = a0[0];
                ASTNode t1 = 
                  SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                               a_len, a0[1], i, j), 
                               VarConstMap);
                ASTNode t2 = 
                  SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                               a_len, a0[2], i, j), 
                               VarConstMap);
                output = CreateSimplifiedTermITE(t0, t1, t2);
                break;
              }
            default:
              {
                output = _bm->CreateTerm(BVEXTRACT, a_len, a0, i, j);
                break;
              }
            }
          break;
        }
      case BVNEG:
        {
          ASTNode a0 = SimplifyTerm(inputterm[0], VarConstMap);
          unsigned len = inputValueWidth;
          switch (a0.GetKind())
            {
            case BVCONST:
              output = BVConstEvaluator(_bm->CreateTerm(BVNEG, len, a0));
              break;
            case BVNEG:
              output = a0[0];
              break;
              // case ITE: { ASTNode cond = a0[0]; ASTNode thenpart =
              //        SimplifyTerm(_bm->CreateTerm(BVNEG,len,a0[1]),
              //        VarConstMap); ASTNode elsepart =
              //        SimplifyTerm(_bm->CreateTerm(BVNEG,len,a0[2]),
              //        VarConstMap); output =
              //        _bm->CreateSimplifiedTermITE(cond,thenpart,elsepart);
              //        break; }
            default:
              output = _bm->CreateTerm(BVNEG, len, a0);
              break;
            }
          break;
        }

      case BVSX:
        {
          //a0 is the expr which is being sign extended
          ASTNode a0 = SimplifyTerm(inputterm[0], VarConstMap);
          //a1 represents the length of the term BVSX(a0)
          ASTNode a1 = inputterm[1];
          //output length of the BVSX term
          unsigned len = inputValueWidth;

          if (a0.GetValueWidth() == len)
            {
              //nothing to signextend
              return a0;
            }

          switch (a0.GetKind())
            {
            case BVCONST:
              output = BVConstEvaluator(_bm->CreateTerm(BVSX, len, a0, a1));
              break;
            case BVNEG:
              output = 
                _bm->CreateTerm(a0.GetKind(), len, 
                                _bm->CreateTerm(BVSX, len, a0[0], a1));
              break;
            case BVAND:
            case BVOR:
              //assuming BVAND and BVOR are binary
              output = 
                _bm->CreateTerm(a0.GetKind(), len, 
                                _bm->CreateTerm(BVSX, len, a0[0], a1), 
                                _bm->CreateTerm(BVSX, len, a0[1], a1));
              break;
            case BVPLUS:
              {
                //BVSX(m,BVPLUS(n,BVSX(t1),BVSX(t2))) <==>
                //BVPLUS(m,BVSX(m,t1),BVSX(m,t2))
                ASTVec c = a0.GetChildren();
                bool returnflag = false;
                for (ASTVec::iterator
                       it = c.begin(), itend = c.end(); it != itend; it++)
                  {
                    if (BVSX != it->GetKind())
                      {
                        returnflag = true;
                        break;
                      }
                  }
                if (returnflag)
                  {
                    output = _bm->CreateTerm(BVSX, len, a0, a1);
                  }
                else
                  {
                    ASTVec o;
                    for (ASTVec::iterator 
                           it = c.begin(), itend = c.end(); it != itend; it++)
                      {
                        ASTNode aaa = 
                          SimplifyTerm(_bm->CreateTerm(BVSX, len, *it, a1), 
                                       VarConstMap);
                        o.push_back(aaa);
                      }
                    output = _bm->CreateTerm(a0.GetKind(), len, o);
                  }
                break;
              }
            case BVSX:
              {
                //if you have BVSX(m,BVSX(n,a)) then you can drop the inner
                //BVSX provided m is greater than n.
                a0 = SimplifyTerm(a0[0], VarConstMap);
                output = _bm->CreateTerm(BVSX, len, a0, a1);
                break;
              }
            case ITE:
              {
                ASTNode cond = a0[0];
                ASTNode thenpart = 
                  SimplifyTerm(_bm->CreateTerm(BVSX, len, a0[1], a1), 
                               VarConstMap);
                ASTNode elsepart = 
                  SimplifyTerm(_bm->CreateTerm(BVSX, len, a0[2], a1), 
                               VarConstMap);
                output = CreateSimplifiedTermITE(cond, thenpart, elsepart);
                break;
              }
            default:
              output = _bm->CreateTerm(BVSX, len, a0, a1);
              break;
            }
          break;
        }
      case BVAND:
      case BVOR:
        {
          ASTNode max = _bm->CreateMaxConst(inputValueWidth);
          ASTNode zero = _bm->CreateZeroConst(inputValueWidth);

          ASTNode identity = (BVAND == k) ? max : zero;
          ASTNode annihilator = (BVAND == k) ? zero : max;
          ASTVec c = Flatten(inputterm).GetChildren();
          SortByArith(c);
          ASTVec o;
          bool constant = true;
          for (ASTVec::iterator
                 it = c.begin(), itend = c.end(); it != itend; it++)
            {
              ASTNode aaa = SimplifyTerm(*it, VarConstMap);
              if (BVCONST != aaa.GetKind())
                {
                  constant = false;
                }

              if (aaa == annihilator)
                {
                  output = annihilator;
                  //memoize
                  UpdateSimplifyMap(inputterm, output, false, VarConstMap);
                  //cerr << "output of SimplifyTerm: " << output << endl;
                  return output;
                }

              if (aaa != identity)
                {
                  o.push_back(aaa);
                }
            }

          switch (o.size())
            {
            case 0:
              output = identity;
              break;
            case 1:
              output = o[0];
              break;
            default:
              SortByArith(o);
              output = _bm->CreateTerm(k, inputValueWidth, o);
              if (constant)
                {
                  output = BVConstEvaluator(output);
                }
              break;
            }
          break;
        }
      case BVCONCAT:
        {
          ASTNode t = SimplifyTerm(inputterm[0], VarConstMap);
          ASTNode u = SimplifyTerm(inputterm[1], VarConstMap);
          Kind tkind = t.GetKind();
          Kind ukind = u.GetKind();

          if (BVCONST == tkind && BVCONST == ukind)
            {
              output = 
                BVConstEvaluator(_bm->CreateTerm(BVCONCAT, 
                                                 inputValueWidth, t, u));
            }
          else if (BVEXTRACT == tkind 
                   && BVEXTRACT == ukind 
                   && t[0] == u[0])
            {
              //to handle the case x[m:n]@x[n-1:k] <==> x[m:k]
              ASTNode t_hi = t[1];
              ASTNode t_low = t[2];
              ASTNode u_hi = u[1];
              ASTNode u_low = u[2];
              ASTNode c =
                BVConstEvaluator(_bm->CreateTerm(BVPLUS, 32, 
                                                 u_hi, 
                                                 _bm->CreateOneConst(32)));
              if (t_low == c)
                {
                  output = 
                    _bm->CreateTerm(BVEXTRACT, 
                                    inputValueWidth, t[0], t_hi, u_low);
                }
              else
                {
                  output = _bm->CreateTerm(BVCONCAT, inputValueWidth, t, u);
                }
            }
          else
            {
              output = _bm->CreateTerm(BVCONCAT, inputValueWidth, t, u);
            }
          break;
        }


      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:

        { // If the shift amount is known. Then replace it by an extract.
          ASTNode a = SimplifyTerm(inputterm[0], VarConstMap);
          ASTNode b = SimplifyTerm(inputterm[1], VarConstMap);
          const unsigned int width = a.GetValueWidth();
          if (BVCONST == b.GetKind()) // known shift amount.
            {
              if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + log2(width))
                {
                  // Intended to remove shifts by very large amounts
                  // that don't fit into the unsigned.  at thhe start
                  // of the "else" branch.
                  output = _bm->CreateZeroConst(width);
                }
              else
                {
                  const unsigned int shift = GetUnsignedConst(b);
                  if (shift >= width)
                    {
                      output = _bm->CreateZeroConst(width);
                    }
                  else if (shift == 0)
                    {
                      output = a; // unchanged.
                    }
                  else
                    {
                      if (k == BVLEFTSHIFT)
                        {
                          ASTNode zero = _bm->CreateZeroConst(shift);
                          ASTNode hi = _bm->CreateBVConst(32, width - shift -1);
                          ASTNode low = _bm->CreateBVConst(32, 0);
                          ASTNode extract = 
                            _bm->CreateTerm(BVEXTRACT, width - shift, 
                                            a, hi, low);
                          BVTypeCheck(extract);
                          output = 
                            _bm->CreateTerm(BVCONCAT, width, 
                                            extract, zero);
                          BVTypeCheck(output);
                        }
                      else if (k == BVRIGHTSHIFT)
                        {
                          ASTNode zero = _bm->CreateZeroConst(shift);
                          ASTNode hi = _bm->CreateBVConst(32, width -1);
                          ASTNode low = _bm->CreateBVConst(32, shift);
                          ASTNode extract = 
                            _bm->CreateTerm(BVEXTRACT, width - shift, 
                                            a, hi, low);
                          BVTypeCheck(extract);
                          output = 
                            _bm->CreateTerm(BVCONCAT, width, zero, extract);
                          BVTypeCheck(output);
                        }
                      else
                        FatalError("herasdf");
                    }
                }
            }
          else
            output = _bm->CreateTerm(k, width, a, b);
        }
        break;


      case BVXOR:
      case BVXNOR:
      case BVNAND:
      case BVNOR:
      case BVVARSHIFT:
      case BVSRSHIFT:
      case BVDIV:
      case BVMOD:
        {
          ASTVec c = inputterm.GetChildren();
          ASTVec o;
          bool constant = true;
          for (ASTVec::iterator 
                 it = c.begin(), itend = c.end(); it != itend; it++)
            {
              ASTNode aaa = SimplifyTerm(*it, VarConstMap);
              if (BVCONST != aaa.GetKind())
                {
                  constant = false;
                }
              o.push_back(aaa);
            }
          output = _bm->CreateTerm(k, inputValueWidth, o);
          if (constant)
            output = BVConstEvaluator(output);
          break;
        }
      case READ:
        {
          ASTNode out1;
          //process only if not  in the substitution map. simplifymap
          //has been checked already
          if (!CheckSubstitutionMap(inputterm, out1))
            {
              if (WRITE == inputterm[0].GetKind())
                {
                  //get rid of all writes
		  //_bm->ASTNodeStats("before RemoveWrites_TopLevel:", inputterm);
                  ASTNode nowrites = RemoveWrites_TopLevel(inputterm);
		  //_bm->ASTNodeStats("after RemoveWrites_TopLevel:", nowrites);
                  out1 = nowrites;
                }
              else if (ITE == inputterm[0].GetKind())
                {
                  ASTNode cond = 
                    SimplifyFormula(inputterm[0][0], false, VarConstMap);
                  ASTNode index = 
                    SimplifyTerm(inputterm[1], VarConstMap);
                  ASTNode read1 = 
                    _bm->CreateTerm(READ, 
                                    inputValueWidth, 
                                    inputterm[0][1], index);
                  ASTNode read2 = 
                    _bm->CreateTerm(READ, 
                                    inputValueWidth, 
                                    inputterm[0][2], index);
                  read1 = SimplifyTerm(read1, VarConstMap);
                  read2 = SimplifyTerm(read2, VarConstMap);
                  out1 = CreateSimplifiedTermITE(cond, read1, read2);
                }
              else
                {
                  //arr is a SYMBOL for sure
                  ASTNode arr = inputterm[0];
                  ASTNode index = SimplifyTerm(inputterm[1], VarConstMap);
                  out1 = _bm->CreateTerm(READ, inputValueWidth, arr, index);
                }
            }
          //it is possible that after all the procesing the READ term
          //reduces to READ(Symbol,const) and hence we should check the
          //substitutionmap once again.
          if (!CheckSubstitutionMap(out1, output))
            output = out1;
          break;
        }
      case ITE:
        {
          ASTNode t0 = SimplifyFormula(inputterm[0], false, VarConstMap);
          ASTNode t1 = SimplifyTerm(inputterm[1], VarConstMap);
          ASTNode t2 = SimplifyTerm(inputterm[2], VarConstMap);
          output = CreateSimplifiedTermITE(t0, t1, t2);
          break;
        }
      case SBVREM:
      case SBVDIV:
      case SBVMOD:
        {
          ASTVec c = inputterm.GetChildren();
          ASTVec o;
          for (ASTVec::iterator
                 it = c.begin(), itend = c.end(); it != itend; it++)
            {
              ASTNode aaa = SimplifyTerm(*it, VarConstMap);
              o.push_back(aaa);
            }
          output = _bm->CreateTerm(k, inputValueWidth, o);
          break;
        }
      case WRITE:
      default:
        FatalError("SimplifyTerm: Control should never reach here:", 
                   inputterm, k);
        return inputterm;
        break;
      }
    assert(!output.IsNull());

    //memoize
    UpdateSimplifyMap(inputterm, output, false, VarConstMap);
    //cerr << "SimplifyTerm: output" << output << endl;
    // CheckSimplifyInvariant(inputterm,output);

    return output;
  } //end of SimplifyTerm()


  //At the end of each simplification call, we want the output to be
  //always smaller or equal to the input in size.
  void Simplifier::CheckSimplifyInvariant(const ASTNode& a, 
                                          const ASTNode& output)
  {

    if (_bm->NodeSize(a, true) + 1 < _bm->NodeSize(output, true))
      {
        cerr << "lhs := " << a << endl;
        cerr << "NodeSize of lhs is: " 
             << _bm->NodeSize(a, true) << endl;
        cerr << endl;
        cerr << "rhs := " << output << endl;
        cerr << "NodeSize of rhs is: " 
             << _bm->NodeSize(output, true) << endl;
        //  FatalError("SimplifyFormula: The nodesize shoudl decrease
        //  from lhs to rhs: ",ASTUndefined);
      }
  }

  //this function assumes that the input is a vector of childnodes of
  //a BVPLUS term. it combines like terms and returns a bvplus
  //term. e.g. 1.x + 2.x is converted to 3.x
  ASTNode Simplifier::CombineLikeTerms(const ASTNode& a)
  {
    if (BVPLUS != a.GetKind())
      return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    const ASTVec& c = a.GetChildren();
    //map from variables to vector of constants
    ASTNodeToVecMap vars_to_consts;
    //vector to hold constants
    ASTVec constkids;
    ASTVec outputvec;

    //useful constants
    unsigned int len = c[0].GetValueWidth();
    ASTNode one = _bm->CreateOneConst(len);
    ASTNode zero = _bm->CreateZeroConst(len);
    ASTNode max = _bm->CreateMaxConst(len);

    //go over the childnodes of the input bvplus, and collect like
    //terms in a map. the key of the map are the variables, and the
    //values are stored in a ASTVec
    for (ASTVec::const_iterator
           it = c.begin(), itend = c.end(); it != itend; it++)
      {
        ASTNode aaa = *it;
        if (SYMBOL == aaa.GetKind())
          {
            vars_to_consts[aaa].push_back(one);
          }
        else if (BVMULT == aaa.GetKind() 
                 && BVUMINUS == aaa[0].GetKind() 
                 && BVCONST == aaa[0][0].GetKind())
          {
            //(BVUMINUS(c))*(y) <==> compute(BVUMINUS(c))*y
            ASTNode compute_const = BVConstEvaluator(aaa[0]);
            vars_to_consts[aaa[1]].push_back(compute_const);
          }
        else if (BVMULT == aaa.GetKind() 
                 && BVUMINUS == aaa[1].GetKind() 
                 && BVCONST == aaa[0].GetKind())
          {
            //c*(BVUMINUS(y)) <==> compute(BVUMINUS(c))*y
            ASTNode cccc = 
              BVConstEvaluator(_bm->CreateTerm(BVUMINUS, len, aaa[0]));
            vars_to_consts[aaa[1][0]].push_back(cccc);
          }
        else if (BVMULT == aaa.GetKind() && BVCONST == aaa[0].GetKind())
          {
            //assumes that BVMULT is binary
            vars_to_consts[aaa[1]].push_back(aaa[0]);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[0].GetKind())
          {
            //(-1*x)*(y) <==> -1*(xy)
            ASTNode cccc = _bm->CreateTerm(BVMULT, len, aaa[0][0], aaa[1]);
            ASTVec cNodes = cccc.GetChildren();
            SortByArith(cNodes);
            vars_to_consts[cccc].push_back(max);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[1].GetKind())
          {
            //x*(-1*y) <==> -1*(xy)
            ASTNode cccc = _bm->CreateTerm(BVMULT, len, aaa[0], aaa[1][0]);
            ASTVec cNodes = cccc.GetChildren();
            SortByArith(cNodes);
            vars_to_consts[cccc].push_back(max);
          }
        else if (BVCONST == aaa.GetKind())
          {
            constkids.push_back(aaa);
          }
        else if (BVUMINUS == aaa.GetKind())
          {
            //helps to convert BVUMINUS into a BVMULT. here the max
            //constant represents -1. this transformation allows us to
            //conclude that x + BVUMINUS(x) is 0.
            vars_to_consts[aaa[0]].push_back(max);
          }
        else
          vars_to_consts[aaa].push_back(one);
      } //end of for loop

    //go over the map from variables to vector of values. combine the
    //vector of values, multiply to the variable, and put the
    //resultant monomial in the output BVPLUS.
    for (ASTNodeToVecMap::iterator 
           it = vars_to_consts.begin(), itend = vars_to_consts.end();
         it != itend; it++)
      {
        ASTVec ccc = it->second;

        ASTNode constant;
        if (1 < ccc.size())
          {
            constant = _bm->CreateTerm(BVPLUS, ccc[0].GetValueWidth(), ccc);
            constant = BVConstEvaluator(constant);
          }
        else
          constant = ccc[0];

        //constant * var
        ASTNode monom;
        if (zero == constant)
          monom = zero;
        else if (one == constant)
          monom = it->first;
        else
          {
            monom = 
              SimplifyTerm(_bm->CreateTerm(BVMULT, 
                                           constant.GetValueWidth(), 
                                           constant, it->first));
          }
        if (zero != monom)
          {
            outputvec.push_back(monom);
          }
      } //end of for loop

    if (constkids.size() > 1)
      {
        ASTNode output = 
          _bm->CreateTerm(BVPLUS, 
                          constkids[0].GetValueWidth(), constkids);
        output = BVConstEvaluator(output);
        if (output != zero)
          outputvec.push_back(output);
      }
    else if (constkids.size() == 1)
      {
        if (constkids[0] != zero)
          outputvec.push_back(constkids[0]);
      }

    if (outputvec.size() > 1)
      {
        output = _bm->CreateTerm(BVPLUS, len, outputvec);
      }
    else if (outputvec.size() == 1)
      {
        output = outputvec[0];
      }
    else
      {
        output = zero;
      }

    //memoize
    //UpdateSimplifyMap(a,output,false);
    return output;
  } //end of CombineLikeTerms()

  //accepts lhs and rhs, and returns lhs - rhs = 0. The function
  //assumes that lhs and rhs have already been simplified. although
  //this assumption is not needed for correctness, it is essential for
  //performance. The function also assumes that lhs is a BVPLUS
  ASTNode Simplifier::LhsMinusRhs(const ASTNode& eq)
  {
    //if input is not an equality, simply return it
    if (EQ != eq.GetKind())
      return eq;

    ASTNode lhs = eq[0];
    ASTNode rhs = eq[1];
    Kind k_lhs = lhs.GetKind();
    Kind k_rhs = rhs.GetKind();
    //either the lhs has to be a BVPLUS or the rhs has to be a
    //BVPLUS
    if (!(BVPLUS == k_lhs 
          || BVPLUS == k_rhs 
          || (BVMULT == k_lhs 
              && BVMULT == k_rhs)))
      {
        return eq;
      }

    ASTNode output;
    if (CheckSimplifyMap(eq, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    //if the lhs is not a BVPLUS, but the rhs is a BVPLUS, then swap
    //the lhs and rhs
    bool swap_flag = false;
    if (BVPLUS != k_lhs && BVPLUS == k_rhs)
      {
        ASTNode swap = lhs;
        lhs = rhs;
        rhs = swap;
        swap_flag = true;
      }

    ASTNodeCountMap::const_iterator it;
    it = ReferenceCount->find(lhs);
    if (it != ReferenceCount->end())
      {
        if (it->second > 1)
          return eq;
      }

    unsigned int len = lhs.GetValueWidth();
    ASTNode zero = _bm->CreateZeroConst(len);
    //right is -1*(rhs): Simplify(-1*rhs)
    rhs = SimplifyTerm(_bm->CreateTerm(BVUMINUS, len, rhs));

    ASTVec lvec = lhs.GetChildren();
    ASTVec rvec = rhs.GetChildren();
    ASTNode lhsplusrhs;
    if (BVPLUS != lhs.GetKind() && BVPLUS != rhs.GetKind())
      {
        lhsplusrhs = _bm->CreateTerm(BVPLUS, len, lhs, rhs);
      }
    else if (BVPLUS == lhs.GetKind() && BVPLUS == rhs.GetKind())
      {
        //combine the childnodes of the left and the right
        lvec.insert(lvec.end(), rvec.begin(), rvec.end());
        lhsplusrhs = _bm->CreateTerm(BVPLUS, len, lvec);
      }
    else if (BVPLUS == lhs.GetKind() && BVPLUS != rhs.GetKind())
      {
        lvec.push_back(rhs);
        lhsplusrhs = _bm->CreateTerm(BVPLUS, len, lvec);
      }
    else
      {
        //Control should never reach here
        FatalError("LhsMinusRhs: Control should never reach here\n");
      }

    //combine like terms
    output = CombineLikeTerms(lhsplusrhs);
    output = SimplifyTerm(output);
    //
    //Now make output into: lhs-rhs = 0
    output = CreateSimplifiedEQ(output, zero);
    //sort if BVPLUS
    if (BVPLUS == output.GetKind())
      {
        ASTVec outv = output.GetChildren();
        SortByArith(outv);
        output = _bm->CreateTerm(BVPLUS, len, outv);
      }

    //memoize
    //UpdateSimplifyMap(eq,output,false);
    return output;
  } //end of LhsMinusRHS()

  //THis function accepts a BVMULT(t1,t2) and distributes the mult
  //over plus if either or both t1 and t2 are BVPLUSes.
  //
  // x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
  //
  // (y1 + y2 + ...+ yn)*x <==> x*y1 + x*y2 + ... + x*yn
  //
  // The function assumes that the BVPLUSes have been flattened
  ASTNode Simplifier::DistributeMultOverPlus(const ASTNode& a, 
                                             bool startdistribution)
  {
    if (!startdistribution)
      return a;
    Kind k = a.GetKind();
    if (BVMULT != k)
      return a;

    ASTNode left = a[0];
    ASTNode right = a[1];
    Kind left_kind = left.GetKind();
    Kind right_kind = right.GetKind();

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    //special case optimization: c1*(c2*t1) <==> (c1*c2)*t1
    if (BVCONST == left_kind
        && BVMULT == right_kind 
        && BVCONST == right[0].GetKind())
      {
        ASTNode c = 
          BVConstEvaluator(_bm->CreateTerm(BVMULT, 
                                           a.GetValueWidth(), 
                                           left, right[0]));
        c = _bm->CreateTerm(BVMULT, a.GetValueWidth(), c, right[1]);
        return c;
        left = c[0];
        right = c[1];
        left_kind = left.GetKind();
        right_kind = right.GetKind();
      }

    //special case optimization: c1*(t1*c2) <==> (c1*c2)*t1
    if (BVCONST == left_kind
        && BVMULT == right_kind 
        && BVCONST == right[1].GetKind())
      {
        ASTNode c = 
          BVConstEvaluator(_bm->CreateTerm(BVMULT, 
                                           a.GetValueWidth(), 
                                           left, right[1]));
        c = _bm->CreateTerm(BVMULT, a.GetValueWidth(), c, right[0]);
        return c;
        left = c[0];
        right = c[1];
        left_kind = left.GetKind();
        right_kind = right.GetKind();
      }

    //atleast one of left or right have to be BVPLUS
    if (!(BVPLUS == left_kind || BVPLUS == right_kind))
      {
        return a;
      }

    //if left is BVPLUS and right is not, then swap left and right. we
    //can do this since BVMULT is communtative
    ASTNode swap;
    if (BVPLUS == left_kind && BVPLUS != right_kind)
      {
        swap = left;
        left = right;
        right = swap;
      }
    left_kind = left.GetKind();
    right_kind = right.GetKind();

    //by this point we are gauranteed that right is a BVPLUS, but left
    //may not be
    ASTVec rightnodes = right.GetChildren();
    ASTVec outputvec;
    unsigned len = a.GetValueWidth();
    ASTNode zero = _bm->CreateZeroConst(len);
    ASTNode one = _bm->CreateOneConst(len);
    if (BVPLUS != left_kind)
      {
        //if the multiplier is not a BVPLUS then we have a special case
        // x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
        if (zero == left)
          {
            outputvec.push_back(zero);
          }
        else if (one == left)
          {
            outputvec.push_back(left);
          }
        else
          {
            for (ASTVec::iterator
                   j = rightnodes.begin(), jend = rightnodes.end(); 
                 j != jend; j++)
              {
                ASTNode out = 
                  SimplifyTerm(_bm->CreateTerm(BVMULT, len, left, *j));
                outputvec.push_back(out);
              }
          }
      }
    else
      {
        ASTVec leftnodes = left.GetChildren();
        // (x1 + x2 + ... + xm)*(y1 + y2 + ...+ yn) <==> x1*y1 + x1*y2 +
        // ... + x2*y1 + ... + xm*yn
        for (ASTVec::iterator 
               i = leftnodes.begin(), iend = leftnodes.end(); 
             i != iend; i++)
          {
            ASTNode multiplier = *i;
            for (ASTVec::iterator 
                   j = rightnodes.begin(), jend = rightnodes.end(); 
                 j != jend; j++)
              {
                ASTNode out = 
                  SimplifyTerm(_bm->CreateTerm(BVMULT, len, multiplier, *j));
                outputvec.push_back(out);
              }
          }
      }

    //compute output here
    if (outputvec.size() > 1)
      {
        output = CombineLikeTerms(_bm->CreateTerm(BVPLUS, len, outputvec));
        output = SimplifyTerm(output);
      }
    else
      output = SimplifyTerm(outputvec[0]);

    //memoize
    //UpdateSimplifyMap(a,output,false);
    return output;
  } //end of distributemultoverplus()

  //converts the BVSX(len, a0) operator into ITE( check top bit,
  //extend a0 by 1, extend a0 by 0)
  ASTNode Simplifier::ConvertBVSXToITE(const ASTNode& a)
  {
    if (BVSX != a.GetKind())
      return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of ConvertBVSXToITE Cache: " << output << endl;
        return output;
      }

    ASTNode a0 = a[0];
    unsigned a_len = a.GetValueWidth();
    unsigned a0_len = a0.GetValueWidth();

    if (a0_len > a_len)
      {
        FatalError("Trying to sign_extend a larger BV into a smaller BV");
        return ASTUndefined;
      }

    //sign extend
    unsigned extensionlen = a_len - a0_len;
    if (0 == extensionlen)
      {
        UpdateSimplifyMap(a, output, false);
        return a;
      }

    std::string ones;
    for (unsigned c = 0; c < extensionlen; c++)
      ones += '1';
    std::string zeros;
    for (unsigned c = 0; c < extensionlen; c++)
      zeros += '0';

    //string of oness of length extensionlen
    BEEV::ASTNode BVOnes = _bm->CreateBVConst(ones.c_str(), 2);
    //string of zeros of length extensionlen
    BEEV::ASTNode BVZeros = _bm->CreateBVConst(zeros.c_str(), 2);

    //string of ones BVCONCAT a0
    BEEV::ASTNode concatOnes = 
      _bm->CreateTerm(BEEV::BVCONCAT, a_len, BVOnes, a0);
    //string of zeros BVCONCAT a0
    BEEV::ASTNode concatZeros = 
      _bm->CreateTerm(BEEV::BVCONCAT, a_len, BVZeros, a0);

    //extract top bit of a0
    BEEV::ASTNode hi = _bm->CreateBVConst(32, a0_len - 1);
    BEEV::ASTNode low = _bm->CreateBVConst(32, a0_len - 1);
    BEEV::ASTNode topBit = _bm->CreateTerm(BEEV::BVEXTRACT, 1, a0, hi, low);

    //compare topBit of a0 with 0bin1
    BEEV::ASTNode condition = 
      CreateSimplifiedEQ(_bm->CreateBVConst(1, 1), topBit);

    //ITE(topbit = 0bin1, 0bin1111...a0, 0bin000...a0)
    output = CreateSimplifiedTermITE(condition, concatOnes, concatZeros);
    UpdateSimplifyMap(a, output, false);
    return output;
  } //end of ConvertBVSXToITE()


  ASTNode Simplifier::RemoveWrites_TopLevel(const ASTNode& term)
  {
    if (READ != term.GetKind() || WRITE != term[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    if (!_bm->Begin_RemoveWrites 
        && !_bm->SimplifyWrites_InPlace_Flag 
        && !_bm->start_abstracting)
      {
        return term;
      }
    else if (!_bm->Begin_RemoveWrites 
             && _bm->SimplifyWrites_InPlace_Flag 
             && !_bm->start_abstracting)
      {
        //return term;
        return SimplifyWrites_InPlace(term);
      }
    else
      {
        return RemoveWrites(term);
      }
  } //end of RemoveWrites_TopLevel()

  ASTNode Simplifier::SimplifyWrites_InPlace(const ASTNode& term,
                                             ASTNodeMap* VarConstMap)
  {
    ASTNodeMultiSet WriteIndicesSeenSoFar;
    bool SeenNonConstWriteIndex = false;

    if ((READ != term.GetKind()) 
        || (WRITE != term[0].GetKind()))
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    ASTNode output;
    if (CheckSimplifyMap(term, output, false))
      {
        return output;
      }

    ASTVec writeIndices, writeValues;
    unsigned int width = term.GetValueWidth();
    ASTNode original_write = term[0];
    ASTNode write = term[0];
    unsigned indexwidth = write.GetIndexWidth();
    ASTNode readIndex = SimplifyTerm(term[1]);

    do
      {
        ASTNode writeIndex = SimplifyTerm(write[1]);
        ASTNode writeVal = SimplifyTerm(write[2]);

        //compare the readIndex and the current writeIndex and see if they
        //simplify to TRUE or FALSE or UNDETERMINABLE at this stage
        ASTNode compare_readwrite_indices = 
          SimplifyFormula(CreateSimplifiedEQ(writeIndex, readIndex), 
                          false, VarConstMap);

        //if readIndex and writeIndex are equal
        if (ASTTrue == compare_readwrite_indices && !SeenNonConstWriteIndex)
          {
            UpdateSimplifyMap(term, writeVal, false);
            return writeVal;
          }

        if (!(ASTTrue == compare_readwrite_indices 
              || ASTFalse == compare_readwrite_indices))
          {
            SeenNonConstWriteIndex = true;
          }

        //if (readIndex=writeIndex <=> FALSE)
        if (ASTFalse == compare_readwrite_indices 
            || (WriteIndicesSeenSoFar.find(writeIndex) 
                != WriteIndicesSeenSoFar.end()))
          {
            //drop the current level write
            //do nothing
          }
        else
          {
            writeIndices.push_back(writeIndex);
            writeValues.push_back(writeVal);
          }

        //record the write indices seen so far
        //if(BVCONST == writeIndex.GetKind()) {
        WriteIndicesSeenSoFar.insert(writeIndex);
        //}

        //Setup the write for the new iteration, one level inner write
        write = write[0];
      } while (WRITE == write.GetKind());

    ASTVec::reverse_iterator it_index = writeIndices.rbegin();
    ASTVec::reverse_iterator itend_index = writeIndices.rend();
    ASTVec::reverse_iterator it_values = writeValues.rbegin();
    ASTVec::reverse_iterator itend_values = writeValues.rend();

    // May be a symbol, or an ITE.
    for (; it_index != itend_index; it_index++, it_values++)
      {
        write = _bm->CreateTerm(WRITE, width, write, *it_index, *it_values);
        write.SetIndexWidth(indexwidth);
      }

    output = _bm->CreateTerm(READ, width, write, readIndex);
    assert(BVTypeCheck(output));
    if(ITE == write.GetKind())
      {
	output = SimplifyTerm(output, VarConstMap);
      }

    //UpdateSimplifyMap(original_write, write, false);
    UpdateSimplifyMap(term, output, false);
    return output;
  } //end of SimplifyWrites_In_Place()

  //accepts a read over a write and returns a term without the write
  //READ(WRITE(A i val) j) <==> ITE(i=j,val,READ(A,j)). We use a memo
  //table for this function called RemoveWritesMemoMap
  ASTNode Simplifier::RemoveWrites(const ASTNode& input)
  {
    //unsigned int width = input.GetValueWidth();
    if (READ != input.GetKind() || WRITE != input[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", input);
      }

    ASTNodeMap::iterator it;
    ASTNode output = input;
    if (CheckSimplifyMap(input, output, false))
      {
        return output;
      }

    if (!_bm->start_abstracting 
        && _bm->Begin_RemoveWrites)
      {
        output = ReadOverWrite_To_ITE(input);
      }

    if (_bm->start_abstracting)
      {
        ASTNode newVar;
        if (!CheckSimplifyMap(input, newVar, false))
          {
            newVar = _bm->NewVar(input.GetValueWidth());
            (*ReadOverWrite_NewName_Map)[input] = newVar;
            NewName_ReadOverWrite_Map[newVar] = input;

            UpdateSimplifyMap(input, newVar, false);
            _bm->ASTNodeStats("New Var Name which replace Read_Over_Write: ", 
                              newVar);
          }
        output = newVar;
      } //end of start_abstracting if condition

    //memoize
    UpdateSimplifyMap(input, output, false);
    return output;
  } //end of RemoveWrites()

  ASTNode Simplifier::ReadOverWrite_To_ITE(const ASTNode& term, 
                                           ASTNodeMap* VarConstMap)
  {
    unsigned int width = term.GetValueWidth();
    ASTNode input = term;
    if (READ != term.GetKind() || WRITE != term[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    ASTNodeMap::iterator it;
    ASTNode output;
    // if(CheckSimplifyMap(term,output,false)) {
    //       return output;
    //     }

    ASTNode partialITE = term;
    ASTNode writeA = ASTTrue;
    ASTNode oldRead = term;
    //iteratively expand read-over-write
    do
      {
        ASTNode write = input[0];
        ASTNode readIndex = SimplifyTerm(input[1]);
        //DO NOT CALL SimplifyTerm() on write[0]. You will go into an
        //infinite loop
        writeA = write[0];
        ASTNode writeIndex = SimplifyTerm(write[1]);
        ASTNode writeVal = SimplifyTerm(write[2]);

        ASTNode cond = 
          SimplifyFormula(CreateSimplifiedEQ(writeIndex, readIndex), 
                          false, 
                          VarConstMap);
        ASTNode newRead = _bm->CreateTerm(READ, width, writeA, readIndex);
        ASTNode newRead_memoized = newRead;
        if (CheckSimplifyMap(newRead, newRead_memoized, false))
          {
            newRead = newRead_memoized;
          }

        if (ASTTrue == cond 
            && (term == partialITE))
          {
            //found the write-value in the first iteration
            //itself. return it
            output = writeVal;
            UpdateSimplifyMap(term, output, false);
            return output;
          }

        if (READ == partialITE.GetKind() 
            && WRITE == partialITE[0].GetKind())
          {
            //first iteration or (previous cond==ASTFALSE and
            //partialITE is a "READ over WRITE")
            partialITE = 
              CreateSimplifiedTermITE(cond, writeVal, newRead);
          }
        else if (ITE == partialITE.GetKind())
          {
            //ITE(i1 = j, v1, R(A,j))
            ASTNode ElseITE = 
              CreateSimplifiedTermITE(cond, writeVal, newRead);
            //R(W(A,i1,v1),j) <==> ITE(i1 = j, v1, R(A,j))
            UpdateSimplifyMap(oldRead, ElseITE, false);
            //ITE(i2 = j, v2, R(W(A,i1,v1),j)) <==> ITE(i2 = j, v2,
            //ITE(i1 = j, v1, R(A,j)))
            partialITE = SimplifyTerm(partialITE);
          }
        else
          {
            FatalError("RemoveWrites: Control should not reach here\n");
          }

        if (ASTTrue == cond)
          {
            //no more iterations required
            output = partialITE;
            UpdateSimplifyMap(term, output, false);
            return output;
          }

        input = newRead;
        oldRead = newRead;
      } while (READ == input.GetKind() && WRITE == input[0].GetKind());

    output = partialITE;

    //memoize
    //UpdateSimplifyMap(term,output,false);
    return output;
  } //ReadOverWrite_To_ITE()

  //compute the multiplicative inverse of the input
  ASTNode Simplifier::MultiplicativeInverse(const ASTNode& d)
  {
    ASTNode c = d;
    if (BVCONST != c.GetKind())
      {
        FatalError("Input must be a constant", c);
      }

    if (!BVConstIsOdd(c))
      {
        FatalError("MultiplicativeInverse: Input must be odd: ", c);
      }

    //cerr << "input to multinverse function is: " << d << endl;
    ASTNode inverse;
    if (CheckMultInverseMap(d, inverse))
      {
        //cerr << "found the inverse of: " << d << "and it is: " <<
        //inverse << endl;
        return inverse;
      }

    inverse = c;
    unsigned inputwidth = c.GetValueWidth();

    //Compute the multiplicative inverse of c using the extended
    //euclidian algorithm
    //
    //create a '0' which is 1 bit long
    ASTNode onebit_zero = _bm->CreateZeroConst(1);
    //zero pad t0, i.e. 0 @ t0
    c = 
      BVConstEvaluator(_bm->CreateTerm(BVCONCAT,
                                       inputwidth + 1, onebit_zero, c));

    //construct 2^(inputwidth), i.e. a bitvector of length
    //'inputwidth+1', which is max(inputwidth)+1
    //
    //all 1's
    ASTNode max = _bm->CreateMaxConst(inputwidth);
    //zero pad max
    max = 
      BVConstEvaluator(_bm->CreateTerm(BVCONCAT, 
                                       inputwidth + 1, onebit_zero, max));
    //_bm->Create a '1' which has leading zeros of length 'inputwidth'
    ASTNode inputwidthplusone_one = 
      _bm->CreateOneConst(inputwidth + 1);
    //add 1 to max
    max = 
      _bm->CreateTerm(BVPLUS, inputwidth + 1, max, inputwidthplusone_one);
    max = 
      BVConstEvaluator(max);
    ASTNode zero = _bm->CreateZeroConst(inputwidth + 1);
    ASTNode max_bvgt_0 = _bm->CreateNode(BVGT, max, zero);
    ASTNode quotient, remainder;
    ASTNode x, x1, x2;

    //x1 initialized to zero
    x1 = zero;
    //x2 initialized to one
    x2 = _bm->CreateOneConst(inputwidth + 1);
    while (ASTTrue == BVConstEvaluator(max_bvgt_0))
      {
        //quotient = (c divided by max)
        quotient = 
          BVConstEvaluator(_bm->CreateTerm(BVDIV, 
                                           inputwidth + 1, c, max));

        //remainder of (c divided by max)
        remainder = 
          BVConstEvaluator(_bm->CreateTerm(BVMOD, 
                                           inputwidth + 1, c, max));

        //x = x2 - q*x1
        x = 
          _bm->CreateTerm(BVSUB, 
                          inputwidth + 1, x2, 
                          _bm->CreateTerm(BVMULT, 
                                          inputwidth + 1, 
                                          quotient, x1));
        x = BVConstEvaluator(x);

        //fix the inputs to the extended euclidian algo
        c = max;
        max = remainder;
        max_bvgt_0 = _bm->CreateNode(BVGT, max, zero);

        x2 = x1;
        x1 = x;
      }

    ASTNode hi = _bm->CreateBVConst(32, inputwidth - 1);
    ASTNode low = _bm->CreateZeroConst(32);
    inverse = _bm->CreateTerm(BVEXTRACT, inputwidth, x2, hi, low);
    inverse = BVConstEvaluator(inverse);

    UpdateMultInverseMap(d, inverse);
    //cerr << "output of multinverse function is: " << inverse << endl;
    return inverse;
  } //end of MultiplicativeInverse()

  //returns true if the input is odd
  bool Simplifier::BVConstIsOdd(const ASTNode& c)
  {
    if (BVCONST != c.GetKind())
      {
        FatalError("Input must be a constant", c);
      }

    ASTNode zero = _bm->CreateZeroConst(1);
    ASTNode hi = _bm->CreateZeroConst(32);
    ASTNode low = hi;
    ASTNode lowestbit = _bm->CreateTerm(BVEXTRACT, 1, c, hi, low);
    lowestbit = BVConstEvaluator(lowestbit);

    if (lowestbit == zero)
      {
        return false;
      }
    else
      {
        return true;
      }
  } //end of BVConstIsOdd()
  
  // in ext/hash_map, and tr/unordered_map, there is no provision to
  // shrink down the number of buckets in a hash map. If the hash_map
  // has previously held a lot of data, then it will have a lot of
  // buckets. Slowing down iterators and clears() in particular.
  void Simplifier::ResetSimplifyMaps()
  {
    // clear() is extremely expensive for hash_maps with a lot of
    // buckets, in the EXT_MAP implementation it visits every bucket,
    // checking whether each bucket is empty or not, if non-empty it
    // deletes the contents.  The destructor seems to clear everything
    // anyway.

    //SimplifyMap->clear();
    delete SimplifyMap;
    SimplifyMap = new ASTNodeMap();

    //SimplifyNegMap->clear();
    delete SimplifyNegMap;
    SimplifyNegMap = new ASTNodeMap();

    //ReferenceCount->clear();
    delete ReferenceCount;
    ReferenceCount = new ASTNodeCountMap();
  }

  void Simplifier::printCacheStatus()
  {
    cerr << SimplifyMap->size() << endl;
    cerr << SimplifyNegMap->size() << endl;
    cerr << ReferenceCount->size() << endl;
    //cerr << TermsAlreadySeenMap.size() << endl;
  
    cerr << SimplifyMap->bucket_count() << endl;
    cerr << SimplifyNegMap->bucket_count() << endl;
    cerr << ReferenceCount->bucket_count() << endl;
    //cerr << TermsAlreadySeenMap.bucket_count() << endl;
  } //printCacheStatus()
};//end of namespace

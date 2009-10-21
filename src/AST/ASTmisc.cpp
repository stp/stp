// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "AST.h"

namespace BEEV
{
  
  /****************************************************************
   * Universal Helper Functions                                   *
   ****************************************************************/
  
  void FatalError(const char * str, const ASTNode& a, int w)
  {
    if (a.GetKind() != UNDEFINED)
      {
        cerr << "Fatal Error: " << str << endl << a << endl;
        cerr << w << endl;
      }
    else
      {
        cerr << "Fatal Error: " << str << endl;
        cerr << w << endl;
      }
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    assert(0); // gdb will stop here giving a stacktrace.
    exit(-1);
  }

  void FatalError(const char * str)
  {
    cerr << "Fatal Error: " << str << endl;
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    assert(0);
    exit(-1);

  }
  
  void SortByExprNum(ASTVec& v)
  {
    sort(v.begin(), v.end(), exprless);
  }

  void SortByArith(ASTVec& v)
  {
    sort(v.begin(), v.end(), arithless);
  }

  bool isAtomic(Kind kind)
  {
    if (TRUE == kind  || FALSE == kind || 
        EQ == kind    ||
        BVLT == kind  || BVLE == kind  || 
        BVGT == kind  || BVGE == kind  || 
        BVSLT == kind || BVSLE == kind || 
        BVSGT == kind || BVSGE == kind || 
        SYMBOL == kind || BVGETBIT == kind)
      return true;
    return false;
  }


  // If there is a lot of sharing in the graph, this will take a long
  // time.  it doesn't mark subgraphs as already having been
  // typechecked.
  bool BVTypeCheckRecursive(const ASTNode& n)
  {
    const ASTVec& c = n.GetChildren();

    BVTypeCheck(n);

    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      BVTypeCheckRecursive(*it);

    return true;
  }



  /* FUNCTION: Typechecker for terms and formulas
   *
   * TypeChecker: Assumes that the immediate Children of the input
   * ASTNode have been typechecked. This function is suitable in
   * scenarios like where you are building the ASTNode Tree, and you
   * typecheck as you go along. It is not suitable as a general
   * typechecker.
   *
   * If this returns, this ALWAYS returns true. If there is an error it
   * will call FatalError() and abort.
   */
  bool BVTypeCheck(const ASTNode& n)
  {
    Kind k = n.GetKind();
    //The children of bitvector terms are in turn bitvectors.
    const ASTVec& v = n.GetChildren();
    if (is_Term_kind(k))
      {
        switch (k)
          {
          case BVCONST:
            if (BITVECTOR_TYPE != n.GetType())
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            break;
          case SYMBOL:
            return true;
          case ITE:
            if (BOOLEAN_TYPE != n[0].GetType() || (n[1].GetType() != n[2].GetType()))
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            if (n[1].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            if (n[1].GetIndexWidth() != n[2].GetIndexWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            break;
          case READ:
            if (n.GetChildren().size() !=2)
              FatalError("2 params to read.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              {
                cerr << "Length of indexwidth of array: " << n[0] << " is : " << n[0].GetIndexWidth() << endl;
                cerr << "Length of the actual index is: " << n[1] << " is : " << n[1].GetValueWidth() << endl;
                FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
              }
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            break;
          case WRITE:
            if (n.GetChildren().size() !=3)
              FatalError("3 params to write.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
            if (n[0].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: valuewidth of array != length of actual value in the term t = \n", n);
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            if (BITVECTOR_TYPE != n[2].GetType())
              FatalError("Third parameter to read should be a bitvector", n[2]);

            break;
          case BVOR:
          case BVAND:
          case BVXOR:
          case BVNOR:
          case BVNAND:
          case BVXNOR:
          case BVPLUS:
          case BVMULT:
          case BVDIV:
          case BVMOD:
          case BVSUB:
            {
              if (!(v.size() >= 2))
                FatalError("BVTypeCheck:bitwise Booleans and BV arith operators must have atleast two arguments\n", n);
              unsigned int width = n.GetValueWidth();
              for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
                {
                  if (width != it->GetValueWidth())
                    {
                      cerr << "BVTypeCheck:Operands of bitwise-Booleans and BV arith operators must be of equal length\n";
                      cerr << n << endl;
                      cerr << "width of term:" << width << endl;
                      cerr << "width of offending operand:" << it->GetValueWidth() << endl;
                      FatalError("BVTypeCheck:Offending operand:\n", *it);
                    }
                  if (BITVECTOR_TYPE != it->GetType())
                    FatalError("BVTypeCheck: ChildNodes of bitvector-terms must be bitvectors\n", n);
                }
              break;
            }
          case BVSX:
            //in BVSX(n[0],len), the length of the BVSX term must be
            //greater than the length of n[0]
            if (n[0].GetValueWidth() > n.GetValueWidth())
              {
                FatalError("BVTypeCheck: BVSX(t,bvsx_len) : length of 't' must be <= bvsx_len\n", n);
              }
            if ((v.size() != 2))
              FatalError("BVTypeCheck:BVSX must have two arguments. The second is the new width\n", n);
            break;

          default:
            for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
              if (BITVECTOR_TYPE != it->GetType())
                {
                  cerr << "The type is: " << it->GetType() << endl;
                  FatalError("BVTypeCheck:ChildNodes of bitvector-terms must be bitvectors\n", n);
                }
            break;
          }

        switch (k)
          {
          case BVCONCAT:
            if (n.Degree() != 2)
              FatalError("BVTypeCheck: should have exactly 2 args\n", n);
            if (n.GetValueWidth() != n[0].GetValueWidth() + n[1].GetValueWidth())
              FatalError("BVTypeCheck:BVCONCAT: lengths do not add up\n", n);
            break;
          case BVUMINUS:
          case BVNEG:
            if (n.Degree() != 1)
              FatalError("BVTypeCheck: should have exactly 1 args\n", n);
            break;
          case BVEXTRACT:
            if (n.Degree() != 3)
              FatalError("BVTypeCheck: should have exactly 3 args\n", n);
            if (!(BVCONST == n[1].GetKind() && BVCONST == n[2].GetKind()))
              FatalError("BVTypeCheck: indices should be BVCONST\n", n);
            if (n.GetValueWidth() != GetUnsignedConst(n[1]) - GetUnsignedConst(n[2]) + 1)
              FatalError("BVTypeCheck: length mismatch\n", n);
            if (GetUnsignedConst(n[1]) >= n[0].GetValueWidth())
              FatalError("BVTypeCheck: Top index of select is greater or equal to the bitwidth.\n", n);
            break;
          case BVLEFTSHIFT:
          case BVRIGHTSHIFT:
            if (n.Degree() != 2)
              FatalError("BVTypeCheck: should have exactly 2 args\n", n);
            break;
            //case BVVARSHIFT:
            //case BVSRSHIFT:
            //break;
          default:
            break;
          }
      }
    else
      {
        if (!(is_Form_kind(k) && BOOLEAN_TYPE == n.GetType()))
          FatalError("BVTypeCheck: not a formula:", n);
        switch (k)
          {
          case TRUE:
          case FALSE:
          case SYMBOL:
            return true;
          case PARAMBOOL:
            if(2 != n.Degree())
              FatalError("BVTypeCheck: PARAMBOOL formula can have exactly two childNodes", n);
            break;
          case EQ:
            if (!(n[0].GetValueWidth() == n[1].GetValueWidth() && n[0].GetIndexWidth() == n[1].GetIndexWidth()))
              {
                cerr << "valuewidth of lhs of EQ: " << n[0].GetValueWidth() << endl;
                cerr << "valuewidth of rhs of EQ: " << n[1].GetValueWidth() << endl;
                cerr << "indexwidth of lhs of EQ: " << n[0].GetIndexWidth() << endl;
                cerr << "indexwidth of rhs of EQ: " << n[1].GetIndexWidth() << endl;
                FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
              }
            break;
          case BVLT:
          case BVLE:
          case BVGT:
          case BVGE:
          case BVSLT:
          case BVSLE:
          case BVSGT:
          case BVSGE:
            if (BITVECTOR_TYPE != n[0].GetType() && BITVECTOR_TYPE != n[1].GetType())
              FatalError("BVTypeCheck: terms in atomic formulas must be bitvectors", n);
            if (n[0].GetValueWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            if (n[0].GetIndexWidth() != n[1].GetIndexWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            break;
          case NOT:
            if (1 != n.Degree())
              FatalError("BVTypeCheck: NOT formula can have exactly one childNode", n);
            break;
          case AND:
          case OR:
          case XOR:
          case NAND:
          case NOR:
            if (2 > n.Degree())
              FatalError("BVTypeCheck: AND/OR/XOR/NAND/NOR: must have atleast 2 ChildNodes", n);
            break;
          case IFF:
          case IMPLIES:
            if (2 != n.Degree())
              FatalError("BVTypeCheck:IFF/IMPLIES must have exactly 2 ChildNodes", n);
            break;
          case ITE:
            if (3 != n.Degree())
              FatalError("BVTypeCheck:ITE must have exactly 3 ChildNodes", n);
            break;
          case FOR:
            //FIXME: Todo
            break;
          default:
            
            FatalError("BVTypeCheck: Unrecognized kind: ");
            break;
          }
      }
    return true;
  } //End of TypeCheck function

  //Return the unsigned constant value of the input 'n'
  unsigned int GetUnsignedConst(const ASTNode n)
  {
    if(BVCONST != n.GetKind()){
      FatalError("GetUnsignedConst: cannot extract an "\
                 "unsigned value from a non-bvconst");
    }

    if (sizeof(unsigned int) * 8 <= n.GetValueWidth())
      {
        // It may only contain a small value in a bit type,
        // which fits nicely into an unsigned int.  This is
        // common for functions like: bvshl(bv1[128],
        // bv1[128]) where both operands have the same type.
        signed long maxBit = CONSTANTBV::Set_Max(n.GetBVConst());
        if (maxBit >= ((signed long) sizeof(unsigned int)) * 8)
          {
            n.LispPrint(cerr); //print the node so they can find it.
            FatalError("GetUnsignedConst: cannot convert bvconst "\
                       "of length greater than 32 to unsigned int");
          }
      }
    return (unsigned int) *((unsigned int *) n.GetBVConst());
  } //end of GetUnsignedConst

  //if a is READ(Arr,const) or SYMBOL, and b is BVCONST then return 1
  //if b is READ(Arr,const) or SYMBOL, and a is BVCONST then return -1
  //
  //else return 0 by default
  int TermOrder(const ASTNode& a, const ASTNode& b)
  {
    Kind k1 = a.GetKind();
    Kind k2 = b.GetKind();

    //a is of the form READ(Arr,const), and b is const, or
    //a is of the form var, and b is const
    if ((k1 == READ 
         && a[0].GetKind() == SYMBOL 
         && a[1].GetKind() == BVCONST 
         && (k2 == BVCONST)))
      // || k2 == READ && b[0].GetKind() == SYMBOL && b[1].GetKind()
      // == BVCONST)))
      return 1;

    if (SYMBOL == k1 && (BVCONST == k2 || TRUE == k2 || FALSE == k2))
      return 1;

    //b is of the form READ(Arr,const), and a is const, or
    //b is of the form var, and a is const
    if ((k1 == BVCONST) 
        && ((k2 == READ 
             && b[0].GetKind() == SYMBOL 
             && b[1].GetKind() == BVCONST)))
      return -1;

    if (SYMBOL == k2 
        && (BVCONST == k1 
            || TRUE == k1 
            || FALSE == k1))
      return -1;

    return 0;
  } //End of TermOrder()

};//end of namespace

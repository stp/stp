// -*- c++ -*-
/********************************************************************
 * AUTHORS: David L. Dill, Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <cmath>
#include <cassert>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "BitBlast.h"

namespace BEEV
{
  /********************************************************************
   * BitBlast
   *
   * Convert bitvector terms and formulas to boolean formulas.  A term
   * is something that can represent a multi-bit bitvector, such as
   * BVPLUS or BVXOR (or a BV variable or constant).  A formula (form)
   * represents a boolean value, such as EQ or BVLE.  Bit blasting a
   * term representing an n-bit bitvector with BBTerm yields a vector
   * of n boolean formulas (returning ASTVec).  Bit blasting a formula
   * returns a single boolean formula (type ASTNode).  A bitblasted
   * term is a vector of ASTNodes for formulas.  The 0th element of
   * the vector corresponds to bit 0 -- the low-order bit.
   ********************************************************************/

  const ASTNode BitBlaster::BBTerm(const ASTNode& term)
  {

    //CHANGED TermMemo is now an ASTNodeMap. Based on BBFormMemo
    ASTNodeMap::iterator it = BBTermMemo.find(term);
    if (it != BBTermMemo.end())
      {
        // already there.  Just return it.
        return it->second;
      }

    ASTNode result;

    const Kind k = term.GetKind();
    if (!is_Term_kind(k))
      FatalError("BBTerm: Illegal kind to BBTerm", term);

    ASTVec::const_iterator kids_end = term.end();
    unsigned int num_bits = term.GetValueWidth();
    switch (k)
      {
      case BVNEG:
        {
          // bitwise complement
          // bitblast the child.
          //FIXME Uses a tempory const ASTNode
          const ASTNode& bbkids = BBTerm(term[0]);
          result = _bm->CreateNode(BOOLVEC, BBNeg(bbkids.GetChildren()));
          break;
        }

      case BVRIGHTSHIFT:
      case BVSRSHIFT:
      case BVLEFTSHIFT:
        {
          // Barrel shifter
          const ASTVec& bbarg1 = BBTerm(term[0]).GetChildren();
          const ASTVec& bbarg2 = BBTerm(term[1]).GetChildren();

          // Signed right shift, need to copy the sign bit.
          ASTNode toFill;
          if (BVSRSHIFT == k)
            toFill = bbarg1.back();
          else
            toFill = ASTFalse;

          ASTVec temp_result(bbarg1);
          // if any bit is set in bbarg2 higher than log2Width, then
          // we know that the result is zero.  Add one to make
          // allowance for rounding down. For example, given 300 bits,
          // the log2 is about 8.2 so round up to 9.

          const unsigned width = bbarg1.size();
          unsigned log2Width = (unsigned)log2(width) + 1;


          if (k == BVSRSHIFT || k == BVRIGHTSHIFT)
            {
              for (unsigned int i = 0; i < log2Width; i++)
                {
                  if (bbarg2[i] == ASTFalse)
                    continue; // Not shifting by anything.
                  
                  unsigned int shift_amount = 1 << i;
                  
                  for (unsigned int j = 0; j < width; j++)
                    {
                      if (j + shift_amount >= width)
                        {
                          temp_result[j] = 
                            _bm->CreateSimpForm(ITE, bbarg2[i], 
                                                toFill, temp_result[j]);
                        }
                      else
                        {
                          temp_result[j] = 
                            _bm->CreateSimpForm(ITE, bbarg2[i], 
                                                temp_result[j + shift_amount], 
                                                temp_result[j]);
                        }
                    }
                }
            }
          else
            {
              for (unsigned int i = 0; i < log2Width; i++)
                {
                  if (bbarg2[i] == ASTFalse)
                    continue; // Not shifting by anything.
                  
                  int shift_amount = 1 << i;
                  
                  for (signed int j = width - 1; j >= 0; j--)
                    {
                      if (j < shift_amount)
                        {
                          temp_result[j] = 
                            _bm->CreateSimpForm(ITE, bbarg2[i], 
                                                toFill, temp_result[j]);
                        }
                      else
                        {
                          temp_result[j] = 
                            _bm->CreateSimpForm(ITE, bbarg2[i], 
                                                temp_result[j - shift_amount], 
                                                temp_result[j]);
                        }
                    }
                }
            }
          // If any of the remainder are true. Then the whole thing
          // gets the fill value.
          ASTNode remainder = ASTFalse;
          for (unsigned int i = log2Width; i < width; i++)
            {
              remainder = _bm->CreateNode(OR, remainder, bbarg2[i]);
            }

          for (unsigned int i = 0; i < width; i++)
            {
              temp_result[i] = 
                _bm->CreateSimpForm(ITE, remainder, toFill, temp_result[i]);
            }

          result = _bm->CreateNode(BOOLVEC, temp_result);
        }
        break;
      case BVVARSHIFT:
        FatalError("BBTerm: These kinds have not "\
                   "been implemented in the BitBlaster: ", term);
        break;
      case ITE:
        {
          // Term version of ITE.

          // Blast the args FIXME Uses temporary const ASTNodes and an
          // ASTVec& const ASTNode& cond = BBForm(term[0]);
          const ASTNode& cond = BBForm(term[0]);
          const ASTNode& thn = BBTerm(term[1]);
          const ASTNode& els = BBTerm(term[2]);
          result = 
            _bm->CreateNode(BOOLVEC, 
                            BBITE(cond, thn.GetChildren(), 
                                  els.GetChildren()));
          break;
        }

      case BVSX:
        {
          // Replicate high-order bit as many times as necessary.
          // Arg 0 is expression to be sign extended.
          const ASTNode& arg = term[0];
          unsigned long result_width = term.GetValueWidth();
          unsigned long arg_width = arg.GetValueWidth();
          //FIXME Uses a temporary const ASTNode reference
          const ASTNode& bbarg = BBTerm(arg);

          if (result_width == arg_width)
            {
              //nothing to sign extend
              result = arg;
              break;
            }
          else
            {
              //we need to sign extend
              const ASTNode& msbX = bbarg.back();
              //const ASTNode& msb1 = msbX;

              ASTVec ccc = msbX.GetChildren();
              const ASTNode& msb = _bm->CreateSimpForm(msbX.GetKind(), ccc);

              //  Old version
              //  ASTNode msb = bbarg.back();
              //  const ASTNode msb1 = msb;

              //  ASTVec ccc = msb.GetChildren();
              //  msb = _bm->CreateSimpForm(msb.GetKind(),ccc);

              // DD 1/14/07 Simplify silently drops all but first two
              // args of XOR.  I expanded XOR to N args with
              // flattening optimization.  This bug took 2 days to
              // track down!

              // msb = SimplifyFormula(msb,false);

              // cout << "!!!!!!!!!!!!!!!!" << endl
              // << "Simplify msb:" << msb2 << endl
              // << "Simplify result:" << msb << endl;

              //FIXME Dynamically allocate the result vector?
              //Is this doing multiple copies?
              //ASTVec& tmp_res = *(new ASTVec(result_width));
              ASTVec tmp_res(result_width);

              //FIXME Should these be gotten from result?
              ASTVec::const_iterator bb_it = bbarg.begin();
              ASTVec::iterator res_it = tmp_res.begin();
              // first bit of extended part
              ASTVec::iterator res_ext = res_it + arg_width;
              ASTVec::iterator res_end = tmp_res.end();
              // copy LSBs directly from bbvec
              for (; res_it < res_ext; (res_it++, bb_it++))
                {
                  *res_it = *bb_it;
                }
              // repeat MSB to fill up rest of result.
              for (; res_it < res_end; (res_it++))
                {
                  *res_it = msb;
                }

              //Temporary debugging code
              //    cout << "Sign extending:" << endl
              //                << "  Vec ";
              //    lpvec( bbarg.GetChildren() );
              //    cout << "  Extended to ";
              //    lp(result);
              //    cout << endl;

              result = _bm->CreateNode(BOOLVEC, tmp_res);

              break;
            }
        }

      case BVEXTRACT:
        {
          // bitblast the child, then extract the relevant bits.
          // Note: This could be optimized by not bitblasting the bits
          // that aren't fetched.  But that would be tricky, especially
          // with memo-ization.

          //FIXME Using const ASTNode w/out reference
          /*
            if(weregood){
            printf("spot01\n");
            term[0].LispPrint(cout, 0);
            }
          */
          const ASTNode& bbkids = BBTerm(term[0]);
          /*
            if(weregood){
            printf("spot02, kids:\n");
            bbkids.LispPrint(cout, 0);
            }
          */
          unsigned int high = GetUnsignedConst(term[1]);
          /*
            if(weregood){
            printf("spot03, high: %d\n", high);
            }
          */
          unsigned int low = GetUnsignedConst(term[2]);
          /*
            if(weregood){
            printf("spot04, low: %d\n", low);
            }
          */

          ASTVec::const_iterator bbkfit = bbkids.begin();
          // I should have used pointers to ASTVec, to avoid this crock

          //FIXME _bm->Creates a new local ASTVec and does the
          //_bm->CreateNode from that
          result = 
            _bm->CreateNode(BOOLVEC, ASTVec(bbkfit + low, bbkfit + high + 1));
          /*
            if(weregood){
            printf("spot05\n");
            }
          */
          break;
        }
      case BVCONCAT:
        {
          //FIXME Using temporary const ASTNodes
          const ASTNode& vec1 = BBTerm(term[0]);
          const ASTNode& vec2 = BBTerm(term[1]);

          //FIXME This has to be an unnessecary copy and a memory leak
          //Leaking ASTVec tmp_res = *(new ASTVec(vec2.GetChildren()));
          ASTVec tmp_res(vec2.GetChildren());
          tmp_res.insert(tmp_res.end(), vec1.begin(), vec1.end());
          result = _bm->CreateNode(BOOLVEC, tmp_res);
          break;
        }
      case BVPLUS:
        {
          // ASSERT: at least one child.
          // ASSERT: all children and result are the same size.
          // Previous phase must make sure this is true.
          // Add children pairwise and accumulate in BBsum

          // FIXME: Unnecessary array copies.
          ASTVec::const_iterator it = term.begin();
          ASTVec tmp_res = BBTerm(*it).GetChildren();
          for (++it; it < kids_end; it++)
            {
              const ASTVec& tmp = BBTerm(*it).GetChildren();
              BBPlus2(tmp_res, tmp, ASTFalse);
            }

          result = _bm->CreateNode(BOOLVEC, tmp_res);
          break;
        }
      case BVUMINUS:
        {
          //FIXME Using const ASTNode reference
          const ASTNode& bbkid = BBTerm(term[0]);
          result = _bm->CreateNode(BOOLVEC, BBUminus(bbkid.GetChildren()));
          break;
        }
      case BVSUB:
        {
          // complement of subtrahend
          // copy, since BBSub writes into it.

          ASTVec tmp_res = BBTerm(term[0]).GetChildren();
          const ASTVec& bbkid1 = BBTerm(term[1]).GetChildren();
          BBSub(tmp_res, bbkid1);
          result = _bm->CreateNode(BOOLVEC, tmp_res);
          break;
        }
      case BVMULT:
        {
          // ASSERT 2 arguments, same length, result is same length.

          const ASTNode& t0 = term[0];
          const ASTNode& t1 = term[1];

          const ASTNode& mpcd1 = BBTerm(t0);
          const ASTNode& mpcd2 = BBTerm(t1);
          //Reverese the order of the nodes w/out the need for temporaries
          //This is needed because t0 an t1 must be const
          if ((BVCONST != t0.GetKind()) && (BVCONST == t1.GetKind()))
            {
              result = 
                _bm->CreateNode(BOOLVEC, 
                                BBMult(mpcd2.GetChildren(), 
                                       mpcd1.GetChildren()));
            }
          else
            {
              result = 
                _bm->CreateNode(BOOLVEC, 
                                BBMult(mpcd1.GetChildren(), 
                                       mpcd2.GetChildren()));
            }
          break;
        }
      case BVDIV:
      case BVMOD:
        {
          const ASTNode& dvdd = BBTerm(term[0]);
          const ASTNode& dvsr = BBTerm(term[1]);
          unsigned int width = dvdd.Degree();
          ASTVec q(width);
          ASTVec r(width);
          BBDivMod(dvdd.GetChildren(), dvsr.GetChildren(), q, r, width);
          if (k == BVDIV)
            result = _bm->CreateNode(BOOLVEC, q);
          else
            result = _bm->CreateNode(BOOLVEC, r);
          break;
        }
        //  n-ary bitwise operators.
      case BVXOR:
      case BVXNOR:
      case BVAND:
      case BVOR:
      case BVNOR:
      case BVNAND:
        {
          // Add children pairwise and accumulate in BBsum
          ASTVec::const_iterator it = term.begin();
          Kind bk = UNDEFINED; // Kind of individual bit op.
          switch (k)
            {
            case BVXOR:
              bk = XOR;
              break;
            case BVXNOR:
              bk = IFF;
              break;
            case BVAND:
              bk = AND;
              break;
            case BVOR:
              bk = OR;
              break;
            case BVNOR:
              bk = NOR;
              break;
            case BVNAND:
              bk = NAND;
              break;
            default:
              FatalError("BBTerm: Illegal kind to BBTerm", term);
              break;
            }

          // Sum is destructively modified in the loop, so make a copy
          // of value returned by BBTerm.
          ASTNode temp = BBTerm(*it);
          ASTVec sum(temp.GetChildren()); // First operand.

          // Iterate over remaining bitvector term operands
          for (++it; it < kids_end; it++)
            {
              //FIXME FIXME FIXME: Why does using a temp. var change
              //the behavior?
              temp = BBTerm(*it);
              const ASTVec& y = temp.GetChildren();

              // Iterate over bits
              // FIXME: Why is this not using an iterator???
              int n = y.size();
              for (int i = 0; i < n; i++)
                {
                  sum[i] = _bm->CreateSimpForm(bk, sum[i], y[i]);
                }
            }
          result = _bm->CreateNode(BOOLVEC, sum);
          break;
        }
      case SYMBOL:
        {
          // ASSERT: IndexWidth = 0?  Semantic analysis should check.
          //Leaking ASTVec& bbvec = *(new ASTVec);

          ASTVec bbvec;
          for (unsigned int i = 0; i < num_bits; i++)
            {
              ASTNode bit_node = 
                _bm->CreateNode(BVGETBIT, term, _bm->CreateBVConst(32, i));
              bbvec.push_back(bit_node);
            }
          result = _bm->CreateNode(BOOLVEC, bbvec);
          break;
        }
      case BVCONST:
        {
          ASTVec tmp_res(num_bits);
          CBV bv = term.GetBVConst();
          for (unsigned int i = 0; i < num_bits; i++)
            {
              tmp_res[i] =
                CONSTANTBV::BitVector_bit_test(bv, i) ? ASTTrue : ASTFalse;
            }
          result = _bm->CreateNode(BOOLVEC, tmp_res);
          break;
        }
      case BOOLVEC:
        {
          cerr << "Hit a boolvec! what to do?" << endl;
          break;
        }
      default:
        FatalError("BBTerm: Illegal kind to BBTerm", term);
      }

    assert(!result.IsNull());
    return (BBTermMemo[term] = result);

  }

  // bit blast a formula (boolean term).  Result is one bit wide,
  // so it returns a single ASTNode.
  // FIXME:  Add IsNegated flag.
  const ASTNode BitBlaster::BBForm(const ASTNode& form)
  {
    ASTNodeMap::iterator it = BBFormMemo.find(form);
    if (it != BBFormMemo.end())
      {
        // already there.  Just return it.
        return it->second;
      }

    ASTNode result = ASTUndefined;

    Kind k = form.GetKind();
    if (!is_Form_kind(k))
      {
        FatalError("BBForm: Illegal kind: ", form);
      }

    //  Not returning until end, and memoizing everything, makes it easier
    // to trace coherently.

    // Various special cases
    switch (k)
      {
      case TRUE:
      case FALSE:
        {
          result = form;
          break;
        }

      case SYMBOL:
        //printf("bit-blasting SYMBOL\n");
        if (form.GetType() != BOOLEAN_TYPE)
          {
            FatalError("BBForm: Symbol represents more than one bit", form);
          }

        result = form;
        break;

      case BVGETBIT:
        {
          // exactly two children
          const ASTNode bbchild = BBTerm(form[0]);
          unsigned int index = GetUnsignedConst(form[1]);
          result = bbchild[index];
          break;
        }

      case NOT:
        result = _bm->CreateSimpNot(BBForm(form[0]));
        break;

      case ITE:
        // FIXME: SHould this be _bm->CreateSimpITE?
        result = 
          _bm->CreateNode(ITE, BBForm(form[0]), 
                          BBForm(form[1]), BBForm(form[2]));
        break;

      case AND:
      case OR:
      case NAND:
      case NOR:
      case IFF:
      case XOR:
      case IMPLIES:
        {
          //printf("bit-blasting AND or OR\n");
          ASTVec bbkids; // bit-blasted children (formulas)

          // FIXME: Put in fast exits for AND/OR/NAND/NOR/IMPLIES
          ASTVec::const_iterator kids_end = form.end();
          for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++)
            {
              bbkids.push_back(BBForm(*it));
            }
          result = _bm->CreateSimpForm(k, bbkids);
          break;
        }


      case EQ:
        {
          //printf("bit-blasting EQ\n");
          //form.LispPrint(cout, 0);
          // Common code for binary operations
          // FIXME:  This ought to be in a semantic analysis phase.
          //printf("spot01\n");
          const ASTNode left = BBTerm(form[0]);
          //printf("spot02\n");
          const ASTNode right = BBTerm(form[1]);
          //printf("spot03\n");
          if (left.Degree() != right.Degree())
            {
              cerr << "BBForm: Size mismatch" 
                   << endl << form[0] 
                   << endl << form[1] << endl;
              FatalError("", ASTUndefined);
            }
          result = BBEQ(left.GetChildren(), right.GetChildren());
          //printf("spot04\n");
          break;
        }

      case BVLE:
      case BVGE:
      case BVGT:
      case BVLT:
      case BVSLE:
      case BVSGE:
      case BVSGT:
      case BVSLT:
        {
          result = BBcompare(form);
          break;
        }
      default:
        FatalError("BBForm: Illegal kind: ", form);
        break;
      }

    if(_bm->UserFlags.stats_flag)
      {
        //         cout << "================" << endl
        //              << "BBForm: " << form << endl
        //              << "----------------" << endl
        //              << "BBForm Result: " << result << endl;
      }

    return (BBFormMemo[form] = result);
  }

  // Bit blast a sum of two equal length BVs.
  // Update sum vector destructively with new sum.
  void BitBlaster::BBPlus2(ASTVec& sum, const ASTVec& y, ASTNode cin)
  {
    //   cout << "Bitblasting plus.  Operand 1: " << endl;
    //   lpvec(sum);
    //   cout << endl << " operand 2: " << endl;
    //   lpvec(y);
    //   cout << endl << "carry: " << endl << cin << endl;


    int n = sum.size();
    // ASSERT: y.size() == x.size()
    // FIXME: Don't bother computing i+1 carry, which is discarded.
    for (int i = 0; i < n; i++)
      {
        ASTNode nextcin;
        if(i != n-1) 
          {
            //Compute this only for i=0 to n-2
            nextcin = Majority(sum[i], y[i], cin);
          }
        sum[i] = Sum(sum[i], y[i], cin);        
        if(i != n-1)
          {
            //Compute this only for i=0 to n-2
            cin = nextcin;
          }
      }

    //   cout << "----------------" << endl << "Result: " << endl;
    //   lpvec(sum);
    //   cout << endl;

  }

  // Stores result - x in result, destructively
  void BitBlaster::BBSub(ASTVec& result, const ASTVec& y)
  {
    ASTVec compsubtrahend = BBNeg(y);
    BBPlus2(result, compsubtrahend, ASTTrue);
  }

  // Add one bit
  ASTVec BitBlaster::BBAddOneBit(ASTVec& x, ASTNode cin)
  {
    ASTVec result = ASTVec(0);
    ASTVec::const_iterator itend = x.end();
    for (ASTVec::const_iterator it = x.begin(); it < itend; it++)
      {
        ASTNode nextcin = _bm->CreateSimpForm(AND, *it, cin);
        result.push_back(_bm->CreateSimpForm(XOR, *it, cin));
        cin = nextcin;
      }
    // FIXME: unnecessary array copy on return?
    return result;
  }

  // Increment bit-blasted vector and return result.
  ASTVec BitBlaster::BBInc(ASTVec& x)
  {
    return BBAddOneBit(x, ASTTrue);
  }

  // Return formula for majority function of three bits.
  // Pass arguments by reference to reduce refcounting.
  ASTNode BitBlaster::Majority(const ASTNode& a, 
                               const ASTNode& b, const ASTNode& c)
  {
    // Checking explicitly for constant a, b and c could
    // be more efficient, because they are repeated in the logic.
    if (ASTTrue == a)
      {
        return _bm->CreateSimpForm(OR, b, c);
      }
    else if (ASTFalse == a)
      {
        return _bm->CreateSimpForm(AND, b, c);
      }
    else if (ASTTrue == b)
      {
        return _bm->CreateSimpForm(OR, a, c);
      }
    else if (ASTFalse == b)
      {
        return _bm->CreateSimpForm(AND, a, c);
      }
    else if (ASTTrue == c)
      {
        return _bm->CreateSimpForm(OR, a, b);
      }
    else if (ASTFalse == c)
      {
        return _bm->CreateSimpForm(AND, a, b);
      }
    // there are lots more simplifications, but I'm not sure they're
    // worth doing explicitly (e.g., a = b, a = ~b, etc.)
    else
      {
        //         return _bm->CreateSimpForm(OR, 
        //                                    _bm->CreateSimpForm(AND, a, b), 
        //                                    _bm->CreateSimpForm(AND, b, c), 
        //                                    _bm->CreateSimpForm(AND, a, c));
        return _bm->CreateSimpForm(AND, 
                                   _bm->CreateSimpForm(OR, a, b), 
                                   _bm->CreateSimpForm(OR, b, c), 
                                   _bm->CreateSimpForm(OR, a, c));
      
      }
  }

  ASTNode BitBlaster::Sum(const ASTNode& xi,
                          const ASTNode& yi,
                          const ASTNode& cin)
  {
    // For some unexplained reason, XORs are faster than converting
    // them to cluases at this point
    ASTNode S0 = _bm->CreateSimpForm(XOR, 
                                     _bm->CreateSimpForm(XOR, xi, yi), 
                                     cin);    
    return S0;
    // ASTNode S1 = _bm->CreateSimpForm(OR,xi,yi,cin);
    //     ASTNode S2 = _bm->CreateSimpForm(OR,
    //                               _bm->CreateSimpForm(NOT,xi),
    //                               _bm->CreateSimpForm(NOT,yi),
    //                               cin);
    //     ASTNode S3 = _bm->CreateSimpForm(OR,
    //                               _bm->CreateSimpForm(NOT,xi),
    //                               yi,
    //                               _bm->CreateSimpForm(NOT,cin));
    //     ASTNode S4 = _bm->CreateSimpForm(OR,
    //                               xi,
    //                               _bm->CreateSimpForm(NOT,yi),
    //                               _bm->CreateSimpForm(NOT,cin));
    //     ASTVec S;
    //     S.push_back(S1);
    //     S.push_back(S2);
    //     S.push_back(S3);
    //     S.push_back(S4);
    //     return _bm->CreateSimpForm(AND,S);
  }

  // Bitwise complement
  ASTVec BitBlaster::BBNeg(const ASTVec& x)
  {
    ASTVec result = ASTVec(0); // FIXME: faster to preallocate n entries?
    // Negate each bit.
    ASTVec::const_iterator xend = x.end();
    for (ASTVec::const_iterator it = x.begin(); it < xend; it++)
      {
        result.push_back(_bm->CreateSimpNot(*it));
      }
    // FIXME: unecessary array copy when it returns?
    return result;
  }

  // Compute unary minus
  ASTVec BitBlaster::BBUminus(const ASTVec& x)
  {
    ASTVec xneg = BBNeg(x);
    return BBInc(xneg);
  }

  // Multiply two bitblasted numbers
  ASTVec BitBlaster::BBMult(const ASTVec& x, const ASTVec& y)
  {
    ASTVec ycopy(y);
    ASTVec::const_iterator xend = x.end();
    ASTVec::const_iterator xit = x.begin();
    // start prod with first partial product.
    // FIXME: This is unnecessary. Clean it up.
    ASTVec prod = ASTVec(BBAndBit(y, *xit));
    // start loop at next bit.
    for (xit++; xit < xend; xit++)
      {
        // shift first
        BBLShift(ycopy,1);

        if (ASTFalse == *xit)
          {
            // If this bit is zero, the partial product will
            // be zero.  No reason to add that in.
            continue;
          }

        ASTVec pprod = BBAndBit(ycopy, *xit);
        // accumulate in the product.
        BBPlus2(prod, pprod, ASTFalse);
      }
    return prod;
  }

  // This implements a variant of binary long division.
  // q and r are "out" parameters.  rwidth puts a bound on the
  // recursion depth.
  void BitBlaster::BBDivMod(const ASTVec &y, const ASTVec &x, 
                            ASTVec &q, ASTVec &r, unsigned int rwidth)
  {
    unsigned int width = y.size();
    if (rwidth == 0)
      {
        // When we have shifted the entire width, y is guaranteed to be 0.
        q = BBfill(width, ASTFalse);
        r = BBfill(width, ASTFalse);
      }
    else
      {
        ASTVec q1, r1;
        ASTVec yrshift1(y);
        BBRShift(yrshift1,1);

        // recursively divide y/2 by x.
        BBDivMod(yrshift1, x, q1, r1, rwidth - 1);

        ASTVec q1lshift1(q1);
        BBLShift(q1lshift1,1);

        ASTVec r1lshift1(r1);
        BBLShift(r1lshift1,1);

        ASTVec r1lshift1plusyodd = BBAddOneBit(r1lshift1, y[0]);
        ASTVec rminusx(r1lshift1plusyodd);
        BBSub(rminusx, x);

        // Adjusted q, r values when when r is too large.
        ASTNode rtoolarge = BBBVLE(x, r1lshift1plusyodd, false);
        ASTVec ygtrxqval = BBITE(rtoolarge, BBInc(q1lshift1), q1lshift1);
        ASTVec ygtrxrval = BBITE(rtoolarge, rminusx, r1lshift1plusyodd);

        // q & r values when y >= x
        ASTNode yeqx = BBEQ(y, x);
        // *** Problem: the bbfill for qval is wrong.  Should be 1, not -1.
        ASTVec one = BBfill(width, ASTFalse);
        one[0] = ASTTrue;
        ASTVec notylessxqval = BBITE(yeqx, one, ygtrxqval);
        ASTVec notylessxrval = BBITE(yeqx, BBfill(width, ASTFalse), ygtrxrval);
        // y < x <=> not x >= y.
        ASTNode ylessx = _bm->CreateSimpNot(BBBVLE(x, y, false));
        // final values of q and r
        q = BBITE(ylessx, BBfill(width, ASTFalse), notylessxqval);
        r = BBITE(ylessx, y, notylessxrval);
      }
  }

  // build ITE's (ITE cond then[i] else[i]) for each i.
  ASTVec BitBlaster::BBITE(const ASTNode& cond, 
                           const ASTVec& thn, 
                           const ASTVec& els)
  {
    // Fast exits.
    if (ASTTrue == cond)
      {
        return thn;
      }
    else if (ASTFalse == cond)
      {
        return els;
      }

    ASTVec result(0);
    ASTVec::const_iterator th_it_end = thn.end();
    ASTVec::const_iterator el_it = els.begin();
    for (ASTVec::const_iterator 
           th_it = thn.begin(); th_it < th_it_end; th_it++, el_it++)
      {
        result.push_back(_bm->CreateSimpForm(ITE, cond, *th_it, *el_it));
      }
    return result;
  }
  // AND each bit of vector y with single bit b and return the result.
  ASTVec BitBlaster::BBAndBit(const ASTVec& y, ASTNode b)
  {
    ASTVec result(0);

    if (ASTTrue == b)
      {
        return y;
      }
    // FIXME: put in fast exits when b is constant 0.

    ASTVec::const_iterator yend = y.end();
    for (ASTVec::const_iterator yit = y.begin(); yit < yend; yit++)
      {
        result.push_back(_bm->CreateSimpForm(AND, *yit, b));
      }
    return result;
  }

  // Workhorse for comparison routines.  This does a signed BVLE if
  // is_signed is true, else it's unsigned.  All other comparison
  // operators can be reduced to this by swapping args or
  // complementing the result bit.
  ASTNode BitBlaster::BBBVLE(const ASTVec& left, 
                             const ASTVec& right,
                             bool is_signed,
                             bool is_bvlt)
  {
    ASTVec::const_reverse_iterator lit    = left.rbegin();
    ASTVec::const_reverse_iterator litend = left.rend();
    ASTVec::const_reverse_iterator rit    = right.rbegin();    

    ASTNode this_compare_bit = 
      is_signed ?
      _bm->CreateSimpForm(AND, *lit, _bm->CreateSimpNot(*rit)):
      _bm->CreateSimpForm(AND, _bm->CreateSimpNot(*lit), *rit);

    ASTVec bit_comparisons;
    bit_comparisons.push_back(this_compare_bit);
    
    ASTNode prev_eq_bit = _bm->CreateSimpForm(IFF, *lit, *rit);
    for(lit++, rit++; lit < litend; lit++, rit++)
      {
        this_compare_bit = 
          _bm->CreateSimpForm(AND, _bm->CreateSimpNot(*lit), *rit);

        ASTNode thisbit_output = 
          _bm->CreateSimpForm(AND, this_compare_bit, prev_eq_bit);
        bit_comparisons.push_back(thisbit_output);

        // (neg(lit) OR rit)(lit OR neg(rit))
        ASTNode this_eq_bit = 
          _bm->CreateSimpForm(AND,
                              _bm->CreateSimpForm(IFF,*lit,*rit),
                              prev_eq_bit);
        prev_eq_bit = this_eq_bit;
      }
    
    if(!is_bvlt)
      {
        bit_comparisons.push_back(prev_eq_bit);
      }
    ASTNode output =
      _bm->CreateSimpForm(OR, bit_comparisons);

    return output;
    //     // "thisbit" represents BVLE of the suffixes of the BVs
    //     // from that position .  if R < L, return TRUE, else if L < R
    //     // return FALSE, else return BVLE of lower-order bits.  MSB is
    //     // treated separately, because signed comparison is done by
    //     // complementing the MSB of each BV, then doing an unsigned
    //     // comparison.    
    //     ASTVec::const_iterator lit = left.rbegin();
    //     ASTVec::const_iterator litend = left.rend();
    //     ASTVec::const_iterator rit = right.rbegin();
    //     ASTNode prevbit = ASTTrue;
    //     for (; lit < litend - 1; lit++, rit++)
    //       {
    //         ASTNode neglit = _bm->CreateSimpNot(*lit);
    //         ASTNode thisbit = 
    //           _bm->CreateSimpForm(OR, 
    //                               _bm->CreateSimpForm(AND, neglit, *rit),
    //                               _bm->CreateSimpForm(AND, 
    //                                                   _bm->CreateSimpForm(OR, 
    //                                                                       neglit,
    //                                                                       *rit), 
    //                                                   prevbit));    
    //         prevbit = thisbit;
    //       }

    //     // Handle MSB -- negate MSBs if signed comparison
    //     // FIXME: make into refs after it's debugged.
    //     ASTNode lmsb = *lit;
    //     ASTNode rmsb = *rit;
    //     if (is_signed)
    //       {
    //         lmsb = _bm->CreateSimpNot(*lit);
    //         rmsb = _bm->CreateSimpNot(*rit);
    //       }

    //     ASTNode neglmsb = _bm->CreateSimpNot(lmsb);
    //     ASTNode msb = 
    //       // TRUE if l < r
    //       _bm->CreateSimpForm(OR, _bm->CreateSimpForm(AND, neglmsb, rmsb), 
    //                           _bm->CreateSimpForm(AND, 
    //                                               _bm->CreateSimpForm(OR, 
    //                                                                   neglmsb,
    //                                                                   rmsb),
    //                                               prevbit)); // else prevbit
    //     return msb;
  }

  // Left shift  within fixed field inserting zeros at LSB.
  // Writes result into first argument.
  void BitBlaster::BBLShift(ASTVec& x, unsigned int shift)
  {
    // left shift x (destructively) within width.  loop backwards so
    // that copy to self works correctly. (DON'T use STL insert!)
    ASTVec::iterator xbeg = x.begin();
    ASTVec::iterator xit = x.end() - 1;
    for (; xit >= xbeg; xit--)
      {
        if (xit - shift >= xbeg)
          *xit = *(xit - shift);
        else
          *xit = ASTFalse; // new LSB is zero.
      }
  }

  // Right shift within fixed field inserting zeros at MSB.
  // Writes result into first argument.
  void BitBlaster::BBRShift(ASTVec& x, unsigned int shift)
  {
    // right shift x (destructively) within width.
    ASTVec::iterator xend = x.end();
    ASTVec::iterator xit = x.begin();
    for (; xit < xend; xit++)
      {
        if (xit + shift < xend)
          *xit = *(xit + shift);
        else
          *xit = ASTFalse; // new MSB is zero.
      }
  }

  // Right shift within fixed field copying the MSB.
  // Writes result into first argument.
  void BitBlaster::BBRSignedShift(ASTVec& x, unsigned int shift)
  {
    // right shift x (destructively) within width.
    ASTNode & MSB = x.back();
    ASTVec::iterator xend = x.end();
    ASTVec::iterator xit = x.begin();
    for (; xit < xend; xit++)
      {
        if (xit + shift < xend)
          *xit = *(xit + shift);
        else
          *xit = MSB; // new MSB is zero.
      }
  }

  // Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
  ASTNode BitBlaster::BBcompare(const ASTNode& form)
  {
    const ASTNode lnode = BBTerm(form[0]);
    const ASTNode rnode = BBTerm(form[1]);
    const ASTVec& left = lnode.GetChildren();
    const ASTVec& right = rnode.GetChildren();

    //const ASTVec& left = BBTerm(form[0]).GetChildren();
    //const ASTVec& right = BBTerm(form[1]).GetChildren();

    Kind k = form.GetKind();
    switch (k)
      {
      case BVLE:
        {
          return BBBVLE(left, right, false);
          break;
        }
      case BVGE:
        {
          return BBBVLE(right, left, false);
          break;
        }
      case BVGT:
        {
          return _bm->CreateSimpNot(BBBVLE(left, right, false));
          break;
        }
      case BVLT:
        {
          return BBBVLE(left, right, false, true);
          break;
        }
      case BVSLE:
        {
          return BBBVLE(left, right, true);
          break;
        }
      case BVSGE:
        {
          return BBBVLE(right, left, true);
          break;
        }
      case BVSGT:
        {
          return _bm->CreateSimpNot(BBBVLE(left, right, true));
          break;
        }
      case BVSLT:
        {
          return _bm->CreateSimpNot(BBBVLE(right, left, true));
          break;
        }
      default:
        cerr << "BBCompare: Illegal kind" << form << endl;
        FatalError("", ASTUndefined);
      }
    return ASTUndefined;
  }

  // return a vector with n copies of fillval
  ASTVec BitBlaster::BBfill(unsigned int width, ASTNode fillval)
  {
    ASTVec zvec(width, fillval);
    return zvec;
  }

  ASTNode BitBlaster::BBEQ(const ASTVec& left, const ASTVec& right)
  {
    ASTVec andvec;
    ASTVec::const_iterator lit = left.begin();
    ASTVec::const_iterator litend = left.end();
    ASTVec::const_iterator rit = right.begin();

    if (left.size() > 1)
      {
        for (; lit != litend; lit++, rit++)
          {
            ASTNode biteq = _bm->CreateSimpForm(IFF, *lit, *rit);
            // fast path exit
            if (biteq == ASTFalse)
              {
                return ASTFalse;
              }
            else
              {
                andvec.push_back(biteq);
              }
          }
        ASTNode n = _bm->CreateSimpForm(AND, andvec);
        return n;
      }
    else
      return _bm->CreateSimpForm(IFF, *lit, *rit);
  }
} // BEEV namespace

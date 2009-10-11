// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef BITBLAST_H
#define BITBLAST_H

#include <cmath>
#include <cassert>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
  class BitBlaster {
  private:
    /****************************************************************
     * Private Data                                                 *
     ****************************************************************/
    STPMgr * _bm;
    ASTNode ASTTrue, ASTFalse, ASTUndefined;
    
    // Memo table for bit blasted terms.  If a node has already been
    // bitblasted, it is mapped to a vector of Boolean formulas for
    // the
    ASTNodeMap BBTermMemo;

    // Memo table for bit blasted formulas.  If a node has already
    // been bitblasted, it is mapped to a node representing the
    // bitblasted equivalent
    ASTNodeMap BBFormMemo;

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/

    // Get vector of Boolean formulas for sum of two
    // vectors of Boolean formulas
    void BBPlus2(ASTVec& sum, const ASTVec& y, ASTNode cin);
    
    // Increment
    ASTVec BBInc(ASTVec& x);
    
    // Add one bit to a vector of bits.
    ASTVec BBAddOneBit(ASTVec& x, ASTNode cin);
    
    // Bitwise complement
    ASTVec BBNeg(const ASTVec& x);
    
    // Unary minus
    ASTVec BBUminus(const ASTVec& x);
    
    // Multiply.
    ASTVec BBMult(const ASTVec& x, const ASTVec& y);
    
    // AND each bit of vector y with single bit b and return the result.
    // (used in BBMult)
    ASTVec BBAndBit(const ASTVec& y, ASTNode b);
    
    // Returns ASTVec for result - y.  This destroys "result".
    void BBSub(ASTVec& result, const ASTVec& y);
    
    // build ITE's (ITE cond then[i] else[i]) for each i.
    ASTVec BBITE(const ASTNode& cond, const ASTVec& thn, const ASTVec& els);
    
    // Build a vector of zeros.
    ASTVec BBfill(unsigned int width, ASTNode fillval);
    
    // build an EQ formula
    ASTNode BBEQ(const ASTVec& left, const ASTVec& right);

    // This implements a variant of binary long division.
    // q and r are "out" parameters.  rwidth puts a bound on the
    // recursion depth.   Unsigned only, for now.
    void BBDivMod(const ASTVec &y, const ASTVec &x, 
		  ASTVec &q, ASTVec &r, unsigned int rwidth);

    // Return formula for majority function of three formulas.
    ASTNode Majority(const ASTNode& a, const ASTNode& b, const ASTNode& c);

    // Internal bit blasting routines.
    ASTNode BBBVLE(const ASTVec& x, const ASTVec& y, bool is_signed);

    // Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
    ASTNode BBcompare(const ASTNode& form);

    void BBRSignedShift(ASTVec& x, unsigned int shift);
    void BBLShift(ASTVec& x, unsigned int shift);
    void BBRShift(ASTVec& x, unsigned int shift);

  public:

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/
    
    BitBlaster(STPMgr * bm) : _bm(bm) 
    {
      ASTTrue = _bm->CreateNode(TRUE);
      ASTFalse = _bm->CreateNode(FALSE);
      ASTUndefined = _bm->CreateNode(UNDEFINED);
    }

    ~BitBlaster()
    {
    }
    

    // Adds or removes a NOT as necessary to negate a literal.
    ASTNode Negate(const ASTNode& form);

    // Bit blast a bitvector term.  The term must have a kind for a
    // bitvector term.  Result is a ref to a vector of formula nodes
    // representing the boolean formula.
    const ASTNode BBTerm(const ASTNode& term);

    //Bitblast a formula
    const ASTNode BBForm(const ASTNode& formula);

  }; //end of class BitBlaster
}; //end of namespace
#endif

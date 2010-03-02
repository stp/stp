// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef BITBLASTNEW_H
#define BITBLASTNEW_H

#include <cmath>
#include <cassert>
#include "../AST/AST.h"
#include "BBNodeManager.h"
#include "../STPManager/STPManager.h"

namespace BEEV {
class BitBlasterNew;

class BitBlasterNew {

	// Memo table for bit blasted terms.  If a node has already been
	// bitblasted, it is mapped to a vector of Boolean formulas for
	// the
	BBNodeVecMap BBTermMemo;

	// Memo table for bit blasted formulas.  If a node has already
	// been bitblasted, it is mapped to a node representing the
	// bitblasted equivalent
	BBNodeMap BBFormMemo;

	STPMgr * _bm;
	ASTNode ASTTrue, ASTFalse, ASTUndefined;

	/****************************************************************
	 * Private Member Functions                                     *
	 ****************************************************************/

	// Get vector of Boolean formulas for sum of two
	// vectors of Boolean formulas
	void BBPlus2(BBNodeVec& sum, const BBNodeVec& y, BBNode cin);

	// Increment
	BBNodeVec BBInc(BBNodeVec& x);

	// Add one bit to a vector of bits.
	BBNodeVec BBAddOneBit(BBNodeVec& x, BBNode cin);

	// Bitwise complement
	BBNodeVec BBNeg(const BBNodeVec& x);

	// Unary minus
	BBNodeVec BBUminus(const BBNodeVec& x);

	// Multiply.
	ASTVec BBMult(const BBNodeVec& x, const BBNodeVec& y, BBNodeSet& support);

	BBNodeVec BBAndBit(const BBNodeVec& y, BBNode b);

	// AND each bit of vector y with single bit b and return the result.
	// (used in BBMult)
	//BBNodeVec BBAndBit(const BBNodeVec& y, ASTNode b);

	// Returns BBNodeVec for result - y.  This destroys "result".
	void BBSub(BBNodeVec& result, const BBNodeVec& y, BBNodeSet& support);

	// build ITE's (ITE cond then[i] else[i]) for each i.
	BBNodeVec BBITE(const BBNode& cond, const BBNodeVec& thn,
			const BBNodeVec& els);

	// Build a vector of zeros.
	BBNodeVec BBfill(unsigned int width, BBNode fillval);

	// build an EQ formula
	BBNode BBEQ(const BBNodeVec& left, const BBNodeVec& right);

	// This implements a variant of binary long division.
	// q and r are "out" parameters.  rwidth puts a bound on the
	// recursion depth.   Unsigned only, for now.
	void BBDivMod(const BBNodeVec &y, const BBNodeVec &x, BBNodeVec &q,
			BBNodeVec &r, unsigned int rwidth, BBNodeSet& support);

	// Return formula for majority function of three formulas.
	BBNode Majority(const BBNode& a, const BBNode& b, const BBNode& c);

	// Internal bit blasting routines.
	BBNode BBBVLE(const BBNodeVec& x, const BBNodeVec& y, bool is_signed,
			bool is_bvlt = false);

	// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
	BBNode BBcompare(const ASTNode& form, BBNodeSet& support);

	void BBLShift(BBNodeVec& x, unsigned int shift);
	void BBRShift(BBNodeVec& x, unsigned int shift);

	BBNodeManager* nf;

	// Bit blast a bitvector term.  The term must have a kind for a
	// bitvector term.  Result is a ref to a vector of formula nodes
	// representing the boolean formula.
	const BBNodeVec BBTerm(const ASTNode& term, BBNodeSet& support);

public:

	/****************************************************************
	 * Public Member Functions                                      *
	 ****************************************************************/

	BitBlasterNew(STPMgr * bm) :
		_bm(bm) {
		ASTTrue = _bm->CreateNode(TRUE);
		ASTFalse = _bm->CreateNode(FALSE);
		ASTUndefined = _bm->CreateNode(UNDEFINED);
		nf = new BBNodeManager(bm);
	}

	~BitBlasterNew() {
		BBTermMemo.clear();
		BBFormMemo.clear();
		delete nf;
	}

	//Bitblast a formula
	const BBNode BBForm(const ASTNode& form, BBNodeSet& support);

}; //end of class BitBlaster
}
; //end of namespace
#endif

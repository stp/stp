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
#include <map>
#include "../STPManager/STPManager.h"

namespace BEEV {

class ASTNode;
typedef std::vector<ASTNode> ASTVec;

template <class BBNode, class BBNodeManagerT> class BitBlaster;

template <class BBNode, class BBNodeManagerT>
class BitBlaster {
private:
	// Memo table for bit blasted terms.  If a node has already been
	// bitblasted, it is mapped to a vector of Boolean formulas for
	// the
        std::map<ASTNode, vector<BBNode> > BBTermMemo;

	// Memo table for bit blasted formulas.  If a node has already
	// been bitblasted, it is mapped to a node representing the
	// bitblasted equivalent
	map<ASTNode, BBNode> BBFormMemo;

	/****************************************************************
	 * Private Member Functions                                     *
	 ****************************************************************/

	// Get vector of Boolean formulas for sum of two
	// vectors of Boolean formulas
	void BBPlus2(vector<BBNode>& sum, const vector<BBNode>& y, BBNode cin);

	// Increment
	vector<BBNode> BBInc(const vector<BBNode>& x);

	// Add one bit to a vector of bits.
	vector<BBNode> BBAddOneBit(const vector<BBNode>& x, BBNode cin);

	// Bitwise complement
	vector<BBNode> BBNeg(const vector<BBNode>& x);

	// Unary minus
	vector<BBNode> BBUminus(const vector<BBNode>& x);

	// Multiply.
	vector<BBNode> BBMult(const vector<BBNode>& x, const vector<BBNode>& y,
			set<BBNode>& support, const ASTNode& xN, const ASTNode& yN);
	void mult_allPairs(const vector<BBNode>& x, const vector<BBNode>& y, set<BBNode>& support, stack<BBNode> * products);
	void mult_Booth(const vector<BBNode>& x_i, const vector<BBNode>& y_i, set<BBNode>& support, const BEEV::ASTNode& xN, const BEEV::ASTNode& yN, stack<BBNode> * products);
	vector<BBNode> mult_normal(const vector<BBNode>& x,	const vector<BBNode>& y, set<BBNode>& support);


	vector<BBNode> pairWiseAdd(stack<BBNode>* products,
			const int bitWidth);


	vector<BBNode> BBAndBit(const vector<BBNode>& y, BBNode b);

	// AND each bit of vector y with single bit b and return the result.
	// (used in BBMult)
	//vector<BBNode> BBAndBit(const vector<BBNode>& y, ASTNode b);

	// Returns vector<BBNode> for result - y.  This destroys "result".
	void BBSub(vector<BBNode>& result, const vector<BBNode>& y, set<BBNode>& support);

	// build ITE's (ITE cond then[i] else[i]) for each i.
	vector<BBNode> BBITE(const BBNode& cond, const vector<BBNode>& thn,
			const vector<BBNode>& els);

	// Build a vector of zeros.
	vector<BBNode> BBfill(unsigned int width, BBNode fillval);

	// build an EQ formula
	BBNode BBEQ(const vector<BBNode>& left, const vector<BBNode>& right);

	// This implements a variant of binary long division.
	// q and r are "out" parameters.  rwidth puts a bound on the
	// recursion depth.   Unsigned only, for now.
public:
	void BBDivMod(const vector<BBNode> &y, const vector<BBNode> &x, vector<BBNode> &q,
			vector<BBNode> &r, unsigned int rwidth, set<BBNode>& support);

	// Return formula for majority function of three formulas.
	BBNode Majority(const BBNode& a, const BBNode& b, const BBNode& c);

	// Internal bit blasting routines.
	BBNode BBBVLE(const vector<BBNode>& x, const vector<BBNode>& y, bool is_signed,
			bool is_bvlt = false);

	// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
	BBNode BBcompare(const ASTNode& form, set<BBNode>& support);

	void BBLShift(vector<BBNode>& x, unsigned int shift);
	void BBRShift(vector<BBNode>& x, unsigned int shift);

public:
	BBNodeManagerT* nf;

	// Bit blast a bitvector term.  The term must have a kind for a
	// bitvector term.  Result is a ref to a vector of formula nodes
	// representing the boolean formula.
	const vector<BBNode> BBTerm(const ASTNode& term, set<BBNode>& support);

public:

	/****************************************************************
	 * Public Member Functions                                      *
	 ****************************************************************/

	BitBlaster(STPMgr * bm)
		{
		nf = new BBNodeManagerT(bm);
	}

	~BitBlaster() {
		BBTermMemo.clear();
		BBFormMemo.clear();
		delete nf;
	}

	//Bitblast a formula
	const BBNode BBForm(const ASTNode& form, set<BBNode>& support);

}; //end of class BitBlaster
}
; //end of namespace
#endif

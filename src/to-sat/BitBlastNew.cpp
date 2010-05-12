/********************************************************************
 * AUTHORS: David L. Dill, Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include <cmath>
#include <cassert>
#include "BitBlastNew.h"
#include "../AST/AST.h"

namespace BEEV {

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

BBNodeVec _empty_BBNodeVec;

// Bit blast a bitvector term.  The term must have a kind for a
// bitvector term.  Result is a ref to a vector of formula nodes
// representing the boolean formula.


const BBNodeVec BitBlasterNew::BBTerm(const ASTNode& term, BBNodeSet& support) {
	BBNodeVecMap::iterator it = BBTermMemo.find(term);
	if (it != BBTermMemo.end()) {
		// already there.  Just return it.
		return it->second;
	}

	BBNodeVec result;

	const Kind k = term.GetKind();
	if (!is_Term_kind(k))
		FatalError("BBTerm: Illegal kind to BBTerm", term);

	const ASTVec::const_iterator kids_end = term.end();
	const unsigned int num_bits = term.GetValueWidth();
	switch (k) {
	case BVNEG: {
		// bitwise complement
		const BBNodeVec& bbkids = BBTerm(term[0], support);
		result = BBNeg(bbkids);
		break;
	}

	case BVRIGHTSHIFT:
	case BVSRSHIFT:
	case BVLEFTSHIFT: {
		// Barrel shifter
		const BBNodeVec& bbarg1 = BBTerm(term[0], support);
		const BBNodeVec& bbarg2 = BBTerm(term[1], support);

		// Signed right shift, need to copy the sign bit.
		BBNode toFill;
		if (BVSRSHIFT == k)
			toFill = bbarg1.back();
		else
			toFill = nf->getFalse();

		BBNodeVec temp_result(bbarg1);
		// if any bit is set in bbarg2 higher than log2Width, then we know that the result is zero.
		// Add one to make allowance for rounding down. For example, given 300 bits, the log2 is about
		// 8.2 so round up to 9.

		const unsigned width = bbarg1.size();
		const unsigned log2Width = (unsigned) log2(width) + 1;

		if (k == BVSRSHIFT || k == BVRIGHTSHIFT)
			for (unsigned int i = 0; i < log2Width; i++) {
				if (bbarg2[i] == nf->getFalse())
					continue; // Not shifting by anything.

				unsigned int shift_amount = 1 << i;

				for (unsigned int j = 0; j < width; j++) {
					if (j + shift_amount >= width)
						temp_result[j] = nf->CreateNode(ITE, bbarg2[i], toFill,
								temp_result[j]);
					else
						temp_result[j] = nf->CreateNode(ITE, bbarg2[i],
								temp_result[j + shift_amount], temp_result[j]);
				}
			}
		else
			for (unsigned int i = 0; i < log2Width; i++) {
				if (bbarg2[i] == nf->getFalse())
					continue; // Not shifting by anything.

				int shift_amount = 1 << i;

				for (signed int j = width - 1; j >= 0; j--) {
					if (j < shift_amount)
						temp_result[j] = nf->CreateNode(ITE, bbarg2[i], toFill,
								temp_result[j]);
					else
						temp_result[j] = nf->CreateNode(ITE, bbarg2[i],
								temp_result[j - shift_amount], temp_result[j]);
				}
			}

		// If any of the remainder are true. Then the whole thing gets the fill value.
		BBNode remainder = nf->getFalse();
		for (unsigned int i = log2Width; i < width; i++) {
			remainder = nf->CreateNode(OR, remainder, bbarg2[i]);
		}

		for (unsigned int i = 0; i < width; i++) {
			temp_result[i] = nf->CreateNode(ITE, remainder, toFill,
					temp_result[i]);
		}

		result = temp_result;
	}
		break;

	case ITE: {
		// Term version of ITE.
		const BBNode& cond = BBForm(term[0], support);
		const BBNodeVec& thn = BBTerm(term[1], support);
		const BBNodeVec& els = BBTerm(term[2], support);
		result = BBITE(cond, thn, els);
		break;
	}

	case BVSX: {
		// Replicate high-order bit as many times as necessary.
		// Arg 0 is expression to be sign extended.
		const ASTNode& arg = term[0];
		const unsigned long result_width = term.GetValueWidth();
		const unsigned long arg_width = arg.GetValueWidth();
		const BBNodeVec& bbarg = BBTerm(arg, support);

		if (result_width == arg_width) {
			//nothing to sign extend
			result = bbarg;
			break;
		} else {
			//we need to sign extend
			const BBNode& msb = bbarg.back();

			BBNodeVec tmp_res(result_width);

			BBNodeVec::const_iterator bb_it = bbarg.begin();
			BBNodeVec::iterator res_it = tmp_res.begin();
			BBNodeVec::iterator res_ext = res_it + arg_width; // first bit of extended part
			BBNodeVec::iterator res_end = tmp_res.end();

			// copy LSBs directly from bbvec
			for (; res_it < res_ext; (res_it++, bb_it++)) {
				*res_it = *bb_it;
			}
			// repeat MSB to fill up rest of result.
			for (; res_it < res_end; (res_it++)) {
				*res_it = msb;
			}

			result = tmp_res;
			break;
		}
	}

	case BVEXTRACT: {
		// bitblast the child, then extract the relevant bits.
		// Note: This could be optimized by not bitblasting the bits
		// that aren't fetched.  But that would be tricky, especially
		// with memo-ization.

		const BBNodeVec& bbkids = BBTerm(term[0], support);
		const unsigned int high = GetUnsignedConst(term[1]);
		const unsigned int low = GetUnsignedConst(term[2]);

		BBNodeVec::const_iterator bbkfit = bbkids.begin();
		// I should have used pointers to BBNodeVec, to avoid this crock

		result = BBNodeVec(bbkfit + low, bbkfit + high + 1);
		break;
	}
	case BVCONCAT: {
		const BBNodeVec& vec1 = BBTerm(term[0], support);
		const BBNodeVec& vec2 = BBTerm(term[1], support);

		BBNodeVec tmp_res(vec2);
		tmp_res.insert(tmp_res.end(), vec1.begin(), vec1.end());
		result = tmp_res;
		break;
	}
	case BVPLUS: {
		assert(term.Degree() >=1);
		// Add children pairwise and accumulate in BBsum

		ASTVec::const_iterator it = term.begin();
		BBNodeVec tmp_res = BBTerm(*it, support);
		for (++it; it < kids_end; it++) {
			const BBNodeVec& tmp = BBTerm(*it, support);
			assert(tmp.size() == num_bits);
			BBPlus2(tmp_res, tmp, nf->getFalse());
		}

		result = tmp_res;
		break;
	}
	case BVUMINUS: {
		const BBNodeVec& bbkid = BBTerm(term[0], support);
		result = BBUminus(bbkid);
		break;
	}
	case BVSUB: {
		// complement of subtrahend
		// copy, since BBSub writes into it.

		BBNodeVec tmp_res = BBTerm(term[0], support);

		const BBNodeVec& bbkid1 = BBTerm(term[1], support);
		BBSub(tmp_res, bbkid1, support);
		result = tmp_res;
		break;
	}
	case BVMULT: {
		assert(BVTypeCheck(term));

		const ASTNode& t0 = term[0];
		const ASTNode& t1 = term[1];

		const BBNodeVec& mpcd1 = BBTerm(t0, support);
		const BBNodeVec& mpcd2 = BBTerm(t1, support);
		assert(mpcd1.size() == mpcd2.size());
		//Revereses the order of the nodes w/out the need for temporaries
		//This is needed because t0 an t1 must be const
		if ((BVCONST != t0.GetKind()) && (BVCONST == t1.GetKind())) {

			result = BBMult(mpcd2, mpcd1, support);
		} else {
			result = BBMult(mpcd1, mpcd2, support);
		}
		break;
	}
	case BVDIV:
	case BVMOD: {
		const BBNodeVec& dvdd = BBTerm(term[0], support);
		const BBNodeVec& dvsr = BBTerm(term[1], support);
		assert (dvdd.size() == num_bits);
		assert (dvsr.size() == num_bits);
		BBNodeVec q(num_bits);
		BBNodeVec r(num_bits);
		BBDivMod(dvdd, dvsr, q, r, num_bits, support);
		if (k == BVDIV)
			result = q;
		else
			result = r;
		break;
	}
		//  n-ary bitwise operators.
	case BVXOR:
	case BVXNOR:
	case BVAND:
	case BVOR:
	case BVNOR:
	case BVNAND: {
		// Add children pairwise and accumulate in BBsum
		ASTVec::const_iterator it = term.begin();
		Kind bk = UNDEFINED; // Kind of individual bit op.
		switch (k) {
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

		// Sum is destructively modified in the loop, so make a copy of value
		// returned by BBTerm.
		BBNodeVec temp = BBTerm(*it, support);
		BBNodeVec sum(temp); // First operand.

		// Iterate over remaining bitvector term operands
		for (++it; it < kids_end; it++) {
			//FIXME FIXME FIXME: Why does using a temp. var change the behavior?
			temp = BBTerm(*it, support);
			const BBNodeVec& y = temp;

			assert(y.size() == num_bits);
			for (unsigned i = 0; i < num_bits; i++) {
				sum[i] = nf->CreateNode(bk, sum[i], y[i]);
			}
		}
		result = sum;
		break;
	}
	case SYMBOL: {
		assert(num_bits >0);

		BBNodeVec bbvec;
		bbvec.reserve(num_bits);

		for (unsigned int i = 0; i < num_bits; i++) {
			BBNode bit_node = nf->CreateSymbol(term, i);
			bbvec.push_back(bit_node);
		}
		result = bbvec;
		break;
	}
	case BVCONST: {
		BBNodeVec tmp_res(num_bits);
		CBV bv = term.GetBVConst();
		for (unsigned int i = 0; i < num_bits; i++) {
			tmp_res[i] = CONSTANTBV::BitVector_bit_test(bv, i) ? nf->getTrue()
					: nf->getFalse();
		}
		result = tmp_res;
		break;
	}
	default:
		FatalError("BBTerm: Illegal kind to BBTerm", term);
	}

	assert(result.size() == term.GetValueWidth());

	return (BBTermMemo[term] = result);
}

// bit blast a formula (boolean term).  Result is one bit wide,
const BBNode BitBlasterNew::BBForm(const ASTNode& form, BBNodeSet& support) {
	BBNodeMap::iterator it = BBFormMemo.find(form);
	if (it != BBFormMemo.end()) {
		// already there.  Just return it.
		return it->second;
	}

	BBNode result;

	const Kind k = form.GetKind();
	if (!is_Form_kind(k)) {
		FatalError("BBForm: Illegal kind: ", form);
	}

	//  Not returning until end, and memoizing everything, makes it easier
	// to trace coherently.

	// Various special cases
	switch (k) {

	case TRUE: {
		result = nf->getTrue();
		break;
	}

	case FALSE: {
		result = nf->getFalse();
		break;
	}

	case SYMBOL:
		assert (form.GetType() == BOOLEAN_TYPE);

		result = nf->CreateSymbol(form, 0); // 1 bit symbol.
		break;

	case NOT:
		result = nf->CreateNode(NOT, BBForm(form[0], support));
		break;

	case ITE:
		result = nf->CreateNode(ITE, BBForm(form[0], support), BBForm(form[1],
				support), BBForm(form[2], support));
		break;

	case AND:
	case OR:
	case NAND:
	case NOR:
	case IFF:
	case XOR:
	case IMPLIES: {
		BBNodeVec bbkids; // bit-blasted children (formulas)

		ASTVec::const_iterator kids_end = form.end();
		for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++) {
			bbkids.push_back(BBForm(*it, support));
		}
		result = nf->CreateNode(k, bbkids);
		break;
	}

	case EQ: {
		const BBNodeVec left = BBTerm(form[0], support);
		const BBNodeVec right = BBTerm(form[1], support);
		assert (left.size() == right.size());

		result = BBEQ(left, right);
		break;
	}

	case BVLE:
	case BVGE:
	case BVGT:
	case BVLT:
	case BVSLE:
	case BVSGE:
	case BVSGT:
	case BVSLT: {
		result = BBcompare(form, support);
		break;
	}
	default:
		FatalError("BBForm: Illegal kind: ", form);
		break;
	}

	assert(!result.IsNull());

	return (BBFormMemo[form] = result);
}

// Bit blast a sum of two equal length BVs.
// Update sum vector destructively with new sum.
void BitBlasterNew::BBPlus2(BBNodeVec& sum, const BBNodeVec& y, BBNode cin) {

	const int n = sum.size();
	assert(y.size() == (unsigned)n);
	// Revision 320 avoided creating the nextcin, at I suspect unjustified cost.
	for (int i = 0; i < n; i++) {
		BBNode nextcin = Majority(sum[i], y[i], cin);
		sum[i] = nf->CreateNode(XOR, sum[i], y[i], cin);
		cin = nextcin;
	}
}

// Stores result - x in result, destructively
void BitBlasterNew::BBSub(BBNodeVec& result, const BBNodeVec& y,
		BBNodeSet& support) {
	BBNodeVec compsubtrahend = BBNeg(y);
	BBPlus2(result, compsubtrahend, nf->getTrue());
}

// Add one bit
BBNodeVec BitBlasterNew::BBAddOneBit(const BBNodeVec& x, BBNode cin) {
	BBNodeVec result;
	result.reserve(x.size());
	const BBNodeVec::const_iterator itend = x.end();
	for (BBNodeVec::const_iterator it = x.begin(); it < itend; it++) {
		BBNode nextcin = nf->CreateNode(AND, *it, cin);
		result.push_back(nf->CreateNode(XOR, *it, cin));
		cin = nextcin;
	}
	return result;
}

// Increment bit-blasted vector and return result.
BBNodeVec BitBlasterNew::BBInc(const BBNodeVec& x) {
	return BBAddOneBit(x, nf->getTrue());
}

// Return formula for majority function of three bits.
// Pass arguments by reference to reduce refcounting.
BBNode BitBlasterNew::Majority(const BBNode& a, const BBNode& b,
		const BBNode& c) {
	// Checking explicitly for constant a, b and c could
	// be more efficient, because they are repeated in the logic.
	if (nf->getTrue() == a) {
		return nf->CreateNode(OR, b, c);
	} else if (nf->getFalse() == a) {
		return nf->CreateNode(AND, b, c);
	} else if (nf->getTrue() == b) {
		return nf->CreateNode(OR, a, c);
	} else if (nf->getFalse() == b) {
		return nf->CreateNode(AND, a, c);
	} else if (nf->getTrue() == c) {
		return nf->CreateNode(OR, a, b);
	} else if (nf->getFalse() == c) {
		return nf->CreateNode(AND, a, b);
	}
	// there are lots more simplifications, but I'm not sure they're
	// worth doing explicitly (e.g., a = b, a = ~b, etc.)
	else {
		return nf->CreateNode(OR, nf->CreateNode(AND, a, b), nf->CreateNode(
				AND, b, c), nf->CreateNode(AND, a, c));
	}
}

// Bitwise complement
BBNodeVec BitBlasterNew::BBNeg(const BBNodeVec& x) {
	BBNodeVec result;
	result.reserve(x.size());
	// Negate each bit.
	const BBNodeVec::const_iterator& xend = x.end();
	for (BBNodeVec::const_iterator it = x.begin(); it < xend; it++) {
		result.push_back(nf->CreateNode(NOT, *it));
	}
	return result;
}

// Compute unary minus
BBNodeVec BitBlasterNew::BBUminus(const BBNodeVec& x) {
	BBNodeVec xneg = BBNeg(x);
	return BBInc(xneg);
}

// AND each bit of vector y with single bit b and return the result.
BBNodeVec BitBlasterNew::BBAndBit(const BBNodeVec& y, BBNode b) {
	if (nf->getTrue() == b) {
		return y;
	}

	BBNodeVec result;
	result.reserve(y.size());

	const BBNodeVec::const_iterator yend = y.end();
	for (BBNodeVec::const_iterator yit = y.begin(); yit < yend; yit++) {
		result.push_back(nf->CreateNode(AND, *yit, b));
	}
	return result;
}

// Multiply two bitblasted numbers
ASTVec BitBlasterNew::BBMult(const BBNodeVec& x, const BBNodeVec& y,
		BBNodeSet& support) {
	BBNodeVec ycopy(y);
	const BBNodeVec::const_iterator xend = x.end();
	BBNodeVec::const_iterator xit = x.begin();
	// start prod with first partial product.
	BBNodeVec prod = BBNodeVec(BBAndBit(y, *xit));
	// start loop at next bit.
	for (xit++; xit < xend; xit++) {
		// shift first
		BBLShift(ycopy, 1);

		if (nf->getFalse() == *xit) {
			// If this bit is zero, the partial product will
			// be zero.  No reason to add that in.
			continue;
		}

		BBNodeVec pprod = BBAndBit(ycopy, *xit);
		// accumulate in the product.
		BBPlus2(prod, pprod, nf->getFalse());
	}
	return prod;
}

// on factoring12bitsx12.cvc
// variant1 = t, variant2 = t: 66 seconds
// variant1 = t, variant2 = f: 37 seconds
// variant1 = f, variant2 = f: 46 seconds
// variant1 = f, variant2 = t: 65 seconds

// You can select these with any combination you want of true & false.
const bool division_variant_1 = true;
const bool division_variant_2 = false;

// This implements a variant of binary long division.
// q and r are "out" parameters.  rwidth puts a bound on the
// recursion depth.
void BitBlasterNew::BBDivMod(const BBNodeVec &y, const BBNodeVec &x,
		BBNodeVec &q, BBNodeVec &r, unsigned int rwidth, BBNodeSet& support) {
	const unsigned int width = y.size();
	const BBNodeVec zero = BBfill(width, nf->getFalse());
	const BBNodeVec one = BBInc(zero);

	if (rwidth == 0) {
		// When we have shifted the entire width, y is guaranteed to be 0.
		q = zero;
		r = zero;
	} else {
		BBNodeVec q1, r1;
		BBNodeVec yrshift1(y);
		BBRShift(yrshift1, 1);

		// recursively divide y/2 by x.
		BBDivMod(yrshift1, x, q1, r1, rwidth - 1, support);

		BBNodeVec q1lshift1(q1);
		BBLShift(q1lshift1, 1);

		BBNodeVec r1lshift1(r1);
		BBLShift(r1lshift1, 1);

		BBNodeVec r1lshift1plusyodd = BBAddOneBit(r1lshift1, y[0]);
		BBNodeVec rminusx(r1lshift1plusyodd);
		BBSub(rminusx, x, support);

		// Adjusted q, r values when when r is too large.
		BBNode rtoolarge = BBBVLE(x, r1lshift1plusyodd, false);
		BBNodeVec ygtrxqval = BBITE(rtoolarge, BBInc(q1lshift1), q1lshift1);
		BBNodeVec ygtrxrval = BBITE(rtoolarge, rminusx, r1lshift1plusyodd);

		BBNodeVec notylessxqval;
		BBNodeVec notylessxrval;


		/* variant_1 removes the equality check of (x=y). When we get to here I think
		 that r and q already have the proper values.
		 Let x =y, so we are solving y/y.
		 As a first step solve (y/2)/y.
		 If y != 0, then y/2 < y. (strictly less than).
		 By the last rule in this block, that will return q=0, r=(y/2)
		 On return, that will be rightshifted, and the parity bit added back,
		 giving q = 0, r=y.
		 By the immediately preceeding rule, 0 <= 0 is true, so q becomes 1,
		 and r becomes 0.
		 So q and r are already set correctly when we get here.

		 If y=0 & x=0, then (y/2)/0 will return q=0, r=0.
		 By the preceeding rule  0 <= 0 is true, so q =1, r=0.
		 So q and r are already set correctly when we get here.
		 */

		if (division_variant_1)
		{
			notylessxqval = ygtrxqval;
			notylessxrval = ygtrxrval;
		}
		else
		{
			// q & r values when y >= x
			BBNode yeqx = BBEQ(y, x);
			// *** Problem: the bbfill for qval is wrong.  Should be 1, not -1.
			notylessxqval = BBITE(yeqx, one, ygtrxqval);
			notylessxrval = BBITE(yeqx, zero,ygtrxrval);
		}

		BBNode ylessx;
		if (division_variant_2)
		{
			ylessx = BBBVLE(y, x, false, true);
		}
		else
		{
			// y < x <=> not x >= y.
			ylessx = nf->CreateNode(NOT, BBBVLE(x, y, false));
		}

		// final values of q and r
		q = BBITE(ylessx, zero, notylessxqval);
		r = BBITE(ylessx, y, notylessxrval);
	}
}

// build ITE's (ITE cond then[i] else[i]) for each i.
BBNodeVec BitBlasterNew::BBITE(const BBNode& cond, const BBNodeVec& thn,
		const BBNodeVec& els) {
	// Fast exits.
	if (cond == nf->getTrue()) {
		return thn;
	} else if (cond == nf->getFalse()) {
		return els;
	}

	BBNodeVec result;
	result.reserve(els.size());
	const BBNodeVec::const_iterator th_it_end = thn.end();
	BBNodeVec::const_iterator el_it = els.begin();
	for (BBNodeVec::const_iterator th_it = thn.begin(); th_it < th_it_end; th_it++, el_it++) {
		result.push_back(nf->CreateNode(ITE, cond, *th_it, *el_it));
	}
	return result;
}


// On some cases I suspect this is better than the new variant.
ASTNode BBBVLE_variant(const BBNodeVec& left, const BBNodeVec& right, bool is_signed, BBNodeManager* nf)
{
  // "thisbit" represents BVLE of the suffixes of the BVs
  // from that position .  if R < L, return TRUE, else if L < R
  // return FALSE, else return BVLE of lower-order bits.  MSB is
  // treated separately, because signed comparison is done by
  // complementing the MSB of each BV, then doing an unsigned
  // comparison.
  BBNodeVec::const_iterator lit = left.begin();
  BBNodeVec::const_iterator litend = left.end();
  BBNodeVec::const_iterator rit = right.begin();
  BBNode prevbit = nf->getTrue();
  for (; lit < litend - 1; lit++, rit++)
    {
      BBNode thisbit = nf->CreateNode(ITE, nf->CreateNode(IFF, *rit, *lit), prevbit, *rit);
      prevbit = thisbit;
    }

  // Handle MSB -- negate MSBs if signed comparison
  BBNode lmsb = *lit;
  BBNode rmsb = *rit;
  if (is_signed)
    {
      lmsb = nf->CreateNode(NOT, *lit);
      rmsb = nf->CreateNode(NOT, *rit);
    }

  BBNode msb = nf->CreateNode(ITE, nf->CreateNode(IFF, rmsb, lmsb), prevbit, rmsb);
  return msb;
}



// Workhorse for comparison routines.  This does a signed BVLE if is_signed
// is true, else it's unsigned.  All other comparison operators can be reduced
// to this by swapping args or complementing the result bit.
ASTNode BitBlasterNew::BBBVLE(const BBNodeVec& left, const BBNodeVec& right,
		bool is_signed, bool is_bvlt) {
	BBNodeVec::const_reverse_iterator lit = left.rbegin();
	const BBNodeVec::const_reverse_iterator litend = left.rend();
	BBNodeVec::const_reverse_iterator rit = right.rbegin();

	BBNode this_compare_bit = is_signed ? nf->CreateNode(AND, *lit,
			nf->CreateNode(NOT,*rit)) : nf->CreateNode(AND,
					nf->CreateNode(NOT,*lit), *rit);

	BBNodeVec bit_comparisons;
	bit_comparisons.reserve(left.size() +1);

	bit_comparisons.push_back(this_compare_bit);

	//(lit IFF rit) is the same as (NOT(lit) XOR rit)
	BBNode prev_eq_bit = nf->CreateNode(XOR, nf->CreateNode(NOT,
			*lit), *rit);
	for (lit++, rit++; lit < litend; lit++, rit++) {
		this_compare_bit = nf->CreateNode(AND, nf->CreateNode(NOT,*lit),
				*rit);

		BBNode thisbit_output = nf->CreateNode(AND, this_compare_bit,
				prev_eq_bit);
		bit_comparisons.push_back(thisbit_output);

		BBNode this_eq_bit = nf->CreateNode(AND, nf->CreateNode(XOR,
				nf->CreateNode(NOT, *lit), *rit), prev_eq_bit);
		prev_eq_bit = this_eq_bit;
	}

	if (!is_bvlt) {
		bit_comparisons.push_back(prev_eq_bit);
	}

	// Either zero or one of the nodes in bit_comparisons can be true.
	BBNode output =
#ifdef CRYPTOMINISAT2
			nf->CreateNode(XOR, bit_comparisons);
#else
			nf->CreateNode(OR, bit_comparisons);
#endif
	return output;
}

// Left shift  within fixed field inserting zeros at LSB.
// Writes result into first argument.
void BitBlasterNew::BBLShift(BBNodeVec& x, unsigned int shift) {
	// left shift x (destructively) within width.
	// loop backwards so that copy to self works correctly. (DON'T use STL insert!)
	for (int i =((int)x.size())-1; i >=0; i--)
	{
		if (i-(int)shift >= 0)
			x[i] = x[i-(int)shift];
		else
			x[i] = nf->getFalse(); // new LSB is zero.
	}
}

// Right shift within fixed field inserting zeros at MSB.
// Writes result into first argument.
void BitBlasterNew::BBRShift(BBNodeVec& x, unsigned int shift) {
	// right shift x (destructively) within width.
	const BBNodeVec::iterator xend = x.end();
	BBNodeVec::iterator xit = x.begin();
	for (; xit < xend; xit++) {
		if (xit + shift < xend)
			*xit = *(xit + shift);
		else
			*xit = nf->getFalse(); // new MSB is zero.
	}
}

// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
BBNode BitBlasterNew::BBcompare(const ASTNode& form, BBNodeSet& support) {
	const BBNodeVec& left = BBTerm(form[0], support);
	const BBNodeVec& right = BBTerm(form[1], support);

	const Kind k = form.GetKind();
	switch (k) {
	case BVLE: {
		return BBBVLE(left, right, false);
		break;
	}
	case BVGE: {
		return BBBVLE(right, left, false);
		break;
	}
	case BVGT: {
		return BBBVLE(right, left, false, true);
		break;
	}
	case BVLT: {
		return BBBVLE(left, right, false, true);
		break;
	}
	case BVSLE: {
		return BBBVLE(left, right, true);
		break;
	}
	case BVSGE: {
		return BBBVLE(right, left, true);
		break;
	}
	case BVSGT: {
		return nf->CreateNode(NOT, BBBVLE(left, right, true));
		break;
	}
	case BVSLT: {
		return nf->CreateNode(NOT, BBBVLE(right, left, true));
		break;
	}
	default:
		cerr << "BBCompare: Illegal kind" << form << endl;
		FatalError("", form);
	}
}

// return a vector with n copies of fillval
BBNodeVec BitBlasterNew::BBfill(unsigned int width, BBNode fillval) {
	BBNodeVec zvec(width, fillval);
	return zvec;
}

BBNode BitBlasterNew::BBEQ(const BBNodeVec& left, const BBNodeVec& right) {
	BBNodeVec andvec;
	andvec.reserve(left.size());
	BBNodeVec::const_iterator lit = left.begin();
	const BBNodeVec::const_iterator litend = left.end();
	BBNodeVec::const_iterator rit = right.begin();

	if (left.size() > 1) {
		for (; lit != litend; lit++, rit++) {
			BBNode biteq = nf->CreateNode(IFF, *lit, *rit);
			// fast path exit
			if (biteq == nf->getFalse()) {
				return nf->getFalse();
			} else {
				andvec.push_back(biteq);
			}
		}
		BBNode n = nf->CreateNode(AND, andvec);
		return n;
	} else
		return nf->CreateNode(IFF, *lit, *rit);
}

} // BEEV namespace

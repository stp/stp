// Experimental bvsolver.


/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "../AST/AST.h"
#include "bvsolverExp.h"
#include <cassert>
#include "simplifier.h"
#include "CountOfSymbols.h"

//This file contains the implementation of member functions of
//bvsolver class, which represents the bitvector arithmetic linear
//solver. Please also refer the STP's CAV 2007 paper for the
//complete description of the linear solver algorithm
//
//The bitvector solver is a partial solver, i.e. it does not solve
//for all variables in the system of equations. it is
//best-effort. it relies on the SAT solver to be complete.
//
//The BVSolver assumes that the input equations are normalized, and
//have liketerms combined etc.
//
//0. Traverse top-down over the input DAG, looking for a conjunction
//0. of equations. if you find one, then for each equation in the
//0. conjunction, do the following steps.
//
//1. check for Linearity of the input equation
//
//2. Solve for a "chosen" variable. The variable should occur
//2. exactly once and must have an odd coeff. Refer STP's CAV 2007
//2. paper for actual solving procedure
//
//4. Outside the solver, Substitute and Re-normalize the input DAG
namespace BEEV {
const bool bv_debug = false;

//check the solver map for 'key'. If key is present, then return the
//value by reference in the argument 'output'
bool BVSolverExp::CheckAlreadySolvedMap(const ASTNode& key, ASTNode& output) {
	ASTNodeMap::const_iterator it;
	if ((it = FormulasAlreadySolvedMap.find(key))
			!= FormulasAlreadySolvedMap.end()) {
		output = it->second;
		return true;
	}
	return false;
} //CheckAlreadySolvedMap()

void BVSolverExp::UpdateAlreadySolvedMap(const ASTNode& key,
		const ASTNode& value) {
	FormulasAlreadySolvedMap[key] = value;
} //end of UpdateAlreadySolvedMap()

//Accepts an even number "in", and splits it into an odd number and
//a power of 2. i.e " in = b.(2^k) ". returns the odd number, and
//the power of two by reference.
//An "in" of zero returns a large shift.
void BVSolverExp::SplitEven_into_Oddnum_PowerOf2(const ASTNode& in,
		unsigned int& number_shifts) {
	if (BVCONST != in.GetKind() || simplifier->BVConstIsOdd(in)) {
		FatalError(
				"BVSolver:SplitNum_Odd_PowerOf2: input must be a BVCONST and even\n",
				in);
	}

	for (number_shifts = 0; number_shifts < in.GetValueWidth()
			&& !CONSTANTBV::BitVector_bit_test(in.GetBVConst(), number_shifts); number_shifts++) {
	};
	assert(number_shifts >0);
}
#if 0
ASTNode OLDSplitEven_into_Oddnum_PowerOf2(const ASTNode& in, unsigned int& number_shifts)
{
	if (BVCONST != in.GetKind() || simplifier->BVConstIsOdd(in))
	{
		FatalError("BVSolver:SplitNum_Odd_PowerOf2: input must be a BVCONST and even\n", in);
	}

	unsigned int len = in.GetValueWidth();
	ASTNode zero = _bm->CreateZeroConst(len);
	ASTNode two = _bm->CreateTwoConst(len);
	ASTNode div_by_2 = in;
	ASTNode mod_by_2 = _bm->BVConstEvaluator(_bm->CreateTerm(BVMOD, len, div_by_2, two));
	while (mod_by_2 == zero)
	{
		div_by_2 = _bm->BVConstEvaluator(_bm->CreateTerm(BVDIV, len, div_by_2, two));
		number_shifts++;
		mod_by_2 = _bm->BVConstEvaluator(_bm->CreateTerm(BVMOD, len, div_by_2, two));
	}
	return div_by_2;
} //end of SplitEven_into_Oddnum_PowerOf2()

//Checks if there are any ARRAYREADS in the term, after the
//alreadyseenmap is cleared, i.e. traversing a new term altogether


bool BVSolver::CheckForArrayReads_TopLevel(const ASTNode& term)
{
	TermsAlreadySeenMap.clear();
	return CheckForArrayReads(term);
}

//Checks if there are any ARRAYREADS in the term
bool BVSolver::CheckForArrayReads(const ASTNode& term)
{
	ASTNode a = term;
	ASTNodeMap::iterator it;
	if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end())
	{
		//if the term has been seen, then simply return true, else
		//return false
		if (ASTTrue == (it->second))
		{
			return true;
		}
		else
		{
			return false;
		}
	}

	switch (term.GetKind())
	{
		case READ:
		//an array read has been seen. Make an entry in the map and
		//return true
		TermsAlreadySeenMap[term] = ASTTrue;
		return true;
		default:
		{
			ASTVec c = term.GetChildren();
			for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
			{
				if (CheckForArrayReads(*it))
				{
					return true;
				}
			}
			break;
		}
	}

	//If control is here, then it means that no arrayread was seen for
	//the input 'term'. Make an entry in the map with the term as key
	//and FALSE as value.
	TermsAlreadySeenMap[term] = ASTFalse;
	return false;
} //end of CheckForArrayReads()
#endif

bool BVSolverExp::DoNotSolveThis(const ASTNode& var) {
	if (DoNotSolve_TheseVars.find(var) != DoNotSolve_TheseVars.end()) {
		if (bv_debug) {
			cerr << "DoNotSolveThis. Do Not Solve for:" << var;
		}
		return true;
	}
	return false;
}

//chooses a variable in the lhs and returns the chosen variable
ASTNode BVSolverExp::ChooseMonom(const ASTNode& eq, ASTNode& modifiedlhs) {
	if (!(EQ == eq.GetKind() && BVPLUS == eq[0].GetKind())) {
		FatalError("ChooseMonom: input must be a EQ", eq);
	}

	const ASTNode& lhs = eq[0];
	const ASTNode& rhs = eq[1];

	assert(lhs.Degree() > 1);

	CountOfSymbols Vars(eq);

	const ASTVec& c = lhs.GetChildren();
	ASTVec o;
	ASTNode outmonom = _bm->CreateNode(UNDEFINED);
	bool chosen_symbol = false;

	//choose variables with no coeffs.
	for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++) {
		const ASTNode& monom = *it;
		if (SYMBOL == monom.GetKind() && !DoNotSolveThis(monom)
				&& !chosen_symbol && Vars.single(monom)) {
			outmonom = monom;
			chosen_symbol = true;
		} else if (BVUMINUS == monom.GetKind() && SYMBOL == monom[0].GetKind()
				&& !DoNotSolveThis(monom[0]) && !chosen_symbol && Vars.single(
				monom[0])) {
			//cerr << "Chosen Monom: " << monom << endl;
			outmonom = monom;
			chosen_symbol = true;
		} else {
			o.push_back(monom);
		}
	}

	//try to choose only odd coeffed variables.
	if (!chosen_symbol) {
		bool chosen_odd = false;
		const ASTNode& zero = _bm->CreateZeroConst(32);
		o.clear();

		for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it
				!= itend; it++) {
			const ASTNode& monom = *it;
			ASTNode var = (BVMULT == monom.GetKind()) ? monom[1]
					: _bm->CreateNode(UNDEFINED);

			if (BVMULT == monom.GetKind() && BVCONST == monom[0].GetKind()
					&& simplifier->BVConstIsOdd(monom[0]) && ((SYMBOL == var.GetKind()
					&& Vars.single(var)) || (BVEXTRACT == var.GetKind()
					&& SYMBOL == var[0].GetKind() && BVCONST
					== var[1].GetKind() && zero == var[2]
					&& Vars.single(var[0]) && !DoNotSolveThis(var[0])))
					&& !DoNotSolveThis(var) && !_bm->VarSeenInTerm(var, rhs)
					&& !chosen_odd && Vars.single(var)) {
				//monom[0] is odd.
				outmonom = monom;
				chosen_odd = true;
			} else {
				o.push_back(monom);
			}
		}
	}

	modifiedlhs = (o.size() > 1) ? _bm->CreateTerm(BVPLUS, lhs.GetValueWidth(),
			o) : o[0];
	return outmonom;
} //end of choosemonom()

//solver function which solves for variables with odd coefficient
ASTNode BVSolverExp::BVSolve_Odd(const ASTNode& eq_original) {
	ASTNode eq = eq_original;

	if (!(EQ == eq.GetKind())) {
		return eq;
	}

	//get the lhs and the rhs, and case-split on the lhs kind
	ASTNode lhs = eq[0];
	ASTNode rhs = eq[1];

	// if only one side is a constant, it should be on the RHS.
	if (((BVCONST == lhs.GetKind()) ^ (BVCONST == rhs.GetKind()))
			&& (lhs.GetKind() == BVCONST)) {
		lhs = eq[1];
		rhs = eq[0];
		eq = _bm->CreateNode(EQ, lhs, rhs); // If "return eq" is called, return the arguments in the correct order.
	}

	ASTNode output = eq;
	if (CheckAlreadySolvedMap(eq, output)) {
		return output;
	}

	if (BVPLUS == lhs.GetKind()) {
		ASTNode chosen_monom = _bm->CreateNode(UNDEFINED);
		ASTNode leftover_lhs;

		//choose monom makes sure that it gets only those vars that
		//occur exactly once in lhs and rhs put together
		chosen_monom = ChooseMonom(eq, leftover_lhs);
		if (chosen_monom == _bm->CreateNode(UNDEFINED)) {
			//no monomial was chosen
			return eq;
		}

		if (bv_debug)
			cerr << "Chosen monomial:" << chosen_monom;

		//if control is here then it means that a monom was chosen
		//
		//construct:  rhs - (lhs without the chosen monom)
		unsigned int len = lhs.GetValueWidth();
		leftover_lhs = simplifier->SimplifyTerm_TopLevel(_bm->CreateTerm(BVUMINUS,
				len, leftover_lhs));
		rhs
				= simplifier->SimplifyTerm(_bm->CreateTerm(BVPLUS, len, rhs,
						leftover_lhs));
		lhs = chosen_monom;
	} //end of if(BVPLUS ...)

	if (BVUMINUS == lhs.GetKind()) {
		//equation is of the form (-lhs0) = rhs
		ASTNode lhs0 = lhs[0];
		rhs = simplifier->SimplifyTerm(_bm->CreateTerm(BVUMINUS, rhs.GetValueWidth(),
				rhs));
		lhs = lhs0;
	}

	switch (lhs.GetKind()) {
	case SYMBOL: {
		//input is of the form x = rhs first make sure that the lhs
		//symbol does not occur on the rhs or that it has not been
		//solved for
		if (_bm->VarSeenInTerm(lhs, rhs)) {
			//found the lhs in the rhs. Abort!
			DoNotSolve_TheseVars.insert(lhs);
			return eq;
		}

		//rhs should not have arrayreads in it. it complicates matters
		//during transformation
		// if(CheckForArrayReads_TopLevel(rhs)) {
		//            return eq;
		//       }

		DoNotSolve_TheseVars.insert(lhs);
		if (simplifier->UpdateSolverMap(lhs, rhs)) {
			return eq;
		}

		output = ASTTrue;
		break;
	}
		//              case READ:
		//              {
		//                if(BVCONST != lhs[1].GetKind() || READ != rhs.GetKind() ||
		//                     BVCONST != rhs[1].GetKind() || lhs == rhs)
		//                {
		//                  return eq;
		//                }
		//                else
		//                {
		//                  DoNotSolve_TheseVars.insert(lhs);
		//                  if (!_bm->UpdateSolverMap(lhs, rhs))
		//                    {
		//                      return eq;
		//                    }

		//                  output = ASTTrue;
		//                  break;
		//                }
		//              }
	case BVEXTRACT: {
		const ASTNode zero = _bm->CreateZeroConst(32);

		if (!(SYMBOL == lhs[0].GetKind() && BVCONST == lhs[1].GetKind() && zero
				== lhs[2] && !_bm->VarSeenInTerm(lhs[0], rhs)
				&& !DoNotSolveThis(lhs[0]))) {
			return eq;
		}

		if (_bm->VarSeenInTerm(lhs[0], rhs)) {
			DoNotSolve_TheseVars.insert(lhs[0]);
			return eq;
		}

		DoNotSolve_TheseVars.insert(lhs[0]);
		if (!simplifier->UpdateSolverMap(lhs, rhs)) {
			return eq;
		}

		//if the extract of x[i:0] = t is entered into the solvermap,
		//then also add another entry for x = x1@t
		ASTNode var = lhs[0];
		ASTNode newvar = NewVar(var.GetValueWidth() - lhs.GetValueWidth());
		newvar = _bm->CreateTerm(BVCONCAT, var.GetValueWidth(), newvar, rhs);
		simplifier->UpdateSolverMap(var, newvar);
		output = ASTTrue;
		break;
	}
	case BVMULT: {
		//the input is of the form a*x = t. If 'a' is odd, then compute
		//its multiplicative inverse a^-1, multiply 't' with it, and
		//update the solver map
		if (BVCONST != lhs[0].GetKind()) {
			return eq;
		}

		if (!(SYMBOL == lhs[1].GetKind() || (BVEXTRACT == lhs[1].GetKind()
				&& SYMBOL == lhs[1][0].GetKind()))) {
			return eq;
		}

		bool ChosenVar_Is_Extract = (BVEXTRACT == lhs[1].GetKind()) ? true
				: false;

		//if coeff is even, then we know that all the coeffs in the eqn
		//are even. Simply return the eqn
		if (simplifier->BVConstIsOdd(lhs[0])) {
			return eq;
		}

		ASTNode a = simplifier->MultiplicativeInverse(lhs[0]);
		ASTNode chosenvar = ChosenVar_Is_Extract ? lhs[1][0] : lhs[1];
		ASTNode chosenvar_value = simplifier->SimplifyTerm(_bm->CreateTerm(BVMULT,
				rhs.GetValueWidth(), a, rhs));

		//if chosenvar is seen in chosenvar_value then abort
		if (_bm->VarSeenInTerm(chosenvar, chosenvar_value)) {
			//abort solving
			if (bv_debug)
				cerr << "The chosen variable appears elsewhere:" << chosenvar;

			DoNotSolve_TheseVars.insert(lhs); // this could be an extract??
			return eq;
		}

		//rhs should not have arrayreads in it. it complicates matters
		//during transformation
		// if(CheckForArrayReads_TopLevel(chosenvar_value)) {
		//            return eq;
		//       }

		//found a variable to solve
		DoNotSolve_TheseVars.insert(chosenvar);
		chosenvar = lhs[1];
		if (!simplifier->UpdateSolverMap(chosenvar, chosenvar_value)) {
			return eq;
		}

		// can we be sure that the extract is from zero?
		if (ChosenVar_Is_Extract) {
			const ASTNode& var = lhs[1][0];
			ASTNode newvar = NewVar(var.GetValueWidth()
					- lhs[1].GetValueWidth());
			newvar = _bm->CreateTerm(BVCONCAT, var.GetValueWidth(), newvar,
					chosenvar_value);
			simplifier->UpdateSolverMap(var, newvar);
		}

		output = ASTTrue;
		break;
	}
	default:
		output = eq;
		break;
	}

	assert(!output.IsNull());
	UpdateAlreadySolvedMap(eq, output);
	return output;
} //end of BVSolve_Odd()

//Create a new variable of ValueWidth 'n'
ASTNode BVSolverExp::NewVar(unsigned int n) {
	std::string c("v");
	char d[32];
	sprintf(d, "%d", _symbol_count++);
	std::string ccc(d);
	c += "_solver_" + ccc;

	ASTNode CurrentSymbol = _bm->CreateSymbol(c.c_str());
	CurrentSymbol.SetValueWidth(n);
	CurrentSymbol.SetIndexWidth(0);
	return CurrentSymbol;
} //end of NewVar()


bool containsExtract(const ASTNode& n, ASTNodeSet& visited) {
	if (visited.find(n) != visited.end())
		return false;

	if (BVEXTRACT == n.GetKind())
		return true;

	for (unsigned i = 0; i < n.Degree(); i++) {
		if (containsExtract(n[i], visited))
			return true;
	}
	visited.insert(n);
	return false;
}

// The order that monomials are chosen in from the system of equations is important.
// In particular if a symbol is chosen that is extracted over, and that symbol
// appears elsewhere in the system. Then those other positions will be replaced by
// an equation that contains a concatenation.
// For example, given:
// 5x[5:1] + 4y[5:1] = 6
// 3x + 2y = 5
//
// If the x that is extracted over is selected as the monomial, then the later eqn. will be
// rewritten as:
// 3(concat (1/5)(6-4y[5:1]) v) + 2y =5
// where v is a fresh one-bit variable.
// What's particularly bad about this is that the "y" appears now in two places in the eqn.
// Because it appears in two places it can't be simplified by this algorithm
// This sorting function is a partial solution. Ideally the "best" monomial should be
// chosen from the system of equations.
void specialSort(ASTVec& c) {
	// Place equations that don't contain extracts before those that do.
	deque<ASTNode> extracts;
	ASTNodeSet v;

	for (unsigned i = 0; i < c.size(); i++) {
		if (containsExtract(c[i], v))
			extracts.push_back(c[i]);
		else
			extracts.push_front(c[i]);
	}

	c.clear();
	deque<ASTNode>::iterator it = extracts.begin();
	while (it != extracts.end()) {
		c.push_back(*it++);
	}
}

//The toplevel bvsolver(). Checks if the formula has already been
//solved. If not, the solver() is invoked. If yes, then simply drop
//the formula
ASTNode BVSolverExp::TopLevelBVSolve(const ASTNode& input) {
	assert(_bm->UserFlags.wordlevel_solve_flag);
	return input;

	if (bv_debug) {
		cerr << "input to bvSolver";
		cerr << input;
	}

	const Kind k = input.GetKind();
	if (!(EQ == k || AND == k)) {
		return input;
	}

	ASTNode output = input;
	if (CheckAlreadySolvedMap(input, output)) {
		//output is TRUE. The formula is thus dropped
		return output;
	}

	_bm->GetRunTimes()->start(RunTimes::BVSolver);
	ASTVec o;
	ASTVec c;
	if (EQ == k)
		c.push_back(input);
	else {
		// Flatten the AND, this may flatten BVPLUS (say) which we don't really want.
		ASTNode n = input;
		while (true) {
			ASTNode nold = n;
			n = simplifier->FlattenOneLevel(n);
			if ((n == nold))
				break;
		}

		// When flattening simplifications will be applied to the node, potentially changing it's type:
		// (AND x (ANY (not x) y)) gives us FALSE.
		if (!(EQ == n.GetKind() || AND == n.GetKind())) {
			{
				_bm->GetRunTimes()->stop(RunTimes::BVSolver);
				return n;
			}
		}

		c = n.GetChildren();
		specialSort(c);
	}

	assert(c.size()> 0);

	ASTVec eveneqns;
	bool substitution = false;
	for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++) {
		assert(it->GetKind() != AND); // These should have been flattened.

		// If there has been a prior substitution we need to be careful that the newly encountered equations
		// don't have the substituted variable on the rhs. For example, say we have the substitution already:
		// v1 = (concat v2 v3).
		// Next, say we encounter the equation:
		// v2 = (concat v1 v3).
		// if the v1 in the second equation is not substituted, then we will create a circular reference in the
		// substitution map. We use simplify to perform the substitutions.
		ASTNode aaa =
				(substitution && EQ == it->GetKind()) ? simplifier->SimplifyFormula(
						*it, false) : *it;
		aaa = BVSolve_Odd(aaa);
		bool even = false;
		aaa = CheckEvenEqn(aaa, even);
		if (even) {
			eveneqns.push_back(aaa);
		} else {
			if (ASTTrue != aaa) {
				o.push_back(aaa);
			} else {
				substitution = true;
			}
		}
	}

	ASTNode evens;
	if (eveneqns.size() > 0) {
		//if there is a system of even equations then solve them
		evens = (eveneqns.size() > 1) ? _bm->CreateNode(AND, eveneqns)
				: eveneqns[0];
		//evens = _bm->SimplifyFormula(evens,false);
		evens = BVSolve_Even(evens);
		_bm->ASTNodeStats("Printing after evensolver:", evens);
	} else {
		evens = ASTTrue;
	}
	output = (o.size() > 0) ? ((o.size() > 1) ? _bm->CreateNode(AND, o) : o[0])
			: ASTTrue;
	output = _bm->CreateNode(AND, evens, output);

	UpdateAlreadySolvedMap(input, output);

	if (bv_debug) {
		cerr << "output from bvSolver";
		cerr << output;
	}

	_bm->GetRunTimes()->stop(RunTimes::BVSolver);
	return output;
} //end of TopLevelBVSolve()


ASTNode BVSolverExp::CheckEvenEqn(const ASTNode& input, bool& evenflag) {
	ASTNode eq = input;
	//cerr << "Input to BVSolve_Odd()" << eq << endl;
	if (!(EQ == eq.GetKind())) {
		evenflag = false;
		return eq;
	}

	ASTNode lhs = eq[0];
	ASTNode rhs = eq[1];
	ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
	//lhs must be a BVPLUS, and rhs must be a BVCONST
	assert(!(BVPLUS == rhs.GetKind() && zero == lhs)); // shouldn't be swapped.
	if (!(BVPLUS == lhs.GetKind() && zero == rhs)) {
		evenflag = false;
		return eq;
	}

	const ASTVec lhs_c = lhs.GetChildren();
	ASTNode savetheconst = rhs;
	bool first = true;
	for (ASTVec::const_iterator it = lhs_c.begin(), itend = lhs_c.end(); it
			!= itend; it++) {
		ASTNode aaa = *it;
		const Kind itk = aaa.GetKind();

		if (BVCONST == itk) {
			//check later if the constant is even or not
			savetheconst = aaa;
			assert(first); // atmost a single constant in the expression.
			first = false;
			continue;
		}

		if (!(BVMULT == itk && BVCONST == aaa[0].GetKind() && SYMBOL
				== aaa[1].GetKind() && !simplifier->BVConstIsOdd(aaa[0]))) {
			//If the monomials of the lhs are NOT of the form 'a*x' where
			//'a' is even, then return the false
			evenflag = false;
			return eq;
		}
	}//end of for loop

	//if control is here then it means that all coeffs are even. the
	//only remaining thing is to check if the constant is even or not
	if (simplifier->BVConstIsOdd(savetheconst)) {
		//the constant turned out to be odd. we have UNSAT eqn
		evenflag = false;
		return ASTFalse;
	}

	//all is clear. the eqn in even, through and through
	evenflag = true;
	return eq;
} //end of CheckEvenEqn

//solve an eqn whose monomials have only even coefficients
//The input should have already been checked with "checkeveneqn"
// Given an input of "2x + 6y + 12 = 0",
// it will divide by the smallest co-efficient, giving: "x[?:1] + 3y[?:1] + 6 = 0"
ASTNode BVSolverExp::BVSolve_Even(const ASTNode& input) {
	assert(_bm->UserFlags.wordlevel_solve_flag);

	assert((EQ == input.GetKind() || AND == input.GetKind()));
	if (!(EQ == input.GetKind() || AND == input.GetKind())) {
		return input;
	}

	{
		ASTNode output;
		if (CheckAlreadySolvedMap(input, output)) {
			return output;
		}
	}

	ASTVec input_c;
	if (EQ == input.GetKind()) {
		input_c.push_back(input);
	} else {
		input_c = input.GetChildren();
	}

	//power_of_2 holds the exponent of 2 in the coeff
	unsigned int power_of_2 = 0;
	//we need this additional variable to find the lowest power of 2
	unsigned int power_of_2_lowest = ~0;
	//the monom which has the least power of 2 in the coeff
	for (ASTVec::iterator jt = input_c.begin(), jtend = input_c.end(); jt
			!= jtend; jt++) {
		ASTNode eq = *jt;
		assert(EQ ==eq.GetKind());
		ASTNode lhs = eq[0];
		ASTNode rhs = eq[1];
		ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());

		//lhs must be a BVPLUS, and rhs must be zero
		assert ((BVPLUS == lhs.GetKind() && zero == rhs));
		if (!(BVPLUS == lhs.GetKind() && zero == rhs)) {
			return input;
		}

		const ASTVec& lhs_c = lhs.GetChildren();
		for (ASTVec::const_iterator it = lhs_c.begin(), itend = lhs_c.end(); it
				!= itend; it++) {
			ASTNode aaa = *it;
			const Kind itk = aaa.GetKind();

			//If the monomials of the lhs are NOT of the form 'a*x' or 'a'
			//where 'a' is even, then return the eqn

			assert ((BVCONST == itk && !simplifier->BVConstIsOdd(aaa)) ||
					(BVMULT == itk && BVCONST == aaa[0].GetKind() && SYMBOL == aaa[1].GetKind() && !simplifier->BVConstIsOdd(aaa[0])));

			if (!(BVCONST == itk && !simplifier->BVConstIsOdd(aaa)) && !(BVMULT == itk
					&& BVCONST == aaa[0].GetKind() && SYMBOL
					== aaa[1].GetKind() && !simplifier->BVConstIsOdd(aaa[0]))) {
				return input;
			}

			//we are gauranteed that if control is here then the monomial is
			//of the form 'a*x' or 'a', where 'a' is even
			ASTNode coeff = (BVCONST == itk) ? aaa : aaa[0];
			SplitEven_into_Oddnum_PowerOf2(coeff, power_of_2);
			if (power_of_2 < power_of_2_lowest) {
				power_of_2_lowest = power_of_2;
			}
			power_of_2 = 0;
		}//end of inner for loop
	} //end of outer for loop

	//get the exponent
	power_of_2 = power_of_2_lowest;
	assert(power_of_2 > 0);

	if (bv_debug)
		cerr << "Shifting all by:" << power_of_2 << endl;

	//if control is here, we are gauranteed that we have chosen a
	//monomial with fewest powers of 2
	//Go through all the formulae, dividing the co-efficients.
	ASTVec formula_out;
	for (ASTVec::iterator jt = input_c.begin(), jtend = input_c.end(); jt
			!= jtend; jt++) {
		const ASTNode eq = *jt;
		assert(EQ == eq.GetKind());
		ASTNode lhs = eq[0];
		ASTNode rhs = eq[1];
		unsigned len = lhs.GetValueWidth();
		const ASTNode zero = _bm->CreateZeroConst(len);

		//lhs must be a BVPLUS, and rhs must be a BVCONST
		assert((BVPLUS == lhs.GetKind() && zero == rhs));
		if (!(BVPLUS == lhs.GetKind() && zero == rhs)) {
			return input;
		}

		const unsigned newlen = len - power_of_2;
		const ASTNode start = _bm->CreateBVConst(32, newlen - 1);
		ASTNode end = _bm->CreateZeroConst(32);
		const ASTNode two_const = _bm->CreateTwoConst(len);

		unsigned count = power_of_2;
		ASTNode two = two_const;
		while (--count) {
			two = simplifier->BVConstEvaluator(_bm->CreateTerm(BVMULT, len, two_const,
					two));
		}
		const ASTVec& lhs_c = lhs.GetChildren();
		ASTVec lhs_out;
		for (ASTVec::const_iterator it = lhs_c.begin(), itend = lhs_c.end(); it
				!= itend; it++) {
			ASTNode aaa = *it;
			const Kind itk = aaa.GetKind();
			if (BVCONST == itk) {
				aaa = simplifier->BVConstEvaluator(_bm->CreateTerm(BVDIV, len, aaa,
						two));
				aaa = simplifier->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, newlen,
						aaa, start, end));
			} else {
				//it must be of the form a*x
				ASTNode coeff = simplifier->BVConstEvaluator(_bm->CreateTerm(BVDIV,
						len, aaa[0], two));
				coeff = simplifier->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT,
						newlen, coeff, start, end));
				ASTNode lower_x = simplifier->SimplifyTerm(_bm->CreateTerm(BVEXTRACT,
						newlen, aaa[1], start, end));
				aaa = _bm->CreateTerm(BVMULT, newlen, coeff, lower_x);
			}
			lhs_out.push_back(aaa);
		}//end of inner forloop()
		rhs = _bm->CreateZeroConst(newlen);
		lhs = _bm->CreateTerm(BVPLUS, newlen, lhs_out);
		formula_out.push_back(_bm->CreateNode(EQ, lhs, rhs));
	} //end of outer forloop()

	ASTNode
			output =
					(formula_out.size() > 0) ? (formula_out.size() > 1) ? _bm->CreateNode(
							AND, formula_out)
							: formula_out[0]
							: ASTTrue;

	if (bv_debug) {
		cerr << "Even has been solved";
		cerr << input;
		cerr << output;
	}

	UpdateAlreadySolvedMap(input, output);

	return output;
} //end of BVSolve_Even()
}
;//end of namespace BEEV

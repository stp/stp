// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/


#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "bvsolver.h"
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
namespace BEEV
{
	//experimental options. Don't curerntly work.
	const bool flatten_ands = false;
	const bool sort_extracts_last = false;

  //check the solver map for 'key'. If key is present, then return the
  //value by reference in the argument 'output'
  bool BVSolver::CheckAlreadySolvedMap(const ASTNode& key, ASTNode& output)
  {
    ASTNodeMap::const_iterator it;
    if ((it = FormulasAlreadySolvedMap.find(key)) 
        != FormulasAlreadySolvedMap.end())
      {
        output = it->second;
        return true;
      }
    return false;
  } //CheckAlreadySolvedMap()

  void BVSolver::UpdateAlreadySolvedMap(const ASTNode& key, 
                                        const ASTNode& value)
  {
    FormulasAlreadySolvedMap[key] = value;
  } //end of UpdateAlreadySolvedMap()

  //accepts an even number "in", and returns the location of
  // the lowest bit that is turned on in that number.
  void BVSolver::SplitEven_into_Oddnum_PowerOf2(const ASTNode& in,
  		unsigned int& number_shifts) {
  	assert (BVCONST == in.GetKind() && !_simp->BVConstIsOdd(in));

  	// location of the least significant bit turned on.
  	for (number_shifts = 0; number_shifts < in.GetValueWidth()
  			&& !CONSTANTBV::BitVector_bit_test(in.GetBVConst(), number_shifts); number_shifts++) {
  	};
  	assert(number_shifts >0); // shouldn't be odd.
  }


#if 0
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
        //if the term has been seen, then _simply return true, else
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
          for (ASTVec::iterator 
                 it = c.begin(), itend = c.end(); it != itend; it++)
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

  bool BVSolver::DoNotSolveThis(const ASTNode& var)
  {
    if (DoNotSolve_TheseVars.find(var) != DoNotSolve_TheseVars.end())
      {
        return true;
      }
    return false;
  }

  //chooses a variable in the lhs and returns the chosen variable
  ASTNode BVSolver::ChooseMonom(const ASTNode& eq, ASTNode& modifiedlhs)
  {
    if (!(EQ == eq.GetKind() && BVPLUS == eq[0].GetKind()))
      {
        FatalError("ChooseMonom: input must be a EQ", eq);
      }

    const ASTNode& lhs = eq[0];
    const ASTNode& rhs = eq[1];

    //collect all the vars in the lhs and rhs

    BuildSymbolGraph(eq);
    CountOfSymbols count(symbol_graph[eq]);

    //handle BVPLUS case
    const ASTVec& c = lhs.GetChildren();
    ASTVec o;
    ASTNode outmonom = ASTUndefined;
    bool chosen_symbol = false;

    //choose variables with no coeffs
    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
    	const ASTNode& monom = *it;
        if (
        	(
        	SYMBOL == monom.GetKind()
            && !chosen_symbol
       		&& !DoNotSolveThis(monom)
            && !VarSeenInTerm(monom,rhs)
            )
            ||
            (
             BVUMINUS == monom.GetKind()
             && SYMBOL == monom[0].GetKind()
             && !chosen_symbol
             && !DoNotSolveThis(monom[0])
             && !VarSeenInTerm(monom[0],rhs)
            )
           )
        {
        	// Look through all the children of the BVPLUS and check
        	// that the variable appears in none of them.

        	ASTNode var = (SYMBOL == monom.GetKind())? monom: monom[0];
        	bool duplicated = false;
        	for (ASTVec::const_iterator it2 = c.begin(); it2 != itend; it2++)
			{
				if (it2 == it)
					continue;
				if (VarSeenInTerm(var,*it2))
				{
					duplicated = true;
					break;
				}
			}
			if (!duplicated)
			{
				outmonom = monom; //nb. monom not var.
				chosen_symbol = true;
			}
			else
				o.push_back(monom);
        }
    	else
    		o.push_back(monom);
	}

    //try to choose only odd coeffed variables first
    if (!chosen_symbol)
      {
        ASTNode zero = _bm->CreateZeroConst(32);

    	o.clear();
        for (ASTVec::const_iterator
               it = c.begin(), itend = c.end(); it != itend; it++)
          {
            const ASTNode& monom = *it;
            ASTNode var = 
              (BVMULT == monom.GetKind()) ? 
              monom[1] : 
              ASTUndefined;

            if (BVMULT == monom.GetKind() 
                && BVCONST == monom[0].GetKind() 
                && _simp->BVConstIsOdd(monom[0]) 
                && !chosen_symbol
                && !DoNotSolveThis(var)
                && ((SYMBOL == var.GetKind() 
                     && count.single(var)
                    )
                    || (BVEXTRACT == var.GetKind() 
                        && SYMBOL == var[0].GetKind() 
                        && BVCONST == var[1].GetKind() 
                        && zero == var[2]
                        && !DoNotSolveThis(var[0])
                        && count.single(var[0])
                        ))
                )
              {
                //monom[0] is odd.
                outmonom = monom;
                chosen_symbol = true;
              }
            else
              {
                o.push_back(monom);
              }
          }
      }

    modifiedlhs = 
      (o.size() > 1) ? 
      _bm->CreateTerm(BVPLUS, lhs.GetValueWidth(), o) : 
      o[0];

    // can be SYMBOL or (BVUMINUS SYMBOL) or (BVMULT ODD_BVCONST SYMBOL) or
    // (BVMULT ODD_BVCONST (EXTRACT SYMBOL BV_CONST ZERO))
    return outmonom;
  } //end of choosemonom()

  //solver function which solves for variables with odd coefficient
  ASTNode BVSolver::BVSolve_Odd(const ASTNode& input)
  {
    ASTNode eq = input;
    //cerr << "Input to BVSolve_Odd()" << eq << endl;
    if (!(EQ == eq.GetKind()))
      {
        return input;
      }

    ASTNode output = input;

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

    if (CheckAlreadySolvedMap(eq, output))
      {
        return output;
      }

    // ChooseMonom makes sure that the the LHS is not contained on the RHS, so we
    // set this "single" to true in the branch that runs chooseMonomial.
    bool single = false;

    if (BVPLUS == lhs.GetKind())
      {
        ASTNode chosen_monom = ASTUndefined;
        ASTNode leftover_lhs;

        //choose monom makes sure that it gets only those vars that
        //occur exactly once in lhs and rhs put together
        chosen_monom = ChooseMonom(eq, leftover_lhs);
        if (chosen_monom == ASTUndefined)
          {
            //no monomial was chosen
            return eq;
          }

        //if control is here then it means that a monom was chosen
        //
        //construct:  rhs - (lhs without the chosen monom)
        unsigned int len = lhs.GetValueWidth();
        leftover_lhs = 
          _simp->SimplifyTerm_TopLevel(_bm->CreateTerm(BVUMINUS,
                                                       len, leftover_lhs));
        rhs =
          _simp->SimplifyTerm(_bm->CreateTerm(BVPLUS, len, rhs, leftover_lhs));
        lhs = chosen_monom;
        single = true;
      } //end of if(BVPLUS ...)

    if (BVUMINUS == lhs.GetKind())
      {
        //equation is of the form (-lhs0) = rhs
        ASTNode lhs0 = lhs[0];
        rhs = _simp->SimplifyTerm(_bm->CreateTerm(BVUMINUS,
                                                  rhs.GetValueWidth(), rhs));
        lhs = lhs0;
      }

    switch (lhs.GetKind())
      {
      case SYMBOL:
        {
            DoNotSolve_TheseVars.insert(lhs);

          //input is of the form x = rhs first make sure that the lhs
          //symbol does not occur on the rhs or that it has not been
          //solved for
          if (!single && VarSeenInTerm(lhs, rhs))
            {
              //found the lhs in the rhs. Abort!
              return eq;
            }

          //rhs should not have arrayreads in it. it complicates matters
          //during transformation
          // if(CheckForArrayReads_TopLevel(rhs)) {
          //            return eq;
          //       }

          if (!_simp->UpdateSolverMap(lhs, rhs))
            {
              return eq;
            }

          output = ASTTrue;
          break;
        }
        //              case READ:
        //              {
        //                if(BVCONST != lhs[1].GetKind() 
        //                   || READ != rhs.GetKind() || 
        //                     BVCONST != rhs[1].GetKind() || lhs == rhs) 
        //                {
        //                  return eq;
        //                }
        //                else 
        //                {
        //                  DoNotSolve_TheseVars.insert(lhs);
        //                  if (!_simp->UpdateSolverMap(lhs, rhs))
        //                    {
        //                      return eq;
        //                    }

        //                  output = ASTTrue;
        //                  break;                  
        //                }
        //              }
      case BVEXTRACT:
        {
          const ASTNode zero = _bm->CreateZeroConst(32);

          if (!(SYMBOL == lhs[0].GetKind() 
                && BVCONST == lhs[1].GetKind() 
                && zero == lhs[2] 
                && !VarSeenInTerm(lhs[0], rhs) 
                && !DoNotSolveThis(lhs[0])))
            {
              return eq;
            }

          if (VarSeenInTerm(lhs[0], rhs))
            {
              DoNotSolve_TheseVars.insert(lhs[0]);
              return eq;
            }

          DoNotSolve_TheseVars.insert(lhs[0]);
          if (!_simp->UpdateSolverMap(lhs, rhs))
            {
              return eq;
            }

          if (lhs[0].GetValueWidth() != lhs.GetValueWidth())
          {
          //if the extract of x[i:0] = t is entered into the solvermap,
          //then also add another entry for x = x1@t
          ASTNode var = lhs[0];
          ASTNode newvar = 
            _bm->NewVar(var.GetValueWidth() - lhs.GetValueWidth());
          newvar = 
            _bm->CreateTerm(BVCONCAT, var.GetValueWidth(), newvar, rhs);
			  assert(BVTypeCheck(newvar));
          _simp->UpdateSolverMap(var, newvar);
          }
          else
        	  _simp->UpdateSolverMap(lhs[0], rhs);
          output = ASTTrue;
          break;
        }
      case BVMULT:
        {
          //the input is of the form a*x = t. If 'a' is odd, then compute
          //its multiplicative inverse a^-1, multiply 't' with it, and
          //update the solver map
          if (BVCONST != lhs[0].GetKind())
            {
              return eq;
            }

          if (!(SYMBOL == lhs[1].GetKind()
                || (BVEXTRACT == lhs[1].GetKind()
                    && SYMBOL == lhs[1][0].GetKind())))
            {
              return eq;
            }

          bool ChosenVar_Is_Extract = 
            (BVEXTRACT == lhs[1].GetKind());

          //if coeff is even, then we know that all the coeffs in the eqn
          //are even. Simply return the eqn
          if (!_simp->BVConstIsOdd(lhs[0]))
            {
              return eq;
            }

          ASTNode a = _simp->MultiplicativeInverse(lhs[0]);
          ASTNode chosenvar = 
        		  ChosenVar_Is_Extract ? lhs[1][0] : lhs[1];
          ASTNode chosenvar_value = 
            _simp->SimplifyTerm(_bm->CreateTerm(BVMULT, 
                                                rhs.GetValueWidth(), 
                                                a, rhs));

          //if chosenvar is seen in chosenvar_value then abort
          if (VarSeenInTerm(chosenvar, chosenvar_value))
            {
              //abort solving
              DoNotSolve_TheseVars.insert(lhs);
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
          if (!_simp->UpdateSolverMap(chosenvar, chosenvar_value))
            {
              return eq;
            }

          if (ChosenVar_Is_Extract)
            {
              const ASTNode& var = lhs[1][0];
              ASTNode newvar = 
                _bm->NewVar(var.GetValueWidth() - lhs[1].GetValueWidth());
              newvar = 
                _bm->CreateTerm(BVCONCAT, 
                                var.GetValueWidth(), 
                                newvar, chosenvar_value);
              _simp->UpdateSolverMap(var, newvar);
            }
          output = ASTTrue;
          break;
        }
      default:
        output = eq;
        break;
      }

    UpdateAlreadySolvedMap(input, output);
    return output;
  } //end of BVSolve_Odd()

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
  ASTNode BVSolver::TopLevelBVSolve(const ASTNode& _input)
  {
    //    if (!wordlevel_solve_flag)
    //       {
    //         return input;
    //       }
	  ASTNode input = _input;

    Kind k = input.GetKind();
    if (!(EQ == k || AND == k))
      {
        return input;
      }

    ASTNode output = input;
    if (CheckAlreadySolvedMap(input, output))
      {
        //output is TRUE. The formula is thus dropped
        return output;
      }

    if (flatten_ands && AND == k)
    {
		ASTNode n = input;
		while (true) {
			ASTNode nold = n;
			n = _simp->FlattenOneLevel(n);
			if ((n == nold))
				break;
		}

		input = n;

		// When flattening simplifications will be applied to the node, potentially changing it's type:
		// (AND x (ANY (not x) y)) gives us FALSE.
		if (!(EQ == n.GetKind() || AND == n.GetKind())) {
			{
				return n;
			}
		}
    }

    _bm->GetRunTimes()->start(RunTimes::BVSolver);
    ASTVec o;
    ASTVec c;
    if (EQ == k)
      c.push_back(input);
    else
      c = input.GetChildren();

    if (sort_extracts_last)
    	specialSort(c);

    ASTVec eveneqns;
    bool any_solved = false;
    for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        //_bm->ASTNodeStats("Printing before calling simplifyformula
        //inside the solver:", *it);

    	// Calling simplifyFormula makes the required substitutions. For instance, if
    	// first was : v = x,
    	// then if the next formula is: x = v
    	// calling simplify on the second formula will convert it into "true", avoiding a cycle.
    	ASTNode aaa =
          (any_solved
           && EQ == it->GetKind()) ?
          _simp->SimplifyFormula(*it, false) :
          *it;
        //_bm->ASTNodeStats("Printing after calling simplifyformula
        //inside the solver:", aaa);
        aaa = BVSolve_Odd(aaa);

        //_bm->ASTNodeStats("Printing after oddsolver:", aaa);
        bool even = false;
        aaa = CheckEvenEqn(aaa, even);
        if (even)
          {
            eveneqns.push_back(aaa);
          }
        else
          {
            if (ASTTrue != aaa)
              {
                o.push_back(aaa);
              }
          }
        if (ASTTrue == aaa)
        	any_solved=true;
      }

    ASTNode evens;
    if (eveneqns.size() > 0)
      {
        //if there is a system of even equations then solve them
        evens =
          (eveneqns.size() > 1) ? 
          _bm->CreateNode(AND, eveneqns) : 
          eveneqns[0];
        //evens = _simp->SimplifyFormula(evens,false);
        evens = BVSolve_Even(evens);
        _bm->ASTNodeStats("Printing after evensolver:", evens);
      }
    else
      {
        evens = ASTTrue;
      }
    output = 
      (o.size() > 0) ? 
      ((o.size() > 1) ? 
       _bm->CreateNode(AND, o) : 
       o[0]) : 
      ASTTrue;
    output = _bm->CreateNode(AND, output, evens);

    UpdateAlreadySolvedMap(_input, output);
    _bm->GetRunTimes()->stop(RunTimes::BVSolver);
    return output;
  } //end of TopLevelBVSolve()

  ASTNode BVSolver::CheckEvenEqn(const ASTNode& input, bool& evenflag)
  {
    ASTNode eq = input;
    //cerr << "Input to BVSolve_Odd()" << eq << endl;
    if (!(EQ == eq.GetKind()))
      {
        evenflag = false;
        return eq;
      }

    ASTNode lhs = eq[0];
    ASTNode rhs = eq[1];
    const ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
    //lhs must be a BVPLUS, and rhs must be a BVCONST
    if (!(BVPLUS == lhs.GetKind() && zero == rhs))
      {
        evenflag = false;
        return eq;
      }

    const ASTVec& lhs_c = lhs.GetChildren();
    ASTNode savetheconst = rhs;
    for (ASTVec::const_iterator
           it = lhs_c.begin(), itend = lhs_c.end(); it != itend; it++)
      {
        const ASTNode aaa = *it;
        const Kind itk = aaa.GetKind();

        if (BVCONST == itk)
          {
            //check later if the constant is even or not
            savetheconst = aaa;
            continue;
          }

        if (!(BVMULT == itk 
              && BVCONST == aaa[0].GetKind() 
              && SYMBOL == aaa[1].GetKind() 
              && !_simp->BVConstIsOdd(aaa[0])))
          {
            //If the monomials of the lhs are NOT of the form 'a*x' where
            //'a' is even, then return the false
            evenflag = false;
            return eq;
          }
      }//end of for loop

    //if control is here then it means that all coeffs are even. the
    //only remaining thing is to check if the constant is even or not
    if (_simp->BVConstIsOdd(savetheconst))
      {
        //the constant turned out to be odd. we have UNSAT eqn
        evenflag = false;
        return ASTFalse;
      }

    //all is clear. the eqn in even, through and through
    evenflag = true;
    return eq;
  } //end of CheckEvenEqn

  //solve an eqn whose monomials have only even coefficients
  ASTNode BVSolver::BVSolve_Even(const ASTNode& input)
  {
    //     if (!wordlevel_solve_flag)
    //       {
    //         return input;
    //       }

    if (!(EQ == input.GetKind() || AND == input.GetKind()))
      {
        return input;
      }

    ASTNode output;
    if (CheckAlreadySolvedMap(input, output))
      {
        return output;
      }

    ASTVec input_c;
    if (EQ == input.GetKind())
      {
        input_c.push_back(input);
      }
    else
      {
        input_c = input.GetChildren();
      }

    //power_of_2 holds the exponent of 2 in the coeff
    unsigned int power_of_2 = 0;
    //we need this additional variable to find the lowest power of 2
    unsigned int power_of_2_lowest = ~0;
    //the monom which has the least power of 2 in the coeff
    //ASTNode monom_with_best_coeff;
    for (ASTVec::iterator 
           jt = input_c.begin(), jtend = input_c.end(); 
         jt != jtend; jt++)
      {
        ASTNode eq = *jt;
        assert(EQ == eq.GetKind());
        ASTNode lhs = eq[0];
        ASTNode rhs = eq[1];
        ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
        //lhs must be a BVPLUS, and rhs must be a BVCONST
        if (!(BVPLUS == lhs.GetKind() && zero == rhs))
          {
            return input;
          }

        const ASTVec& lhs_c = lhs.GetChildren();
        for (ASTVec::const_iterator
               it = lhs_c.begin(), itend = lhs_c.end(); 
             it != itend; it++)
          {
            const ASTNode aaa = *it;
            const Kind itk = aaa.GetKind();
            if (!(BVCONST == itk 
                  && !_simp->BVConstIsOdd(aaa)) 
                && !(BVMULT == itk 
                     && BVCONST == aaa[0].GetKind() 
                     && SYMBOL == aaa[1].GetKind()
                     && !_simp->BVConstIsOdd(aaa[0])))
              {
                //If the monomials of the lhs are NOT of the form 'a*x' or 'a'
                //where 'a' is even, then return the eqn
                return input;
              }

            //we are gauranteed that if control is here then the monomial is
            //of the form 'a*x' or 'a', where 'a' is even
            ASTNode coeff = (BVCONST == itk) ? aaa : aaa[0];
            SplitEven_into_Oddnum_PowerOf2(coeff, power_of_2);
            if (power_of_2 < power_of_2_lowest)
              {
                power_of_2_lowest = power_of_2;
                //monom_with_best_coeff = aaa;
              }
            power_of_2 = 0;
          }//end of inner for loop
      } //end of outer for loop

    //get the exponent
    power_of_2 = power_of_2_lowest;
    assert(power_of_2 > 0);

    //if control is here, we are gauranteed that we have chosen a
    //monomial with fewest powers of 2
    ASTVec formula_out;
    for (ASTVec::iterator 
           jt = input_c.begin(), jtend = input_c.end(); jt != jtend; jt++)
      {
        ASTNode eq = *jt;
        ASTNode lhs = eq[0];
        ASTNode rhs = eq[1];
        ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
        //lhs must be a BVPLUS, and rhs must be a BVCONST
        if (!(BVPLUS == lhs.GetKind() && zero == rhs))
          {
            return input;
          }

        unsigned len = lhs.GetValueWidth();
        ASTNode hi = _bm->CreateBVConst(32, len - 1);
        ASTNode low = _bm->CreateBVConst(32, len - power_of_2);
        ASTNode low_minus_one = _bm->CreateBVConst(32, len - power_of_2 - 1);
        ASTNode low_zero = _bm->CreateZeroConst(32);
        unsigned newlen = len - power_of_2;
        ASTNode two_const = _bm->CreateTwoConst(len);

        unsigned count = power_of_2;
        ASTNode two = two_const;
        while (--count)
          {
            two = 
              _simp->BVConstEvaluator(_bm->CreateTerm(BVMULT, 
                                                      len, 
                                                      two_const, 
                                                      two));
          }
        const ASTVec& lhs_c = lhs.GetChildren();
        ASTVec lhs_out;
        for (ASTVec::const_iterator
               it = lhs_c.begin(), itend = lhs_c.end(); 
             it != itend; it++)
          {
            ASTNode aaa = *it;
            const Kind itk = aaa.GetKind();
            if (BVCONST == itk)
              {
                aaa = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVDIV, 
                                                          len, 
                                                          aaa, two));
                aaa = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, 
                                                          newlen, 
                                                          aaa, 
                                                          low_minus_one, 
                                                          low_zero));
              }
            else
              {
                //it must be of the form a*x
                ASTNode coeff = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVDIV, 
                                                          len, 
                                                          aaa[0], two));
                coeff = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, 
                                                          newlen, 
                                                          coeff, 
                                                          low_minus_one, 
                                                          low_zero));
                ASTNode lower_x =
                  _simp->SimplifyTerm(_bm->CreateTerm(BVEXTRACT, 
                                                      newlen, 
                                                      aaa[1], 
                                                      low_minus_one, 
                                                      low_zero));
                aaa = _bm->CreateTerm(BVMULT, newlen, coeff, lower_x);
              }
            lhs_out.push_back(aaa);
          }//end of inner forloop()
        rhs = _bm->CreateZeroConst(newlen);
        lhs = _bm->CreateTerm(BVPLUS, newlen, lhs_out);
        formula_out.push_back(_simp->CreateSimplifiedEQ(lhs, rhs));
      } //end of outer forloop()

    output = 
      (formula_out.size() > 0) ? 
      (formula_out.size() > 1) ? 
      _bm->CreateNode(AND, formula_out) : 
      formula_out[0] : 
      ASTTrue;

    UpdateAlreadySolvedMap(input, output);
    return output;
  } //end of BVSolve_Even()


	// This builds a reduced version of a graph, where there
    // is only a new node if the number of non-array SYMBOLS
    // in the descendents changes. For example (EXTRACT 0 1 n)
    // will have the same "Symbols" node as n, because
    // no new symbols are introduced.
	Symbols* BVSolver::BuildSymbolGraph(const ASTNode& n)
	{
	if (symbol_graph.find(n) != symbol_graph.end())
	{
		return symbol_graph[n];
	}

	Symbols* node;

	// Note we skip array variables. We never solve for them so
	// can ignore them.
	if (n.GetKind() == SYMBOL && n.GetIndexWidth() == 0) {
		node = new Symbols(n);
		symbol_graph.insert(make_pair(n, node));
		return node;
	}

	vector<Symbols*> children;
	for (int i = 0; i < n.Degree(); i++) {
		Symbols* v = BuildSymbolGraph(n[i]);
		if (!v->empty())
			children.push_back(v);
	}

	if (children.size() == 1) {
		// If there is only a single child with a symbol. Then jump to it.
		node = children.back();
	}
	else
		node = new Symbols(children);

	symbol_graph.insert(make_pair(n, node));

	return node;
	}

	// Builds a set of the SYMBOLS that were found under the "term". The symbols are the union of "found" and
	// all the sets : TermsAlreadySeen(av[0]) union ... TermsAlreadySeen(av[n])".
	  void BVSolver::VarSeenInTerm(Symbols* term, SymbolPtrSet& visited, ASTNodeSet& found, vector<Symbols*>& av)
	  {
		  if (visited.find(term) != visited.end())
		  {
			  return;
		  }
		SymbolPtrToNode::const_iterator it;
	    if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end())
	      {
	    	// We've previously built the set of variables below this "symbols".
	    	// It's not added into "found" because its sometimes 70k variables
	    	// big, and if there are no other symbols discovered it's a terrible
	    	// waste to create a copy of the set. Instead we store (in effect)
	    	// a pointer to the set.
	    	av.push_back(term);
	    	return;
	      }

	    if (term->isLeaf())
	    {
	    	found.insert(term->found);
	    	return;
	    }

	    for (vector<Symbols*>::const_iterator
	           it = term->children.begin(), itend = term->children.end();
	         it != itend; it++)
	      {
	        VarSeenInTerm(*it,visited,found,av);
	      }

	    visited.insert(term);
	    return;
	  }//End of VarSeenInTerm

	  bool BVSolver::VarSeenInTerm(const ASTNode& var, const ASTNode& term)
	  {
		  // This only returns true if we are searching for variables that aren't arrays.
		  assert(var.GetKind() == SYMBOL && var.GetIndexWidth() == 0);
		  BuildSymbolGraph(term);

		  SymbolPtrSet visited;
		  ASTNodeSet symbols;
		  vector<Symbols*> av;
		  VarSeenInTerm(symbol_graph[term],visited,symbols,av);

		  bool result = (symbols.count(var) !=0);
		  for (int i =0 ; i < av.size();i++)
		  {
			  if (result)
				  break;
			  const ASTNodeSet& sym = TermsAlreadySeenMap.find(av[i])->second;
			  result |= (sym.find(var) !=sym.end());
		  }

		  if (visited.size() > 50) // No use caching it, unless we've done some work.
		  {
			  for (int i =0 ; i < av.size();i++)
			  {
				  const ASTNodeSet& sym = TermsAlreadySeenMap.find(av[i])->second;
				  symbols.insert(sym.begin(), sym.end());
			  }
			  TermsAlreadySeenMap.insert(make_pair(symbol_graph[term],symbols));
		  }
		  return result;
	  }


};//end of namespace BEEV

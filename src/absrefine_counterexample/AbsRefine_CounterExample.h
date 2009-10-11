// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef CTREXAMPLE_H
#define CTREXAMPLE_H

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"
#include "../AST/ArrayTransformer.h"
#include "../to-sat/ToSAT.h"

namespace BEEV
{
  class AbsRefine_CounterExample
    {
    private:

      // Handy defs
      ASTNode ASTTrue, ASTFalse, ASTUndefined;

      // Data structure that holds the counterexample
      ASTNodeMap CounterExampleMap;
            
      // This map for building/printing counterexamples. MINISAT
      // returns values for each bit (a BVGETBIT Node), and this maps
      // allows us to assemble the bits into bitvectors.
      typedef hash_map<
	ASTNode, 
	hash_map<unsigned int, bool> *, 
	ASTNode::ASTNodeHasher, 
	ASTNode::ASTNodeEqual> ASTtoBitvectorMap;

      ASTtoBitvectorMap _ASTNode_to_Bitvector;

      // This memo map is used by the ComputeFormulaUsingModel()
      ASTNodeMap ComputeFormulaMap;
      
      // Ptr to STPManager
      BeevMgr * bm;
      
      // Ptr to Simplifier
      Simplifier * simp;

      // Ptr to ArrayTransformer
      ArrayTransformer * ArrayTransform;
      
      // Ptr to ToSAT
      ToSAT * tosat;

      // Checks if the counterexample is good. In order for the
      // counterexample to be ok, every assert must evaluate to true
      // w.r.t couner_example, and the query must evaluate to
      // false. Otherwise we know that the counter_example is bogus.
      void CheckCounterExample(bool t);

      // Accepts a term and turns it into a constant-term w.r.t
      // counter_example
      ASTNode TermToConstTermUsingModel(const ASTNode& term, 
					bool ArrayReadFlag = true);

      ASTNode Expand_ReadOverWrite_UsingModel(const ASTNode& term, 
					      bool ArrayReadFlag = true);

      void CopySolverMap_To_CounterExample(void);

      //Converts a vector of bools to a BVConst
      ASTNode BoolVectoBVConst(hash_map<unsigned, bool> * w, unsigned int l);

    public:

      // Constructor
      AbsRefine_CounterExample(BeevMgr * b, 
			       Simplifier * s, 
			       ArrayTransformer * at,
			       ToSAT * t) : 
	bm(b), simp(s), ArrayTransform(at), tosat(t)
      {
	ASTTrue  = bm->CreateNode(TRUE);
	ASTFalse = bm->CreateNode(FALSE);
	ASTUndefined = bm->CreateNode(UNDEFINED);
      }

      void ClearCounterExampleMap(void)
      {
	CounterExampleMap.clear();
      }

      void ClearComputeFormulaMap(void) 
	{
	  ComputeFormulaMap.clear();
	}

      //Converts MINISAT counterexample into an AST memotable (i.e. the
      //function populates the datastructure CounterExampleMap)
      void ConstructCounterExample(MINISAT::Solver& S);
      
      //Prints the counterexample to stdout
      void PrintCounterExample(bool t, std::ostream& os = cout);
      
      //Prints the counterexample to stdout
      void PrintCounterExample_InOrder(bool t);
      
      //queries the counterexample, and returns the value corresponding
      //to e
      ASTNode GetCounterExample(bool t, const ASTNode& e);
      
      int CounterExampleSize(void) const
	{
	  return CounterExampleMap.size();
	}

      //FIXME: This is bloody dangerous function. Hack attack to take
      //care of requests from users who want to store complete
      //counter-examples in their own data structures.
      ASTNodeMap GetCompleteCounterExample()
	{
	  return CounterExampleMap;
	}
      
      //Computes the truth value of a formula w.r.t counter_example
      ASTNode ComputeFormulaUsingModel(const ASTNode& form);


      // Prints MINISAT assigment one bit at a time, for debugging.
      void PrintSATModel(MINISAT::Solver& S);

      /****************************************************************
       * Array Refinement functions                                   *
       ****************************************************************/      
      SOLVER_RETURN_TYPE
      CallSAT_ResultCheck(MINISAT::Solver& SatSolver, 
			  const ASTNode& modified_input,
			  const ASTNode& original_input);  
      //creates array write axiom only for the input term or formula, if
      //necessary. If there are no axioms to produce then it simply
      //generates TRUE
      ASTNode 
      Create_ArrayWriteAxioms(const ASTNode& array_readoverwrite_term, 
			      const ASTNode& array_newname);
    
      SOLVER_RETURN_TYPE 
      SATBased_ArrayReadRefinement(MINISAT::Solver& newS, 
				   const ASTNode& modified_input, 
				   const ASTNode& original_input);

      SOLVER_RETURN_TYPE 
      SATBased_ArrayWriteRefinement(MINISAT::Solver& newS,
				    const ASTNode& orig_input);        
   
      //     SOLVER_RETURN_TYPE
      // SATBased_AllFiniteLoops_Refinement(MINISAT::Solver& newS,
      // const ASTNode& orig_input);
      
      //     ASTVec SATBased_FiniteLoop_Refinement(MINISAT::Solver&
      // SatSolver, const ASTNode& original_input, const ASTNode&
      // finiteloop, ASTNodeMap* ParamToCurrentValMap, bool
      // absrefine_flag=false);
      
      //     ASTNode Check_FiniteLoop_UsingModel(const ASTNode&
      // finiteloop, ASTNodeMap* ParamToCurrentValMap, bool
      // CheckUsingModel_Or_Expand);
      //
      //     ASTNode Expand_FiniteLoop_TopLevel(const ASTNode&
      //     finiteloop); ASTNode Check_FiniteLoop_UsingModel(const
      //     ASTNode& finiteloop);

    };//End of Class CounterExample

  class CompleteCounterExample
    {
      ASTNodeMap counterexample;
      BeevMgr * bv;
    public:
      CompleteCounterExample(ASTNodeMap a, BeevMgr* beev) :
	counterexample(a), bv(beev)
	{
	}
      ASTNode GetCounterExample(ASTNode e)
	{
	  if (BOOLEAN_TYPE == e.GetType() && SYMBOL != e.GetKind())
	    {
	      FatalError("You must input a term or propositional variables\n", e);
	    }
	  if (counterexample.find(e) != counterexample.end())
	    {
	      return counterexample[e];
	    }
	  else
	    {
	      if (SYMBOL == e.GetKind() && BOOLEAN_TYPE == e.GetType())
		{
		  return bv->CreateNode(BEEV::FALSE);
		}
	      
	      if (SYMBOL == e.GetKind())
		{
		  ASTNode z = bv->CreateZeroConst(e.GetValueWidth());
		  return z;
		}
	      
	      return e;
	    }
	}
    };//end of Class CompleteCounterExample
};//end of namespace
#endif

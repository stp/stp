// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <assert.h>
#include <math.h>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "AbsRefine_CounterExample.h"

namespace BEEV
{
  /******************************************************************
   * Abstraction Refinement related functions
   ******************************************************************/  

enum Polarity {LEFT_ONLY, RIGHT_ONLY, BOTH};

void getSatVariables(const ASTNode & a, vector<unsigned> & v_a, SATSolver & SatSolver, ToSATBase::ASTNodeToSATVar & satVar)
 {
	ToSATBase::ASTNodeToSATVar::iterator it = satVar.find(a);
	if (it != satVar.end())
		v_a = it->second;
	else
		if (!a.isConstant())
		{
			assert(a.GetKind() == SYMBOL);
			// It was ommitted from the initial problem, so assign it freshly.
			for(int i = 0;i < a.GetValueWidth();i++)
				v_a.push_back(SatSolver.newVar());
			satVar.insert(make_pair(a,v_a));
		}
 }


// This function adds the clauses to constrain (a=b)->c.
// Because it's used to create array axionms (a=b)-> (c=d), it can be
// used to only add one of the polarities..
Minisat::Var getEquals(SATSolver& SatSolver, const ASTNode& a, const ASTNode& b, ToSATBase::ASTNodeToSATVar& satVar, Polarity polary= BOTH)
{
	const int width = a.GetValueWidth();
	assert(width == b.GetValueWidth());
	assert(!a.isConstant() || !b.isConstant());

	vector<unsigned > v_a;
	vector<unsigned > v_b;

	getSatVariables(a,v_a,SatSolver,satVar);
	getSatVariables(b,v_b,SatSolver,satVar);

	// The only time v_a or v_b will be empty is if a resp. b is a constant.

	if (v_a.size() == width && v_b.size() == width)
	{
		SATSolver::vec_literals all;
		const int result = SatSolver.newVar();

		for (int i=0; i < width; i++)
		{
			SATSolver::vec_literals s;
			int nv0 = SatSolver.newVar();

			if (polary != RIGHT_ONLY)
			{
				s.push(SATSolver::mkLit(v_a[i], true));
				s.push(SATSolver::mkLit(v_b[i], true));
				s.push(SATSolver::mkLit(nv0, false));
				SatSolver.addClause(s);
				s.clear();

				s.push(SATSolver::mkLit(v_a[i], false));
				s.push(SATSolver::mkLit(v_b[i], false));
				s.push(SATSolver::mkLit(nv0, false));
				SatSolver.addClause(s);
				s.clear();
			}

			if (polary != LEFT_ONLY)
			{
				s.push(SATSolver::mkLit(v_a[i], true));
				s.push(SATSolver::mkLit(v_b[i], false));
				s.push(SATSolver::mkLit(nv0, true));
				SatSolver.addClause(s);
				s.clear();

				s.push(SATSolver::mkLit(v_a[i], false));
				s.push(SATSolver::mkLit(v_b[i], true));
				s.push(SATSolver::mkLit(nv0, true));
				SatSolver.addClause(s);
				s.clear();

				// result -> nv0 .. new.
				s.push(SATSolver::mkLit(result, true));
				s.push(SATSolver::mkLit(nv0, false));
				SatSolver.addClause(s);
				s.clear();
			}

			all.push(SATSolver::mkLit(nv0, true));
		}
		all.push(SATSolver::mkLit(result, false));

		SatSolver.addClause(all);
		return result;
	}
	else if (v_a.size() == 0 ^ v_b.size() ==0)
	{
		ASTNode constant = a.isConstant()? a:b;
		vector<unsigned > vec  = v_a.size() == 0? v_b : v_a;
		assert(constant.isConstant());
		assert(vec.size() == width);

		SATSolver::vec_literals all;
		const int result = SatSolver.newVar();
		all.push(SATSolver::mkLit(result, false));

		CBV v = constant.GetBVConst();
		for (int i=0; i < width; i++)
		{
			if (CONSTANTBV::BitVector_bit_test(v,i))
				all.push(SATSolver::mkLit(vec[i], true));
			else
				all.push(SATSolver::mkLit(vec[i], false));

			if (polary != LEFT_ONLY)
			{
				SATSolver::vec_literals p;
				p.push(SATSolver::mkLit(result, true));
				if (CONSTANTBV::BitVector_bit_test(v,i))
					p.push(SATSolver::mkLit(vec[i], false));
				else
					p.push(SATSolver::mkLit(vec[i], true));

				SatSolver.addClause(p);
			}

		}
		SatSolver.addClause(all);
		return result;
	}else
		FatalError("Unexpected, both must be constants..");

}


  /******************************************************************
   * ARRAY READ ABSTRACTION REFINEMENT
   *   
   * SATBased_ArrayReadRefinement()
   *
   * What it really does is, for each array, loop over each index i.
   * inside that loop, it finds all the true and false axioms with i
   * as first index.  When it's got them all, it adds the false axioms
   * to the formula and re-solves, and returns if the result is
   * correct.  Otherwise, it goes on to the next index.
   *
   * If it gets through all the indices without a correct result
   * (which I think is impossible), it then solves with all the true
   * axioms, too.
   *
   * This is not the most obvious way to do it, and I don't know how
   * it compares with other approaches (e.g., one false axiom at a
   * time or all the false axioms each time).
   *****************************************************************/
  struct AxiomToBe
  {
	  AxiomToBe(ASTNode i0, ASTNode i1, ASTNode v0, ASTNode v1)
	  {
		  index0 = i0;
		  index1 = i1;
		  value0 = v0;
		  value1 = v1;
	  }
	  ASTNode index0, index1;
	  ASTNode value0, value1;
 };

  void applyAxiomsToSolver(ToSATBase::ASTNodeToSATVar & satVar, vector<AxiomToBe>& toBe, SATSolver & SatSolver)
   {
        for(int i = 0;i < toBe.size();i++){
           Minisat::Var a = getEquals(SatSolver, toBe[i].index0, toBe[i].index1, satVar, LEFT_ONLY);
           Minisat::Var b = getEquals(SatSolver, toBe[i].value0, toBe[i].value1, satVar, RIGHT_ONLY);
           SATSolver::vec_literals satSolverClause;
           satSolverClause.push(SATSolver::mkLit(a, true));
           satSolverClause.push(SATSolver::mkLit(b, false));
           SatSolver.addClause(satSolverClause);
       }
        toBe.clear();
   }

  SOLVER_RETURN_TYPE 
  AbsRefine_CounterExample::
  SATBased_ArrayReadRefinement(SATSolver& SatSolver,
                               const ASTNode& inputAlreadyInSAT, 
                               const ASTNode& original_input,
                               ToSATBase* tosat) {

	vector<AxiomToBe> RemainingAxiomsVec;
	vector<AxiomToBe> FalseAxiomsVec;

	// NB. Because we stop this timer before entering the SAT solver, the count
	// it produces isn't the number of times Array Read Refinement was entered.
	bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);

    //in these loops we try to construct Leibnitz axioms and add it to
    //the solve(). We add only those axioms that are false in the
    //current counterexample. we keep adding the axioms until there
    //are no more axioms to add
    //
    //for each array, fetch its list of indices seen so far
    for (ArrayTransformer::ArrType::const_iterator
           iset = ArrayTransform->arrayToIndexToRead.begin(),
           iset_end = ArrayTransform->arrayToIndexToRead.end();
         iset != iset_end; iset++)
      {
    	const ASTNode& ArrName = iset->first;
    	const map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

        vector<ASTNode> listOfIndices;
        listOfIndices.reserve(mapper.size());

    	// Make a vector of the read symbols.
    	ASTVec read_node_symbols;
    	read_node_symbols.reserve(listOfIndices.size());

    	vector<Kind> jKind;
    	jKind.reserve(mapper.size());

    	vector<ASTNode> concreteIndexes;
    	concreteIndexes.reserve(mapper.size());

    	vector<ASTNode> concreteValues;
    	concreteValues.reserve(mapper.size());

    	ASTVec index_symbols;

    	for (map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator it =mapper.begin() ; it != mapper.end();it++)
    	{
    	    const ASTNode& the_index = it->first;
            listOfIndices.push_back(the_index);

            ASTNode arrsym = it->second.symbol;
            read_node_symbols.push_back(arrsym);

            index_symbols.push_back(it->second.index_symbol);

			assert(read_node_symbols[0].GetValueWidth() == arrsym.GetValueWidth());
			assert(listOfIndices[0].GetValueWidth() == the_index.GetValueWidth());

            jKind.push_back(the_index.GetKind());

            concreteIndexes.push_back(TermToConstTermUsingModel(the_index));
            concreteValues.push_back(TermToConstTermUsingModel(arrsym));
    	}

    	assert(listOfIndices.size() == mapper.size());

        //loop over the list of indices for the array and create LA,
        //and add to inputAlreadyInSAT
        for (int i = 0; i < listOfIndices.size(); i++)
          {
        	const ASTNode& index_i = listOfIndices[i];
        	const Kind iKind = index_i.GetKind();

            // Create all distinct pairs of indexes.
            for (int j = i+1; j < listOfIndices.size(); j++)
              {
            	const ASTNode& index_j = listOfIndices[j];

            	// If the index is a constant, and different, then there's no reason to check.
            	// Sometimes we get the same index stored multiple times in the array. Not sure why...
            	if (BVCONST == iKind && jKind[j] == BVCONST && index_i != index_j)
            		continue;

                if (ASTFalse == simp->CreateSimplifiedEQ(index_i, index_j))
                	continue; // shortcut.

            	AxiomToBe o (index_symbols[i],index_symbols[j],  read_node_symbols[i], read_node_symbols[j]);

                if (concreteIndexes[i] == concreteIndexes[j] && concreteValues[i] != concreteValues[j])
                  {
                	FalseAxiomsVec.push_back(o);
                	//ToSATBase::ASTNodeToSATVar	& satVar = tosat->SATVar_to_SymbolIndexMap();
                	//applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);
                }
                else
                	RemainingAxiomsVec.push_back(o);
              }
            if ( FalseAxiomsVec.size() > 0)
            {
            	ToSATBase::ASTNodeToSATVar	& satVar = tosat->SATVar_to_SymbolIndexMap();
            	applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);

            	SOLVER_RETURN_TYPE res2;
				bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
				res2 =  CallSAT_ResultCheck(SatSolver,
									  ASTTrue,
									  original_input,
									  tosat,
									  true);

				if (SOLVER_UNDECIDED != res2)
					return res2;
				bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
            }
          }
      }

    if (RemainingAxiomsVec.size() > 0)
    {
    	ToSATBase::ASTNodeToSATVar	& satVar = tosat->SATVar_to_SymbolIndexMap();
    	applyAxiomsToSolver(satVar, RemainingAxiomsVec, SatSolver);

		bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
		return CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
				tosat,true);
	}

	bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);

    return SOLVER_UNDECIDED;
  } //end of SATBased_ArrayReadRefinement


  /******************************************************************
   * ARRAY WRITE ABSTRACTION REFINEMENT
   *
   * FIXME: Write Detailed Comment
   *****************************************************************/
  SOLVER_RETURN_TYPE 
  AbsRefine_CounterExample::
  SATBased_ArrayWriteRefinement(SATSolver& SatSolver,
                                const ASTNode& original_input,
                                ToSATBase *tosat
                              )
  {
    ASTNode writeAxiom;
    ASTNodeMap::const_iterator it = simp->ReadOverWriteMap()->begin();
    ASTNodeMap::const_iterator itend = simp->ReadOverWriteMap()->end();

    ASTVec FalseAxioms, RemainingAxioms;
    RemainingAxioms.push_back(ASTTrue);
    for (; it != itend; it++)
      {
        //Guided refinement starts here
        ClearComputeFormulaMap();
        writeAxiom = Create_ArrayWriteAxioms(it->first, it->second);
        if (ASTFalse == ComputeFormulaUsingModel(writeAxiom))
          {
            writeAxiom = ArrayTransform->TransformFormula_TopLevel(writeAxiom);
            FalseAxioms.push_back(writeAxiom);
          }
        else
          {
            writeAxiom = ArrayTransform->TransformFormula_TopLevel(writeAxiom);
            RemainingAxioms.push_back(writeAxiom);
          }
      }

    SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
    if (FalseAxioms.size() > 0)
    {
		writeAxiom = (FalseAxioms.size() != 1) ? bm->CreateNode(AND,
				FalseAxioms) : FalseAxioms[0];
		bm->ASTNodeStats("adding false writeaxiom to SAT: ", writeAxiom);
		res2 = CallSAT_ResultCheck(SatSolver, writeAxiom, original_input, tosat,true);
	}

    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    if (RemainingAxioms.size() > 0)
    {
		writeAxiom =
		  (RemainingAxioms.size() != 1) ?
		  bm->CreateNode(AND, RemainingAxioms) : RemainingAxioms[0];
		bm->ASTNodeStats("adding remaining writeaxiom to SAT: ", writeAxiom);
		res2 = CallSAT_ResultCheck(SatSolver,
								   writeAxiom,
								   original_input,
								   tosat, true);
    }
    return res2;
  } //end of SATBased_ArrayWriteRefinement
  
  //Creates Array Write Axioms
  ASTNode 
  AbsRefine_CounterExample::Create_ArrayWriteAxioms(const ASTNode& term, 
                                                    const ASTNode& newvar)
  {
    if (READ != term.GetKind() && WRITE != term[0].GetKind())
      {
        FatalError("Create_ArrayWriteAxioms: "\
                   "Input must be a READ over a WRITE", term);
      }

    ASTNode lhs = newvar;
    ASTNode rhs = term;
    ASTNode arraywrite_axiom = simp->CreateSimplifiedEQ(lhs, rhs);
    return arraywrite_axiom;
  }//end of Create_ArrayWriteAxioms()

};// end of namespace BEEV

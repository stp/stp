// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
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
  SOLVER_RETURN_TYPE 
  AbsRefine_CounterExample::
  SATBased_ArrayReadRefinement(SATSolver& SatSolver,
                               const ASTNode& inputAlreadyInSAT, 
                               const ASTNode& original_input,
                               ToSATBase* tosat) {

	ASTVec FalseAxiomsVec, RemainingAxiomsVec;

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

    	for (map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator it =mapper.begin() ; it != mapper.end();it++)
    	{
    	    const ASTNode& the_index = it->first;
            listOfIndices.push_back(the_index);

            ASTNode arrsym = it->second.symbol;
            read_node_symbols.push_back(arrsym);

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
            	{
            		continue;
            	}

            	//prepare for SAT LOOP
                //first construct the antecedent for the LA axiom
                ASTNode eqOfIndices = 
                  (exprless(index_i, index_j)) ? 
                  simp->CreateSimplifiedEQ(index_i, index_j) : 
                  simp->CreateSimplifiedEQ(index_j, index_i);

                if (ASTFalse == eqOfIndices)
                	continue; // shortuct.

                ASTNode eqOfReads = simp->CreateSimplifiedEQ(read_node_symbols[i], read_node_symbols[j]);
                //construct appropriate Leibnitz axiom
                ASTNode LeibnitzAxiom = 
                  bm->CreateNode(IMPLIES, eqOfIndices, eqOfReads);
                if (concreteIndexes[i] == concreteIndexes[j] && concreteValues[i] != concreteValues[j])
                  {
                    FalseAxiomsVec.push_back(LeibnitzAxiom);
                    //cerr << "index:" << index_i << " " <<  index_j;
                    //cerr << read_node_symbols[i];
                    //cerr << read_node_symbols[j];
                  }
                else
                  {
                    RemainingAxiomsVec.push_back(LeibnitzAxiom);
                  }
              }
            if (FalseAxiomsVec.size() > 0)
            {
				ASTNode FalseAxioms =
				  (FalseAxiomsVec.size() > 1) ?
				  bm->CreateNode(AND, FalseAxiomsVec) : FalseAxiomsVec[0];
				bm->ASTNodeStats("adding false readaxioms to SAT: ", FalseAxioms);
				SOLVER_RETURN_TYPE res2;
				bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
				res2 =  CallSAT_ResultCheck(SatSolver,
									  FalseAxioms,
									  original_input,
									  tosat,
									  true);
				FalseAxiomsVec.clear();

				if (SOLVER_UNDECIDED != res2)
				  {
					return res2;
				  }
				bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
            }
          }
      }
    if (RemainingAxiomsVec.size() > 0)
    {
		ASTNode RemainingAxioms =
				(RemainingAxiomsVec.size() > 1) ? bm->CreateNode(AND,
						RemainingAxiomsVec) : RemainingAxiomsVec[0];
		bm->ASTNodeStats("adding remaining readaxioms to SAT: ",
				RemainingAxioms);
		bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
		return CallSAT_ResultCheck(SatSolver, RemainingAxioms, original_input,
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

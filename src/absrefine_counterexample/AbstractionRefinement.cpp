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

    //in these loops we try to construct Leibnitz axioms and add it to
    //the solve(). We add only those axioms that are false in the
    //current counterexample. we keep adding the axioms until there
    //are no more axioms to add
    //
    //for each array, fetch its list of indices seen so far
    for (ASTNodeToVecMap::const_iterator 
           iset = ArrayTransform->ArrayName_ReadIndicesMap()->begin(),
           iset_end = ArrayTransform->ArrayName_ReadIndicesMap()->end(); 
         iset != iset_end; iset++)
      {
    	const ASTNode& ArrName = iset->first;
    	const ASTVec& listOfIndices = iset->second;

    	// Make a vector of the read symbols.
    	ASTVec read_node_symbols;
    	read_node_symbols.reserve(listOfIndices.size());
    	for (int i = 0; i < listOfIndices.size(); i++)
    	{
        	const ASTNode& the_index = listOfIndices[i];

        	ASTNode arr_read =
              bm->CreateTerm(READ, ArrName.GetValueWidth(), ArrName, the_index);

        	ASTNode arrsym = ArrayTransform->ArrayRead_SymbolMap(arr_read);
        	assert ((SYMBOL == arrsym.GetKind() || BVCONST == arrsym.GetKind()));

        	read_node_symbols.push_back(arrsym);
    	}

        //loop over the list of indices for the array and create LA,
        //and add to inputAlreadyInSAT
        for (int i = 0; i < listOfIndices.size(); i++)
          {
        	const ASTNode& index_i = listOfIndices[i];

            // Create all distinct pairs of indexes.
            for (int j = i+1; j < listOfIndices.size(); j++)
              {
            	const ASTNode& index_j = listOfIndices[j];

            	// We assume there are no duplicate constant indexes in the list of readindexes,
            	// so "i" and "j" will never be equal.
            	if (BVCONST == index_i.GetKind() && index_j.GetKind() == BVCONST)
            	{
            		assert(index_i != index_j);
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
                if (ASTFalse == ComputeFormulaUsingModel(LeibnitzAxiom))
                  {
                    FalseAxiomsVec.push_back(LeibnitzAxiom);
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
				res2 =  CallSAT_ResultCheck(SatSolver,
									  FalseAxioms,
									  original_input,
									  tosat);
				FalseAxiomsVec.clear();

				if (SOLVER_UNDECIDED != res2)
				  {
					return res2;
				  }
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
		return CallSAT_ResultCheck(SatSolver, RemainingAxioms, original_input,
				tosat);
	}
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
    unsigned int oldFalseAxiomsSize = 0;
    //int count = 0;
    //int num_write_axioms = ReadOverWrite_NewName_Map.size();

    ASTVec FalseAxioms, RemainingAxioms;
    FalseAxioms.push_back(ASTTrue);
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

    writeAxiom = 
      (FalseAxioms.size() != 1) ? 
      bm->CreateNode(AND, FalseAxioms) : FalseAxioms[0];
    bm->ASTNodeStats("adding false writeaxiom to SAT: ", writeAxiom);
    SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
    if (FalseAxioms.size() > oldFalseAxiomsSize)
      {
        res2 = CallSAT_ResultCheck(SatSolver, 
                                   writeAxiom, 
                                   original_input,
                                   tosat);
        oldFalseAxiomsSize = FalseAxioms.size();
      }
    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    writeAxiom = 
      (RemainingAxioms.size() != 1) ? 
      bm->CreateNode(AND, RemainingAxioms) : RemainingAxioms[0];
    bm->ASTNodeStats("adding remaining writeaxiom to SAT: ", writeAxiom);
    res2 = CallSAT_ResultCheck(SatSolver, 
                               writeAxiom, 
                               original_input,
                               tosat);
    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    return SOLVER_UNDECIDED;
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

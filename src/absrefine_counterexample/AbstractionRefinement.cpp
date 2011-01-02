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
    //printf("doing array read refinement\n");
    // if (!bm->UserFlags.arrayread_refinement_flag)
    //       {
    //         FatalError("SATBased_ArrayReadRefinement: "	\
    //                    "Control should not reach here");
    //       }
    ASTVec FalseAxiomsVec, RemainingAxiomsVec;
    RemainingAxiomsVec.push_back(ASTTrue);
    FalseAxiomsVec.push_back(ASTTrue);
    unsigned int oldFalseAxiomsSize = 0;

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
        ASTVec listOfIndices = iset->second;
        //loop over the list of indices for the array and create LA,
        //and add to inputAlreadyInSAT
        for (ASTVec::iterator it = listOfIndices.begin(),
               itend = listOfIndices.end(); it != itend; it++)
          {
            if (BVCONST == it->GetKind())
              {
                continue;
              }

            ASTNode the_index = *it;
            //get the arrayname
            ASTNode ArrName = iset->first;
            // if(SYMBOL != ArrName.GetKind())
            //        FatalError("SATBased_ArrayReadRefinement: "\
            // "arrname is not a SYMBOL",ArrName);
            ASTNode arr_read1 = 
              bm->CreateTerm(READ, ArrName.GetValueWidth(), ArrName, the_index);
            //get the variable corresponding to the array_read1
            //ASTNode arrsym1 = _arrayread_symbol[arr_read1];
            ASTNode arrsym1 = ArrayTransform->ArrayRead_SymbolMap(arr_read1);
            if (!(SYMBOL == arrsym1.GetKind() || BVCONST == arrsym1.GetKind()))
              FatalError("TopLevelSAT: refinementloop:"
                         "term arrsym1 corresponding to READ must be a var", 
                         arrsym1);

            //we have nonconst index here. create Leibnitz axiom for it
            //w.r.t every index in listOfIndices
            for (ASTVec::iterator it1 = listOfIndices.begin(), 
                   itend1 = listOfIndices.end(); it1 != itend1; it1++)
              {
                ASTNode compare_index = *it1;
                //do not compare with yourself
                if (the_index == compare_index)
                  continue;

                //prepare for SAT LOOP
                //first construct the antecedent for the LA axiom
                ASTNode eqOfIndices = 
                  (exprless(the_index, compare_index)) ? 
                  simp->CreateSimplifiedEQ(the_index, compare_index) : 
                  simp->CreateSimplifiedEQ(compare_index, the_index);

                ASTNode arr_read2 = 
                  bm->CreateTerm(READ, ArrName.GetValueWidth(),
                                 ArrName, compare_index);
                //get the variable corresponding to the array_read2
                //ASTNode arrsym2 = _arrayread_symbol[arr_read2];
                ASTNode arrsym2 = 
                  ArrayTransform->ArrayRead_SymbolMap(arr_read2);
                if (!(SYMBOL == arrsym2.GetKind() 
                      || BVCONST == arrsym2.GetKind()))
                  {
                    FatalError("TopLevelSAT: refinement loop:"
                               "term arrsym2 corresponding to "\
                               "READ must be a var", arrsym2);
                  }

                ASTNode eqOfReads = simp->CreateSimplifiedEQ(arrsym1, arrsym2);
                //construct appropriate Leibnitz axiom
                ASTNode LeibnitzAxiom = 
                  bm->CreateNode(IMPLIES, eqOfIndices, eqOfReads);
                if (ASTFalse == ComputeFormulaUsingModel(LeibnitzAxiom))
                  {
                    //FalseAxioms =
                    //bm->CreateNode(AND,FalseAxioms,LeibnitzAxiom);
                    FalseAxiomsVec.push_back(LeibnitzAxiom);
                  }
                else
                  {
                    //RemainingAxioms =
                    //bm->CreateNode(AND,RemainingAxioms,LeibnitzAxiom);
                    RemainingAxiomsVec.push_back(LeibnitzAxiom);
                  }
              }
            ASTNode FalseAxioms = 
              (FalseAxiomsVec.size() > 1) ? 
              bm->CreateNode(AND, FalseAxiomsVec) : FalseAxiomsVec[0];
            bm->ASTNodeStats("adding false readaxioms to SAT: ", FalseAxioms);
            //printf("spot 01\n");
            SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
            //if (FalseAxiomsVec.size() > 0)
            if (FalseAxiomsVec.size() > oldFalseAxiomsSize)
              {
                res2 = 
                  CallSAT_ResultCheck(SatSolver, 
                                      FalseAxioms, 
                                      original_input,
                                      tosat);
                oldFalseAxiomsSize = FalseAxiomsVec.size();
              }
            //printf("spot 02, res2 = %d\n", res2);
            if (SOLVER_UNDECIDED != res2)
              {
                return res2;
              }
          }
      }
    ASTNode RemainingAxioms = 
      (RemainingAxiomsVec.size() > 1) ? 
      bm->CreateNode(AND, RemainingAxiomsVec) : RemainingAxiomsVec[0];
    bm->ASTNodeStats("adding remaining readaxioms to SAT: ", RemainingAxioms);
    return CallSAT_ResultCheck(SatSolver, 
                               RemainingAxioms, 
                               original_input,
                               tosat);
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

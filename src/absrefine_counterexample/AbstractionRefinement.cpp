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
  SATBased_ArrayReadRefinement(MINISAT::Solver& SatSolver, 
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
  SATBased_ArrayWriteRefinement(MINISAT::Solver& SatSolver, 
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

  //   static void ReplaceOrAddToMap(ASTNodeMap * VarToConstMap, 
  //                            const ASTNode& key, const ASTNode& value)
  //   {
  //     ASTNodeMap::iterator it = VarToConstMap->find(key);
  //     if(it != VarToConstMap->end())
  //       {
  //    VarToConstMap->erase(it);       
  //       }

  //     (*VarToConstMap)[key] = value;
  //     return;   
  //   }


  //   /******************************************************************
  //    * FINITE FORLOOP ABSTRACTION REFINEMENT
  //    *
  //    * For each 'finiteloop' in the list 'GlobalList_Of_FiniteLoops'
  //    *
  //    * Expand_FiniteLoop(finiteloop);
  //    *
  //    * The 'Expand_FiniteLoop' function expands the 'finiteloop' in a
  //    * counterexample-guided refinement fashion
  //    *
  //    * Once all the finiteloops have been expanded, we need to go back
  //    * and recheck that every discarded constraint is true with the
  //    * final model. A flag 'done' is set to false if atleast one
  //    * constraint is false during model-check, and is set to true if all
  //    * constraints are true during model-check.
  //    *
  //    * if the 'done' flag is true, then we terminate this refinement
  //    * loop.  
  //    *****************************************************************/
  //   SOLVER_RETURN_TYPE 
  //   AbsRefine_CounterExample::
  //   SATBased_AllFiniteLoops_Refinement(MINISAT::Solver& SatSolver, 
  //                                          const ASTNode& original_input)
  //   {
  //     cout << "The number of abs-refinement limit is " 
  //          << num_absrefine << endl;
  //     for(int absrefine_count=0;
  //         absrefine_count < num_absrefine; absrefine_count++) 
  //       {
  //    ASTVec Allretvec0;
  //    Allretvec0.push_back(ASTTrue);
  //    SOLVER_RETURN_TYPE res = SOLVER_UNDECIDED;      
  //    for(ASTVec::iterator i = GlobalList_Of_FiniteLoops.begin(),
  //          iend=GlobalList_Of_FiniteLoops.end(); i!=iend; i++)
  //      {
  //        ASTVec retvec;
  //        ASTNodeMap ParamToCurrentValMap;
  //        retvec =  SATBased_FiniteLoop_Refinement(SatSolver,
  //                                                 original_input,
  //                                                 *i,
  //                                                 &ParamToCurrentValMap,
  //                                                 true); //absrefine flag

  //        for(ASTVec::iterator j=retvec.begin(),jend=retvec.end();
  //            j!=jend;j++) 
  //          {
  //            Allretvec0.push_back(*j);
  //          }
  //        //Allretvec0.(Allretvec0.end(),retvec.begin(),retvec.end());
  //      } //End of For
          
  //    ASTNode retformula = 
  //      (Allretvec0.size() == 1) ?
  //      Allretvec0[0] : bm->CreateNode(AND,Allretvec0);
  //    retformula = TransformFormula_TopLevel(retformula);
        
  //    //Add the return value of all loops to the SAT Solver
  //    res = 
  //      CallSAT_ResultCheck(SatSolver, retformula, original_input);
  //    if(SOLVER_UNDECIDED != res) 
  //      {
  //        return res;
  //      }     
  //       } //end of absrefine count
    
  //     ASTVec Allretvec1;
  //     Allretvec1.push_back(ASTTrue);
  //     SOLVER_RETURN_TYPE res = SOLVER_UNDECIDED;     
  //     for(ASTVec::iterator i = GlobalList_Of_FiniteLoops.begin(),
  //      iend=GlobalList_Of_FiniteLoops.end(); i!=iend; i++)
  //     {
  //       //cout << "The abs-refine didn't finish the job. "\
  //                 "Add the remaining formulas\n";
  //       ASTNodeMap ParamToCurrentValMap;
  //       ASTVec retvec;
  //       retvec =  SATBased_FiniteLoop_Refinement(SatSolver,
  //                                           original_input,
  //                                           *i,
  //                                           &ParamToCurrentValMap,
  //                                           false); //absrefine flag
  //       for(ASTVec::iterator j=retvec.begin(),jend=retvec.end();j!=jend;j++) 
  //    {
  //      Allretvec1.push_back(*j);
  //    }
  //     } //End of For    
        
  //     ASTNode retformula = 
  //       (Allretvec1.size() == 1) ?
  //       Allretvec1[0] : bm->CreateNode(AND,Allretvec1);
  //     retformula = TransformFormula_TopLevel(retformula);
  //     //Add the return value of all loops to the SAT Solver
  //     res = CallSAT_ResultCheck(SatSolver, retformula, original_input);
  //     return res;
  //   } //end of SATBased_AllFiniteLoops_Refinement()
  
  
  //   /*****************************************************************
  //    * SATBased_FiniteLoop_Refinement
  //    *
  //    * 'finiteloop' is the finite loop to be expanded
  //    * Every finiteloop has three parts:
  //    * 0) Parameter Name
  //    * 1) Parameter initialization
  //    * 2) Parameter limit value
  //    * 3) Increment formula
  //    * 4) Formula Body
  //    *
  //    * ParamToCurrentValMap contains a map from parameters to their
  //    * current values in the recursion
  //    *   
  //    * Nested FORs are allowed, but only the innermost loop can have a
  //    * formula in it
  //    *****************************************************************/
  //   //SATBased_FiniteLoop_Refinement
  //   //
  //   //Expand the finite loop, check against model, and add false
  //   //formulas to the SAT solver
  //   ASTVec
  //   AbsRefine_CounterExample::
  //   SATBased_FiniteLoop_Refinement(MINISAT::Solver& SatSolver, 
  //                                      const ASTNode& original_input,
  //                                      const ASTNode& finiteloop,
  //                                      ASTNodeMap* ParamToCurrentValMap,
  //                                      bool absrefine_flag)
  //   {     
  //     //BVTypeCheck should have already checked the sanity of the input
  //     //FOR-formula
  //     ASTNode parameter     = finiteloop[0];
  //     int paramInit         = GetUnsignedConst(finiteloop[1]);
  //     int paramLimit        = GetUnsignedConst(finiteloop[2]);
  //     int paramIncrement    = GetUnsignedConst(finiteloop[3]);
  //     ASTNode exceptFormula = finiteloop[4];
  //     ASTNode formulabody   = finiteloop[5];
  //     int paramCurrentValue = paramInit;
  //     int width             = finiteloop[1].GetValueWidth();

  //     //Update ParamToCurrentValMap with parameter and its current
  //     //value. Here paramCurrentValue is the initial value    
  //     ASTNode value =       
  //       bm->CreateBVConst(width,paramCurrentValue);
  //     ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);
    
  //     //Go recursively thru' all the FOR-constructs.
  //     if(FOR == formulabody.GetKind()) 
  //       { 
  //    ASTVec retvec;
  //    ASTVec retvec_innerfor;
  //    retvec.push_back(ASTTrue);
  //         while(paramCurrentValue < paramLimit) 
  //           {
  //             retvec_innerfor = 
  //          SATBased_FiniteLoop_Refinement(SatSolver, 
  //                                         original_input,
  //                                         formulabody, 
  //                                         ParamToCurrentValMap,
  //                                         absrefine_flag);

  //        for(ASTVec::iterator i=retvec_innerfor.begin(),
  //              iend=retvec_innerfor.end();i!=iend;i++)
  //          {
  //            retvec.push_back(*i);
  //          }

  //             //Update ParamToCurrentValMap with parameter and its
  //             //current value.
  //             paramCurrentValue = paramCurrentValue + paramIncrement;
  //        value = bm->CreateTerm(BVPLUS, 
  //                           width, 
  //                           (*ParamToCurrentValMap)[parameter],
  //                           bm->CreateOneConst(width));      
  //        ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);
  //           } //end of While

  //    return retvec;
  //       } //end of recursion FORs

  //     //Expand the leaf level FOR-construct completely
  //     //increment of paramCurrentValue done inside loop
  //     int ThisForLoopAllTrue = 0;
  //     ASTVec ForloopVec;
  //     ForloopVec.push_back(ASTTrue);
  //     for(;paramCurrentValue < paramLimit;) 
  //       {
  //         ASTNode currentFormula;
  //    ASTNode currentExceptFormula = exceptFormula;
  //    currentExceptFormula = 
  //      SimplifyFormula(exceptFormula, false, ParamToCurrentValMap);
  //    if(ASTTrue ==  currentExceptFormula)
  //      {         
  //        currentFormula = ASTTrue;
  //      }
  //    else 
  //      {
  //        currentFormula =
  //          SimplifyFormula(formulabody, false, ParamToCurrentValMap);
  //      }

  //         //Check the currentformula against the model, and add it to the
  //         //SAT solver if it is false against the model
  //         if(absrefine_flag 
  //       && 
  //       ASTFalse == ComputeFormulaUsingModel(currentFormula)
  //       ) 
  //      {
  //        ForloopVec.push_back(currentFormula);
  //           }
  //    else 
  //      {
  //        if(ASTTrue != currentFormula)
  //          {
  //            ForloopVec.push_back(currentFormula);
  //          }
  //        if(ASTFalse == currentFormula)
  //          {
  //            ForloopVec.push_back(ASTFalse);
  //            return ForloopVec;
  //          }
  //      }
        
  //         //Update ParamToCurrentValMap with parameter and its current
  //         //value.
  //    paramCurrentValue = paramCurrentValue + paramIncrement;
  //    value = bm->CreateTerm(BVPLUS, 
  //                       width, 
  //                       (*ParamToCurrentValMap)[parameter],
  //                       bm->CreateOneConst(width));  
  //    ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);
  //       } //end of expanding the FOR loop
    
  //     return ForloopVec;
  //   } //end of the SATBased_FiniteLoop_Refinement()

  //   //SATBased_FiniteLoop_Refinement_UsingModel().  Expand the finite
  //   //loop, check against model
  //   ASTNode 
  //   AbsRefine_CounterExample::
  //   Check_FiniteLoop_UsingModel(const ASTNode& finiteloop,
  //                                   ASTNodeMap* ParamToCurrentValMap,
  //                                   bool checkusingmodel_flag = true)
  //   {
  //     /*
  //      * 'finiteloop' is the finite loop to be expanded
  //      * Every finiteloop has three parts:    
  //      * 0) Parameter Name     
  //      * 1) Parameter initialization     
  //      * 2) Parameter limit value     
  //      * 3) Increment formula     
  //      * 4) Formula Body
  //      *    
  //      * ParamToCurrentValMap contains a map from parameters to their
  //      * current values in the recursion
  //      *   
  //      * Nested FORs are allowed, but only the innermost loop can have a
  //      * formula in it
  //      */

  //     //BVTypeCheck should have already checked the sanity of the input
  //     //FOR-formula
  //     ASTNode parameter     = finiteloop[0];
  //     int paramInit         = GetUnsignedConst(finiteloop[1]);
  //     int paramLimit        = GetUnsignedConst(finiteloop[2]);
  //     int paramIncrement    = GetUnsignedConst(finiteloop[3]);
  //     ASTNode exceptFormula = finiteloop[4];
  //     ASTNode formulabody   = finiteloop[5];
  //     int paramCurrentValue = paramInit;
  //     int width             = finiteloop[1].GetValueWidth();

  //     //Update ParamToCurrentValMap with parameter and its current
  //     //value. Here paramCurrentValue is the initial value
  //     ASTNode value =       
  //       bm->CreateBVConst(width,paramCurrentValue);
  //     ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);

  //     ASTNode ret = ASTTrue;
  //     ASTVec returnVec;
  //     //Go recursively thru' all the FOR-constructs.
  //     if(FOR == formulabody.GetKind()) 
  //       { 
  //         while(paramCurrentValue < paramLimit) 
  //           {
  //             ret = Check_FiniteLoop_UsingModel(formulabody,
  //                                          ParamToCurrentValMap, 
  //                                          checkusingmodel_flag);
  //        if(ASTFalse == ret) 
  //          {
  //            //no more expansion needed. Return immediately
  //            return ret;
  //          }
  //        else 
  //          {
  //            returnVec.push_back(ret);
  //          }

  //             //Update ParamToCurrentValMap with parameter and its
  //             //current value.
  //             paramCurrentValue = paramCurrentValue + paramIncrement;
  //        value = bm->CreateTerm(BVPLUS, 
  //                           width, 
  //                           (*ParamToCurrentValMap)[parameter],
  //                           bm->CreateOneConst(width));
  //        ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);
  //           } //end of While

  //    ASTNode retFormula = 
  //      (returnVec.size() > 1) ? 
  //      bm->CreateNode(AND, returnVec) : 
  //      (returnVec.size() == 1) ?
  //      returnVec[0] :
  //      ASTTrue;
  //         return retFormula;      
  //       }

  //     ASTVec forloopFormulaVector;
  //     //Expand the leaf level FOR-construct completely
  //     //incrementing of paramCurrentValue is done inside loop
  //     for(;paramCurrentValue < paramLimit;)
  //       {
  //    ASTNode currentFormula;

  //    ASTNode currentExceptFormula = exceptFormula;
  //    currentExceptFormula = 
  //      SimplifyFormula(exceptFormula, false, ParamToCurrentValMap);
  //    if(ASTTrue ==  currentExceptFormula)
  //      {
  //        currentFormula = ASTTrue;
  //        //continue;
  //      }
  //    else 
  //      {
  //        currentFormula = 
  //          SimplifyFormula(formulabody, false, ParamToCurrentValMap);
  //      }

  //         if(checkusingmodel_flag) 
  //           {
  //             //Check the currentformula against the model, and return
  //             //immediately
  //        //cout << "Printing current Formula: " << currentFormula << "\n"; 
  //        ASTNode computedForm = ComputeFormulaUsingModel(currentFormula);
  //        //cout << "Printing computed Formula: " << computedForm << "\n"; 
  //             if(ASTFalse == computedForm)
  //          {
  //            return ASTFalse;
  //          }
  //           }
  //         else 
  //           {
  //        if(ASTTrue != currentFormula)
  //          {
  //            forloopFormulaVector.push_back(currentFormula);
  //          }
  //           }
        
  //         //Update ParamToCurrentValMap with parameter and its current
  //         //value         
  //    paramCurrentValue = paramCurrentValue + paramIncrement;
  //    value = bm->CreateTerm(BVPLUS, 
  //                       width, 
  //                       (*ParamToCurrentValMap)[parameter],
  //                       bm->CreateOneConst(width));  
  //    ReplaceOrAddToMap(ParamToCurrentValMap, parameter, value);
  //       } //end of For

  //     if(checkusingmodel_flag) 
  //       {
  //    return ASTTrue;
  //       }
  //     else 
  //       {
  //         ASTNode retFormula = 
  //           (forloopFormulaVector.size() > 1) ? 
  //      bm->CreateNode(AND, forloopFormulaVector) :
  //      (forloopFormulaVector.size() == 1) ? 
  //      forloopFormulaVector[0] :
  //      ASTTrue;
  //         return retFormula;
  //       }
  //   } //end of the Check_FiniteLoop_UsingModel()
  

  //   //Expand_FiniteLoop_For_ModelCheck
  //   ASTNode 
  //   AbsRefine_CounterExample::
  //   Expand_FiniteLoop_TopLevel(const ASTNode& finiteloop) 
  //   {
  //     ASTNodeMap ParamToCurrentValMap;
  //     return Check_FiniteLoop_UsingModel(finiteloop, 
  //                                   &ParamToCurrentValMap, false);
  //   } //end of Expand_FiniteLoop_TopLevel()  

  //   ASTNode
  //   AbsRefine_CounterExample::
  //   Check_FiniteLoop_UsingModel(const ASTNode& finiteloop)
  //   {
  //     ASTNodeMap ParamToCurrentValMap;
  //     return Check_FiniteLoop_UsingModel(finiteloop, 
  //                                   &ParamToCurrentValMap, true);
  //   } //end of Check_FiniteLoop_UsingModel  
};// end of namespace BEEV

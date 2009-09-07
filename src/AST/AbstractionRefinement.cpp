/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "AST.h"
#include "ASTUtil.h"
#include "../simplifier/bvsolver.h"
#include <math.h>

namespace BEEV
{

  /******************************************************************
   * Abstraction Refinement related functions
   ******************************************************************/  
  
  /******************************************************************
   * ARRAY READ ABSTRACTION REFINEMENT
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
  SOLVER_RETURN_TYPE BeevMgr::SATBased_ArrayReadRefinement(MINISAT::Solver& SatSolver, 
                                                           const ASTNode& inputAlreadyInSAT, 
                                                           const ASTNode& original_input) {
    //printf("doing array read refinement\n");
    if (!arrayread_refinement_flag)
      FatalError("SATBased_ArrayReadRefinement: Control should not reach here");
    
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
    for (ASTNodeToVecMap::iterator iset = _arrayname_readindices.begin(), 
           iset_end = _arrayname_readindices.end(); iset != iset_end; iset++)
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
            //        FatalError("SATBased_ArrayReadRefinement: arrname is not a SYMBOL",ArrName);
            ASTNode arr_read1 = CreateTerm(READ, ArrName.GetValueWidth(), ArrName, the_index);
            //get the variable corresponding to the array_read1
            ASTNode arrsym1 = _arrayread_symbol[arr_read1];
            if (!(SYMBOL == arrsym1.GetKind() || BVCONST == arrsym1.GetKind()))
              FatalError("TopLevelSAT: refinementloop:"
                         "term arrsym1 corresponding to READ must be a var", arrsym1);

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
                  CreateSimplifiedEQ(the_index, compare_index) : CreateSimplifiedEQ(compare_index, the_index);

                ASTNode arr_read2 = CreateTerm(READ, ArrName.GetValueWidth(), ArrName, compare_index);
                //get the variable corresponding to the array_read2
                ASTNode arrsym2 = _arrayread_symbol[arr_read2];
                if (!(SYMBOL == arrsym2.GetKind() || BVCONST == arrsym2.GetKind()))
                  FatalError("TopLevelSAT: refinement loop:"
                             "term arrsym2 corresponding to READ must be a var", arrsym2);

                ASTNode eqOfReads = CreateSimplifiedEQ(arrsym1, arrsym2);
                //construct appropriate Leibnitz axiom
                ASTNode LeibnitzAxiom = CreateNode(IMPLIES, eqOfIndices, eqOfReads);
                if (ASTFalse == ComputeFormulaUsingModel(LeibnitzAxiom))
                  //FalseAxioms = CreateNode(AND,FalseAxioms,LeibnitzAxiom);
                  FalseAxiomsVec.push_back(LeibnitzAxiom);
                else
                  //RemainingAxioms = CreateNode(AND,RemainingAxioms,LeibnitzAxiom);
                  RemainingAxiomsVec.push_back(LeibnitzAxiom);
              }
            ASTNode FalseAxioms = 
              (FalseAxiomsVec.size() > 1) ? 
              CreateNode(AND, FalseAxiomsVec) : FalseAxiomsVec[0];
            ASTNodeStats("adding false readaxioms to SAT: ", FalseAxioms);
            //printf("spot 01\n");
            SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
            //if (FalseAxiomsVec.size() > 0)
            if (FalseAxiomsVec.size() > oldFalseAxiomsSize)
              {
                res2 = CallSAT_ResultCheck(SatSolver, FalseAxioms, original_input);
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
      CreateNode(AND, RemainingAxiomsVec) : RemainingAxiomsVec[0];
    ASTNodeStats("adding remaining readaxioms to SAT: ", RemainingAxioms);
    return CallSAT_ResultCheck(SatSolver, RemainingAxioms, original_input);
  } //end of SATBased_ArrayReadRefinement


  /******************************************************************
   * ARRAY WRITE ABSTRACTION REFINEMENT
   *
   * FIXME: Write Detailed Comment
   *****************************************************************/
  SOLVER_RETURN_TYPE BeevMgr::SATBased_ArrayWriteRefinement(MINISAT::Solver& SatSolver, 
                                                            const ASTNode& original_input)
  {
    ASTNode writeAxiom;
    ASTNodeMap::iterator it = ReadOverWrite_NewName_Map.begin();
    ASTNodeMap::iterator itend = ReadOverWrite_NewName_Map.end();
    unsigned int oldFalseAxiomsSize = 0;
    //int count = 0;
    //int num_write_axioms = ReadOverWrite_NewName_Map.size();

    ASTVec FalseAxioms, RemainingAxioms;
    FalseAxioms.push_back(ASTTrue);
    RemainingAxioms.push_back(ASTTrue);
    for (; it != itend; it++)
      {
        //Guided refinement starts here
        ComputeFormulaMap.clear();
        writeAxiom = Create_ArrayWriteAxioms(it->first, it->second);
        if (ASTFalse == ComputeFormulaUsingModel(writeAxiom))
          {
            writeAxiom = TransformFormula_TopLevel(writeAxiom);
            FalseAxioms.push_back(writeAxiom);
          }
        else
          {
            writeAxiom = TransformFormula_TopLevel(writeAxiom);
            RemainingAxioms.push_back(writeAxiom);
          }
      }

    writeAxiom = 
      (FalseAxioms.size() != 1) ? 
      CreateNode(AND, FalseAxioms) : FalseAxioms[0];
    ASTNodeStats("adding false writeaxiom to SAT: ", writeAxiom);
    SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
    if (FalseAxioms.size() > oldFalseAxiomsSize)
      {
        res2 = CallSAT_ResultCheck(SatSolver, writeAxiom, original_input);
        oldFalseAxiomsSize = FalseAxioms.size();
      }
    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    writeAxiom = 
      (RemainingAxioms.size() != 1) ? 
      CreateNode(AND, RemainingAxioms) : RemainingAxioms[0];
    ASTNodeStats("adding remaining writeaxiom to SAT: ", writeAxiom);
    res2 = CallSAT_ResultCheck(SatSolver, writeAxiom, original_input);
    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    return SOLVER_UNDECIDED;
  } //end of SATBased_ArrayWriteRefinement
  
  //Creates Array Write Axioms
  ASTNode BeevMgr::Create_ArrayWriteAxioms(const ASTNode& term, 
					   const ASTNode& newvar)
  {
    if (READ != term.GetKind() && WRITE != term[0].GetKind())
      {
        FatalError("Create_ArrayWriteAxioms: Input must be a READ over a WRITE", term);
      }

    ASTNode lhs = newvar;
    ASTNode rhs = term;
    ASTNode arraywrite_axiom = CreateSimplifiedEQ(lhs, rhs);
    return arraywrite_axiom;
  }//end of Create_ArrayWriteAxioms()


  /******************************************************************
   * FINITE FORLOOP ABSTRACTION REFINEMENT
   *
   * For each 'finiteloop' in the list 'GlobalList_Of_FiniteLoops'
   *
   * Expand_FiniteLoop(finiteloop);
   *
   * The 'Expand_FiniteLoop' function expands the 'finiteloop' in a
   * counterexample-guided refinement fashion
   *
   * Once all the finiteloops have been expanded, we need to go back
   * and recheck that every discarded constraint is true with the
   * final model. A flag 'done' is set to false if atleast one
   * constraint is false during model-check, and is set to true if all
   * constraints are true during model-check.
   *
   * if the 'done' flag is true, then we terminate this refinement
   * loop.  
   *****************************************************************/
  SOLVER_RETURN_TYPE BeevMgr::SATBased_AllFiniteLoops_Refinement(MINISAT::Solver& SatSolver, 
                                                                 const ASTNode& original_input)
  {
    for(ASTVec::iterator i = GlobalList_Of_FiniteLoops.begin(),iend=GlobalList_Of_FiniteLoops.end();
	i!=iend;i++)
      {
	ASTNodeMap ParamToCurrentValMap;
	SOLVER_RETURN_TYPE ret = SATBased_FiniteLoop_Refinement(SatSolver,
								original_input,
								*i,&ParamToCurrentValMap);
	if(SOLVER_UNDECIDED != ret)
	  {
	    return ret;
	  }
      }
    return SOLVER_UNDECIDED;
  } //end of SATBased_AllFiniteLoops_Refinement()
  
  
  /*****************************************************************
   * SATBased_FiniteLoop_Refinement
   *
   *
   * 'finiteloop' is the finite loop to be expanded
   * Every finiteloop has three parts:
   * 0) Parameter Name
   * 1) Parameter initialization
   * 2) Parameter limit value
   * 3) Increment formula
   * 4) Formula Body
   *
   * ParamToCurrentValMap contains a map from parameters to their
   * current values in the recursion
   *   
   * Nested FORs are allowed, but only the innermost loop can have a
   * formula in it
   *****************************************************************/
  //SATBased_FiniteLoop_Refinement
  //
  //Expand the finite loop, check against model, and add false
  //formulas to the SAT solver
  SOLVER_RETURN_TYPE BeevMgr::SATBased_FiniteLoop_Refinement(MINISAT::Solver& SatSolver, 
                                                             const ASTNode& original_input,                                               
                                                             const ASTNode& finiteloop,
                                                             ASTNodeMap* ParamToCurrentValMap)
  {     
    //BVTypeCheck should have already checked the sanity of the input
    //FOR-formula
    ASTNode parameter     = finiteloop[0];
    int paramInit         = GetUnsignedConst(finiteloop[1]);
    int paramLimit        = GetUnsignedConst(finiteloop[2]);
    int paramIncrement    = GetUnsignedConst(finiteloop[3]);
    ASTNode formulabody   = finiteloop[4];
    int paramCurrentValue = paramInit;

    //Update ParamToCurrentValMap with parameter and its current
    //value. Here paramCurrentValue is the initial value
    unsigned width = 32;
    (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
    
    //Go recursively thru' all the FOR-constructs.
    if(FOR == formulabody.GetKind()) 
      { 
        while(paramCurrentValue < paramLimit) 
          {
            SATBased_FiniteLoop_Refinement(SatSolver, original_input,
                                           formulabody, ParamToCurrentValMap);
            paramCurrentValue = paramCurrentValue + paramIncrement;

            //Update ParamToCurrentValMap with parameter and its current
            //value
            //
            //FIXME: Possible leak since I am not freeing the previous
            //'value' for the same 'key'       
            (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
          } //end of While
      } //end of recursion FORs

    ASTVec forloopFormulaVector;
    //Expand the leaf level FOR-construct completely
    for(; 
        paramCurrentValue < paramLimit; 
        paramCurrentValue = paramCurrentValue + paramIncrement) 
      {
        ASTNode currentFormula;
        currentFormula = SimplifyFormula(formulabody, ParamToCurrentValMap);
        
        //Check the currentformula against the model, and add it to the
        //SAT solver if it is false against the model
        if(ASTFalse == ComputeFormulaUsingModel(currentFormula)) 
          {
            forloopFormulaVector.push_back(currentFormula);
            ASTNode forloopFormulas = 
              (forloopFormulaVector.size() != 1) ?
              CreateNode(AND, forloopFormulaVector) : forloopFormulaVector[0];
            
            SOLVER_RETURN_TYPE result = 
              CallSAT_ResultCheck(SatSolver, forloopFormulas, original_input);
            if(result != SOLVER_UNDECIDED)           
              {
                return result;
              }
          }
        
        //Update ParamToCurrentValMap with parameter and its current
        //value 
        //
        //FIXME: Possible leak since I am not freeing the previous
        //'value' for the same 'key'
        (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
      } //end of expanding the FOR loop
    
    return SOLVER_UNDECIDED;
  } //end of the SATBased_FiniteLoop_Refinement()

  //SATBased_FiniteLoop_Refinement_UsingModel  
  //
  //Expand the finite loop, check against model, and add false
  //formulas to the SAT solver
  ASTNode BeevMgr::Check_FiniteLoop_UsingModel(const ASTNode& finiteloop,
                                               ASTNodeMap* ParamToCurrentValMap,
                                               bool CheckUsingModel_Or_Expand = true)
  {
    /*
     * 'finiteloop' is the finite loop to be expanded
     * Every finiteloop has three parts:    
     * 0) Parameter Name     
     * 1) Parameter initialization     
     * 2) Parameter limit value     
     * 3) Increment formula     
     * 4) Formula Body
     *    
     * ParamToCurrentValMap contains a map from parameters to their
     * current values in the recursion
     *   
     * Nested FORs are allowed, but only the innermost loop can have a
     * formula in it
     */

    //BVTypeCheck should have already checked the sanity of the input
    //FOR-formula
    ASTNode parameter     = finiteloop[0];
    int paramInit         = GetUnsignedConst(finiteloop[1]);
    int paramLimit        = GetUnsignedConst(finiteloop[2]);
    int paramIncrement    = GetUnsignedConst(finiteloop[3]);
    ASTNode formulabody   = finiteloop[4];
    int paramCurrentValue = paramInit;

    //Update ParamToCurrentValMap with parameter and its current
    //value. Here paramCurrentValue is the initial value
    unsigned width = 32;
    (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
    
    //Go recursively thru' all the FOR-constructs.
    if(FOR == formulabody.GetKind()) 
      { 
        while(paramCurrentValue < paramLimit) 
          {
            Check_FiniteLoop_UsingModel(formulabody,
                                        ParamToCurrentValMap, CheckUsingModel_Or_Expand);
            paramCurrentValue = paramCurrentValue + paramIncrement;

            //Update ParamToCurrentValMap with parameter and its current
            //value
            //
            //FIXME: Possible leak since I am not freeing the previous
            //'value' for the same 'key'       
            (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
          } //end of While
      }

    ASTVec forloopFormulaVector;
    //Expand the leaf level FOR-construct completely
    for(; 
        paramCurrentValue < paramLimit; 
        paramCurrentValue = paramCurrentValue + paramIncrement) 
      {
        ASTNode currentFormula;
        currentFormula = SimplifyFormula(formulabody, ParamToCurrentValMap);
        
        if(CheckUsingModel_Or_Expand) 
          {
            //Check the currentformula against the model, and add it to the
            //SAT solver if it is false against the model
            if(ASTFalse == ComputeFormulaUsingModel(currentFormula)) 
              return ASTFalse;
          }
        else 
          {
            forloopFormulaVector.push_back(currentFormula);
          }
        
        //Update ParamToCurrentValMap with parameter and its current
        //value         
        //FIXME: Possible leak since I am not freeing the previous
        //'value' for the same 'key'
        (*ParamToCurrentValMap)[parameter] = CreateBVConst(32,paramCurrentValue);
      }


    if(CheckUsingModel_Or_Expand) 
      {
        ASTNode retFormula = 
          (forloopFormulaVector.size() != 1) ? CreateNode(AND, forloopFormulaVector) : forloopFormulaVector[0];
        return retFormula;
      }
    else 
      {
        return ASTTrue;
      }
  } //end of the Check_FiniteLoop_UsingModel()
  

  //Expand_FiniteLoop_For_ModelCheck
  ASTNode BeevMgr::Expand_FiniteLoop_TopLevel(const ASTNode& finiteloop) 
  {
    ASTNodeMap ParamToCurrentValMap;
    return Check_FiniteLoop_UsingModel(finiteloop, &ParamToCurrentValMap, false);
  } //end of Expand_FiniteLoop_TopLevel()  

};// end of namespace BEEV

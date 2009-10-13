// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef SIMPLIFIER_H
#define SIMPLIFIER_H

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
  class Simplifier
    {
      friend class counterexample;
    private:

      /****************************************************************
       * Private Data and TypeDefs                                    *
       ****************************************************************/

      // Handy defs
      ASTNode ASTTrue, ASTFalse, ASTUndefined;

      // Memo table for simplifcation. Key is unsimplified node, and
      // value is simplified node.
      ASTNodeMap * SimplifyMap;
      ASTNodeMap * SimplifyNegMap;
      ASTNodeMap * SolverMap;
      ASTNodeSet AlwaysTrueFormMap;
      ASTNodeMap MultInverseMap;

      // For ArrayWrite Abstraction: map from read-over-write term to
      // newname.
      ASTNodeMap * ReadOverWrite_NewName_Map;
      
      // For ArrayWrite Refinement: Map new arraynames to
      // Read-Over-Write terms
      ASTNodeMap NewName_ReadOverWrite_Map;

      
      // The number of direct parents of each node. i.e. the number
      // of times the pointer is in "children".  When we simplify we
      // want to be careful sometimes about using the context of a
      // node. For example, given ((x + 23) = 2), the obvious
      // simplification is to join the constants. However, if there
      // are lots of references to the plus node. Then each time we
      // simplify, we'll create an additional plus.
      // nextpoweroftwo064.smt is the motivating benchmark. The
      // splitting increased the number of pluses from 1 to 65.
      ASTNodeCountMap *ReferenceCount;
      
      //Ptr to STP Manager
      STPMgr * _bm;

    public:
      
      /****************************************************************
       * Public Member Functions                                      *
       ****************************************************************/      
      Simplifier(STPMgr * bm) : _bm(bm) 
      {
	SimplifyMap    = new ASTNodeMap(INITIAL_TABLE_SIZE);
	SimplifyNegMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
	SolverMap      = new ASTNodeMap(INITIAL_TABLE_SIZE);
	ReadOverWrite_NewName_Map = new ASTNodeMap(INITIAL_TABLE_SIZE);
	ReferenceCount = new ASTNodeCountMap(INITIAL_TABLE_SIZE);

	ASTTrue  = bm->CreateNode(TRUE);
	ASTFalse = bm->CreateNode(FALSE);
	ASTUndefined = bm->CreateNode(UNDEFINED);
      }
      
      ~Simplifier()
      {
	delete SimplifyMap;
	delete SimplifyNegMap;
	delete ReferenceCount;
      }

      /****************************************************************
       * Functions to check and update various Maps                   *
       ****************************************************************/      
      
      //Check the map passed to SimplifyTerm
      bool CheckMap(ASTNodeMap* VarConstMap, 
		    const ASTNode& key, ASTNode& output);

      //substitution
      bool CheckSubstitutionMap(const ASTNode& a, ASTNode& output);
      bool CheckSubstitutionMap(const ASTNode& a);
      bool UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1);
      
      //functions for checking and updating simplifcation map
      bool CheckSimplifyMap(const ASTNode& key, 
			    ASTNode& output, 
			    bool pushNeg, ASTNodeMap* VarConstMap=NULL);
      void UpdateSimplifyMap(const ASTNode& key, 
			     const ASTNode& value, 
			     bool pushNeg, ASTNodeMap* VarConstMap=NULL);
      bool CheckAlwaysTrueFormMap(const ASTNode& key);
      void UpdateAlwaysTrueFormMap(const ASTNode& val);
      bool CheckMultInverseMap(const ASTNode& key, ASTNode& output);
      void UpdateMultInverseMap(const ASTNode& key, const ASTNode& value);
      
      //Map for solved variables
      bool CheckSolverMap(const ASTNode& a, ASTNode& output);
      bool CheckSolverMap(const ASTNode& a);
      bool UpdateSolverMap(const ASTNode& e0, const ASTNode& e1);     

      void ResetSimplifyMaps(void);

      /****************************************************************
       * Simplification functions                                     *
       ****************************************************************/      

      ASTNode SimplifyFormula_TopLevel(const ASTNode& a, 
				       bool pushNeg,
				       ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyTerm_TopLevel(const ASTNode& b);


      ASTNode SimplifyFormula(const ASTNode& a, 
			      bool pushNeg, 
			      ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyTerm(const ASTNode& inputterm, 
			   ASTNodeMap* VarConstMap=NULL);
      

      ASTNode SimplifyFormula_NoRemoveWrites(const ASTNode& a, 
					     bool pushNeg, 
					     ASTNodeMap* VarConstMap=NULL);

      void CheckSimplifyInvariant(const ASTNode& a, 
				  const ASTNode& output);

      void BuildReferenceCountMap(const ASTNode& b);

      ASTNode SimplifyAtomicFormula(const ASTNode& a, 
				    bool pushNeg, 
				    ASTNodeMap* VarConstMap=NULL);

      ASTNode CreateSimplifiedEQ(const ASTNode& t1, 
				 const ASTNode& t2);

      ASTNode ITEOpt_InEqs(const ASTNode& in1, 
			   ASTNodeMap* VarConstMap=NULL);

      ASTNode PullUpITE(const ASTNode& in);

      ASTNode RemoveContradictionsFromAND(const ASTNode& in);
      
      ASTNode CreateSimplifiedTermITE(const ASTNode& t1, 
				      const ASTNode& t2, 
				      const ASTNode& t3);

      ASTNode CreateSimplifiedFormulaITE(const ASTNode& in0, 
					 const ASTNode& in1, 
					 const ASTNode& in2);

      ASTNode CreateSimplifiedINEQ(Kind k, 
				   const ASTNode& a0, 
				   const ASTNode& a1, bool pushNeg);

      ASTNode SimplifyNotFormula(const ASTNode& a, 
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyAndOrFormula(const ASTNode& a,
				   bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyXorFormula(const ASTNode& a,
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyNandFormula(const ASTNode& a,
				  bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyNorFormula(const ASTNode& a,
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyImpliesFormula(const ASTNode& a,
				     bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyIffFormula(const ASTNode& a,
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyIteFormula(const ASTNode& a,
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode SimplifyForFormula(const ASTNode& a,
				 bool pushNeg, ASTNodeMap* VarConstMap=NULL);

      ASTNode Flatten(const ASTNode& a);

      ASTNode FlattenOneLevel(const ASTNode& a);

      ASTNode FlattenAndOr(const ASTNode& a);

      ASTNode CombineLikeTerms(const ASTNode& a);

      ASTNode LhsMinusRhs(const ASTNode& eq);

      ASTNode DistributeMultOverPlus(const ASTNode& a,
				     bool startdistribution = false);

      ASTNode ConvertBVSXToITE(const ASTNode& a);

      //accepts constant term and simplifies it to a bvconst
      ASTNode BVConstEvaluator(const ASTNode& t);


      //checks if the input constant is odd or not
      bool BVConstIsOdd(const ASTNode& c);

      //computes the multiplicatve inverse of the input
      ASTNode MultiplicativeInverse(const ASTNode& c);

      //Replaces WRITE(Arr,i,val) with ITE(j=i, val, READ(Arr,j))
      ASTNode RemoveWrites_TopLevel(const ASTNode& term);
      ASTNode RemoveWrites(const ASTNode& term);
      ASTNode SimplifyWrites_InPlace(const ASTNode& term, 
				     ASTNodeMap* VarConstMap=NULL);
      ASTNode ReadOverWrite_To_ITE(const ASTNode& term, 
				   ASTNodeMap* VarConstMap=NULL);

      void printCacheStatus();

      //FIXME: Get rid of this horrible function
      const ASTNodeMap * ReadOverWriteMap()
      {
	return ReadOverWrite_NewName_Map;
      } // End of ReadOverWriteMap()
      
      const ASTNodeMap * Return_SolverMap()
      {
	return SolverMap;
      } // End of SolverMap()

      void ClearAllTables(void) 
      {
	SimplifyMap->clear();
	SimplifyNegMap->clear();
	SolverMap->clear();
	ReadOverWrite_NewName_Map->clear();
	NewName_ReadOverWrite_Map.clear();
	AlwaysTrueFormMap.clear();
	MultInverseMap.clear();
	ReferenceCount->clear();
      }
    };//end of class Simplifier
}; //end of namespace
#endif

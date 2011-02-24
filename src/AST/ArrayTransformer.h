// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TRANSFORM_H
#define TRANSFORM_H

#include "AST.h"
#include "../STPManager/STPManager.h"


namespace BEEV
{
  class Simplifier;

  class ArrayTransformer 
  {
  public:

      // These map from array and index to ITE and Symbol.
      struct ArrayRead
      {
        ArrayRead(ASTNode _ite, ASTNode _symbol)
        {
          assert(! _symbol.IsNull());
          assert ((SYMBOL == _symbol.GetKind() || BVCONST == _symbol.GetKind()));

          ite = _ite;
          symbol = _symbol;
        }

        ASTNode ite;  // if not using refinement this will be the ITE for the read. Otherwise == symbol.
        ASTNode symbol; // each read is allocated a distinct fresh variable.
      };

      // MAP: This maps from arrays to their indexes.
      // This map is used by the TransformArray()
      // function ,as well as the counter example, and refinement.
      // This map is useful in converting array reads into
      // nested ITE constructs. Suppose there are two array reads in the
      // input Read(A,i) and Read(A,j). Then Read(A,i) is replaced with
      // a symbolic constant, say v1, and Read(A,j) is replaced with the
      // following ITE: ITE(i=j,v1,v2)

      typedef map<ASTNode, map<ASTNode, ArrayRead> > ArrType ;
      ArrType arrayToIndexToRead;

  private:

    /****************************************************************
     * Private Typedefs and Data                                    *
     ****************************************************************/
    
    // Handy defs
    ASTNode ASTTrue, ASTFalse, ASTUndefined;
    
    // MAP: This is a map from Array Names to list of array-read
    // indices in the input. This map is used by the TransformArray()
    // function. This map is useful in converting array reads into
    // nested ITE constructs. Suppose there are two array reads in the
    // input Read(A,i) and Read(A,j). Then Read(A,i) is replaced with
    // a symbolic constant, say v1, and Read(A,j) is replaced with the
    // following ITE: ITE(i=j,v1,v2)
    //
    // CAUTION: I tried using a set instead of vector for read
    // indicies. for some odd reason the performance went down
    // considerably. this is totally inexplicable.
    ASTNodeToVecMap * Arrayname_ReadindicesMap;
    
    // MAP: This is a map from array-reads to symbolic constants. This
    // map is used by the TransformArray()     
    ASTNodeMap Arrayread_SymbolMap;
        
    // MAP: This is a map from Array Names to nested ITE constructs,
    // which are built as described below. This map is used by the
    // TransformArray() function. This map is useful in converting
    // array reads into nested ITE constructs. Suppose there are two
    // array reads in the input Read(A,i) and Read(A,j). Then
    // Read(A,i) is replaced with a symbolic constant, say v1, and
    // Read(A,j) is replaced with the following ITE: ITE(i=j,v1,v2)

    //ASTNodeMap * Arrayread_IteMap;

        
    // Memo table used by the transformer while it is transforming the
    // formulas and terms
    ASTNodeMap* TransformMap;
    
    // For finiteloop construct. A list of all finiteloop constructs
    // in the input formula
    //
    // ASTVec GlobalList_Of_FiniteLoops;

    // Flag for debuggin the transformer
    const bool debug_transform;

    // Ptr to an external simplifier
    Simplifier * simp;

    // Ptr to STPManager
    STPMgr * bm;
    
    // Ptr to class that records the runtimes for various parts of the
    // code
    RunTimes * runTimes;

    NodeFactory *nf;

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/
    
    ASTNode TranslateSignedDivModRem(const ASTNode& in);
    ASTNode TransformTerm(const ASTNode& inputterm);
    void assertTransformPostConditions(const ASTNode & term, ASTNodeSet& visited);
        
    /****************************************************************
     * Helper functions to for creating substitution map            *
     ****************************************************************/      
        

    ASTNode TransformArrayRead(const ASTNode& term);

    ASTNode TransformFormula(const ASTNode& form);

  public:

    //fill the arrayname_readindices vector if e0 is a READ(Arr,index)
    //and index is a BVCONST
    void FillUp_ArrReadIndex_Vec(const ASTNode& e0, const ASTNode& e1);


    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/      
    
    // Constructor
    ArrayTransformer(STPMgr * bm, Simplifier* s) : 
      Arrayread_SymbolMap(),
      bm(bm), 
      simp(s), 
      debug_transform(0),
      TransformMap(NULL)
    {
      //Arrayread_IteMap = new ASTNodeMap();
      Arrayname_ReadindicesMap = new ASTNodeToVecMap();
      nf = bm->defaultNodeFactory;

      runTimes = bm->GetRunTimes();
      ASTTrue  = bm->CreateNode(TRUE);
      ASTFalse = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    // Destructor
    ~ArrayTransformer()
    {
      //Arrayread_IteMap->clear();
      //delete Arrayread_IteMap;
      ASTNodeToVecMap::iterator it= Arrayname_ReadindicesMap->begin();
      ASTNodeToVecMap::iterator itend= Arrayname_ReadindicesMap->end();
      for(;it!=itend;it++)
        {
          ((*it).second).clear();
        }
      Arrayname_ReadindicesMap->clear();
      delete Arrayname_ReadindicesMap;
    }

    // Takes a formula, transforms it by replacing array reads with
    // variables, and returns the transformed formula
    ASTNode TransformFormula_TopLevel(const ASTNode& form);

    const ASTNodeToVecMap * ArrayName_ReadIndicesMap()
    {
      return Arrayname_ReadindicesMap;
    } //End of ArrayName_ReadIndicesMap

    const ASTNode ArrayRead_SymbolMap(const ASTNode& arrread) 
    {
      ASTNode symbol = Arrayread_SymbolMap[arrread];
      return symbol;
    } //End of ArrayRead_SymbolMap
    
    void ClearAllTables(void)
    {

      for (ASTNodeToVecMap::iterator
             iset = Arrayname_ReadindicesMap->begin(), 
             iset_end = Arrayname_ReadindicesMap->end(); 
           iset != iset_end; iset++)
        {
          iset->second.clear();
        }

      Arrayname_ReadindicesMap->clear();
      Arrayread_SymbolMap.clear();
      //Arrayread_IteMap->clear();
      arrayToIndexToRead.clear();
    }
  }; //end of class Transformer

};//end of namespace
#endif

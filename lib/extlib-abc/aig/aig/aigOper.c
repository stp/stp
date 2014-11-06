/**CFile****************************************************************

  FileName    [aigOper.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG operations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigOper.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

  Permission is hereby granted, without written agreement and without license or
  royalty fees, to use, copy, modify, and distribute this software and its
  documentation for any purpose, provided that the above copyright notice and
  the following two paragraphs appear in all copies of this software.

  IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
  DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF
  THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
  CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING,
  BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
  A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS" BASIS,
  AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE MAINTENANCE,
  SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

***********************************************************************/

#include "aig.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// procedure to detect an EXOR gate
static inline int Aig_ObjIsExorType( Aig_Obj_t * p0, Aig_Obj_t * p1, Aig_Obj_t ** ppFan0, Aig_Obj_t ** ppFan1 )
{
    if ( !Aig_IsComplement(p0) || !Aig_IsComplement(p1) )
        return 0;
    p0 = Aig_Regular(p0);
    p1 = Aig_Regular(p1);
    if ( !Aig_ObjIsAnd(p0) || !Aig_ObjIsAnd(p1) )
        return 0;
    if ( Aig_ObjFanin0(p0) != Aig_ObjFanin0(p1) || Aig_ObjFanin1(p0) != Aig_ObjFanin1(p1) )
        return 0;
    if ( Aig_ObjFaninC0(p0) == Aig_ObjFaninC0(p1) || Aig_ObjFaninC1(p0) == Aig_ObjFaninC1(p1) )
        return 0;
    *ppFan0 = Aig_ObjChild0(p0);
    *ppFan1 = Aig_ObjChild1(p0);
    return 1;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Returns i-th elementary variable.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_IthVar( Aig_Man_t * p, int i )
{
    int v;
    for ( v = Aig_ManPiNum(p); v <= i; v++ )
        Aig_ObjCreatePi( p );
    assert( i < Vec_PtrSize(p->vPis) );
    return Aig_ManPi( p, i );
}

/**Function*************************************************************

  Synopsis    [Perform one operation.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Oper( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1, Aig_Type_t Type )
{
    if ( Type == AIG_OBJ_AND )
        return Aig_And( p, p0, p1 );
    if ( Type == AIG_OBJ_EXOR )
        return Aig_Exor( p, p0, p1 );
    assert( 0 );
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Creates the canonical form of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_CanonPair_rec( Aig_Man_t * p, Aig_Obj_t * pGhost )
{
    Aig_Obj_t * pResult, * pLat0, * pLat1;
    int fCompl0, fCompl1;
    Aig_Type_t Type;
    assert( Aig_ObjIsNode(pGhost) );
    // consider the case when the pair is canonical
    if ( !Aig_ObjIsLatch(Aig_ObjFanin0(pGhost)) || !Aig_ObjIsLatch(Aig_ObjFanin1(pGhost)) )
    {
        if ( (pResult = Aig_TableLookup( p, pGhost )) )
            return pResult;
        return Aig_ObjCreate( p, pGhost );
    }
    /// remember the latches
    pLat0 = Aig_ObjFanin0(pGhost);
    pLat1 = Aig_ObjFanin1(pGhost);
    // remember type and compls
    Type = Aig_ObjType(pGhost);
    fCompl0 = Aig_ObjFaninC0(pGhost);
    fCompl1 = Aig_ObjFaninC1(pGhost);
    // call recursively
    pResult = Aig_Oper( p, Aig_NotCond(Aig_ObjChild0(pLat0), fCompl0), Aig_NotCond(Aig_ObjChild0(pLat1), fCompl1), Type );
    // build latch on top of this
    return Aig_Latch( p, pResult, (Type == AIG_OBJ_AND)? fCompl0 & fCompl1 : fCompl0 ^ fCompl1 );
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_And( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 )
{
    Aig_Obj_t * pGhost, * pResult;
//    Aig_Obj_t * pFan0, * pFan1;
    // check trivial cases
    if ( p0 == p1 )
        return p0;
    if ( p0 == Aig_Not(p1) )
        return Aig_Not(p->pConst1);
    if ( Aig_Regular(p0) == p->pConst1 )
        return p0 == p->pConst1 ? p1 : Aig_Not(p->pConst1);
    if ( Aig_Regular(p1) == p->pConst1 )
        return p1 == p->pConst1 ? p0 : Aig_Not(p->pConst1);
    // check not so trivial cases
    if ( p->fAddStrash && (Aig_ObjIsNode(Aig_Regular(p0)) || Aig_ObjIsNode(Aig_Regular(p1))) )
    { // http://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf
        Aig_Obj_t * pFanA, * pFanB, * pFanC, * pFanD;
        pFanA = Aig_ObjChild0(Aig_Regular(p0));
        pFanB = Aig_ObjChild1(Aig_Regular(p0));
        pFanC = Aig_ObjChild0(Aig_Regular(p1));
        pFanD = Aig_ObjChild1(Aig_Regular(p1));
        if ( Aig_IsComplement(p0) )
        {
            if ( pFanA == Aig_Not(p1) || pFanB == Aig_Not(p1) )
                return p1;
            if ( pFanB == p1 )
                return Aig_And( p, Aig_Not(pFanA), pFanB );
            if ( pFanA == p1 )
                return Aig_And( p, Aig_Not(pFanB), pFanA );
        }
        else
        {
            if ( pFanA == Aig_Not(p1) || pFanB == Aig_Not(p1) )
                return Aig_Not(p->pConst1);
            if ( pFanA == p1 || pFanB == p1 )
                return p0;
        }
        if ( Aig_IsComplement(p1) )
        {
            if ( pFanC == Aig_Not(p0) || pFanD == Aig_Not(p0) )
                return p0;
            if ( pFanD == p0 )
                return Aig_And( p, Aig_Not(pFanC), pFanD );
            if ( pFanC == p0 )
                return Aig_And( p, Aig_Not(pFanD), pFanC );
        }
        else
        {
            if ( pFanC == Aig_Not(p0) || pFanD == Aig_Not(p0) )
                return Aig_Not(p->pConst1);
            if ( pFanC == p0 || pFanD == p0 )
                return p1;
        }
        if ( !Aig_IsComplement(p0) && !Aig_IsComplement(p1) ) 
        {
            if ( pFanA == Aig_Not(pFanC) || pFanA == Aig_Not(pFanD) || pFanB == Aig_Not(pFanC) || pFanB == Aig_Not(pFanD) )
                return Aig_Not(p->pConst1);
            if ( pFanA == pFanC || pFanB == pFanC )
                return Aig_And( p, p0, pFanD );
            if ( pFanB == pFanC || pFanB == pFanD )
                return Aig_And( p, pFanA, p1 );
            if ( pFanA == pFanD || pFanB == pFanD )
                return Aig_And( p, p0, pFanC );
            if ( pFanA == pFanC || pFanA == pFanD )
                return Aig_And( p, pFanB, p1 );
        }
        else if ( Aig_IsComplement(p0) && !Aig_IsComplement(p1) )
        {
            if ( pFanA == Aig_Not(pFanC) || pFanA == Aig_Not(pFanD) || pFanB == Aig_Not(pFanC) || pFanB == Aig_Not(pFanD) )
                return p1;
            if ( pFanB == pFanC || pFanB == pFanD )
                return Aig_And( p, Aig_Not(pFanA), p1 );
            if ( pFanA == pFanC || pFanA == pFanD )
                return Aig_And( p, Aig_Not(pFanB), p1 );
        }
        else if ( !Aig_IsComplement(p0) && Aig_IsComplement(p1) )
        {
            if ( pFanC == Aig_Not(pFanA) || pFanC == Aig_Not(pFanB) || pFanD == Aig_Not(pFanA) || pFanD == Aig_Not(pFanB) )
                return p0;
            if ( pFanD == pFanA || pFanD == pFanB )
                return Aig_And( p, Aig_Not(pFanC), p0 );
            if ( pFanC == pFanA || pFanC == pFanB )
                return Aig_And( p, Aig_Not(pFanD), p0 );
        }
        else // if ( Aig_IsComplement(p0) && Aig_IsComplement(p1) )
        {
            if ( pFanA == pFanD && pFanB == Aig_Not(pFanC) )
                return Aig_Not(pFanA);
            if ( pFanB == pFanC && pFanA == Aig_Not(pFanD) )
                return Aig_Not(pFanB);
            if ( pFanA == pFanC && pFanB == Aig_Not(pFanD) )
                return Aig_Not(pFanA);
            if ( pFanB == pFanD && pFanA == Aig_Not(pFanC) )
                return Aig_Not(pFanB);
        }
    }
    // check if it can be an EXOR gate
//    if ( Aig_ObjIsExorType( p0, p1, &pFan0, &pFan1 ) )
//        return Aig_Exor( p, pFan0, pFan1 );
    pGhost = Aig_ObjCreateGhost( p, p0, p1, AIG_OBJ_AND );
    pResult = Aig_CanonPair_rec( p, pGhost );
    return pResult;
}

/**Function*************************************************************

  Synopsis    [Creates the canonical form of the node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Latch( Aig_Man_t * p, Aig_Obj_t * pObj, int fInitOne )
{
    Aig_Obj_t * pGhost, * pResult;
    pGhost = Aig_ObjCreateGhost( p, Aig_NotCond(pObj, fInitOne), NULL, AIG_OBJ_LATCH );
    pResult = Aig_TableLookup( p, pGhost );
    if ( pResult == NULL )
        pResult = Aig_ObjCreate( p, pGhost );
    return Aig_NotCond( pResult, fInitOne );
}

/**Function*************************************************************

  Synopsis    [Performs canonicization step.]

  Description [The argument nodes can be complemented.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Exor( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 )
{
/*
    Aig_Obj_t * pGhost, * pResult;
    // check trivial cases
    if ( p0 == p1 )
        return Aig_Not(p->pConst1);
    if ( p0 == Aig_Not(p1) )
        return p->pConst1;
    if ( Aig_Regular(p0) == p->pConst1 )
        return Aig_NotCond( p1, p0 == p->pConst1 );
    if ( Aig_Regular(p1) == p->pConst1 )
        return Aig_NotCond( p0, p1 == p->pConst1 );
    // check the table
    pGhost = Aig_ObjCreateGhost( p, p0, p1, AIG_OBJ_EXOR );
    if ( pResult = Aig_TableLookup( p, pGhost ) )
        return pResult;
    return Aig_ObjCreate( p, pGhost );
*/
    return Aig_Or( p, Aig_And(p, p0, Aig_Not(p1)), Aig_And(p, Aig_Not(p0), p1) );
}

/**Function*************************************************************

  Synopsis    [Implements Boolean OR.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Or( Aig_Man_t * p, Aig_Obj_t * p0, Aig_Obj_t * p1 )
{
    return Aig_Not( Aig_And( p, Aig_Not(p0), Aig_Not(p1) ) );
}

/**Function*************************************************************

  Synopsis    [Implements ITE operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Mux( Aig_Man_t * p, Aig_Obj_t * pC, Aig_Obj_t * p1, Aig_Obj_t * p0 )
{
/*    
    Aig_Obj_t * pTempA1, * pTempA2, * pTempB1, * pTempB2, * pTemp;
    int Count0, Count1;
    // consider trivial cases
    if ( p0 == Aig_Not(p1) )
        return Aig_Exor( p, pC, p0 );
    // other cases can be added
    // implement the first MUX (F = C * x1 + C' * x0)

    // check for constants here!!!

    pTempA1 = Aig_TableLookup( p, Aig_ObjCreateGhost(p, pC,          p1, AIG_OBJ_AND) );
    pTempA2 = Aig_TableLookup( p, Aig_ObjCreateGhost(p, Aig_Not(pC), p0, AIG_OBJ_AND) );
    if ( pTempA1 && pTempA2 )
    {
        pTemp = Aig_TableLookup( p, Aig_ObjCreateGhost(p, Aig_Not(pTempA1), Aig_Not(pTempA2), AIG_OBJ_AND) );
        if ( pTemp ) return Aig_Not(pTemp);
    }
    Count0 = (pTempA1 != NULL) + (pTempA2 != NULL);
    // implement the second MUX (F' = C * x1' + C' * x0')
    pTempB1 = Aig_TableLookup( p, Aig_ObjCreateGhost(p, pC,          Aig_Not(p1), AIG_OBJ_AND) );
    pTempB2 = Aig_TableLookup( p, Aig_ObjCreateGhost(p, Aig_Not(pC), Aig_Not(p0), AIG_OBJ_AND) );
    if ( pTempB1 && pTempB2 )
    {
        pTemp = Aig_TableLookup( p, Aig_ObjCreateGhost(p, Aig_Not(pTempB1), Aig_Not(pTempB2), AIG_OBJ_AND) );
        if ( pTemp ) return pTemp;
    }
    Count1 = (pTempB1 != NULL) + (pTempB2 != NULL);
    // compare and decide which one to implement
    if ( Count0 >= Count1 )
    {
        pTempA1 = pTempA1? pTempA1 : Aig_And(p, pC,          p1);
        pTempA2 = pTempA2? pTempA2 : Aig_And(p, Aig_Not(pC), p0);
        return Aig_Or( p, pTempA1, pTempA2 );
    }
    pTempB1 = pTempB1? pTempB1 : Aig_And(p, pC,          Aig_Not(p1));
    pTempB2 = pTempB2? pTempB2 : Aig_And(p, Aig_Not(pC), Aig_Not(p0));
    return Aig_Not( Aig_Or( p, pTempB1, pTempB2 ) );
*/
    return Aig_Or( p, Aig_And(p, pC, p1), Aig_And(p, Aig_Not(pC), p0) );
}

/**Function*************************************************************

  Synopsis    [Implements ITE operation.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Maj( Aig_Man_t * p, Aig_Obj_t * pA, Aig_Obj_t * pB, Aig_Obj_t * pC )
{
    return Aig_Or( p, Aig_Or(p, Aig_And(p, pA, pB), Aig_And(p, pA, pC)), Aig_And(p, pB, pC) );
}

/**Function*************************************************************

  Synopsis    [Constructs the well-balanced tree of gates.]

  Description [Disregards levels and possible logic sharing.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Multi_rec( Aig_Man_t * p, Aig_Obj_t ** ppObjs, int nObjs, Aig_Type_t Type )
{
    Aig_Obj_t * pObj1, * pObj2;
    if ( nObjs == 1 )
        return ppObjs[0];
    pObj1 = Aig_Multi_rec( p, ppObjs,           nObjs/2,         Type );
    pObj2 = Aig_Multi_rec( p, ppObjs + nObjs/2, nObjs - nObjs/2, Type );
    return Aig_Oper( p, pObj1, pObj2, Type );
}

/**Function*************************************************************

  Synopsis    [Old code.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Multi( Aig_Man_t * p, Aig_Obj_t ** pArgs, int nArgs, Aig_Type_t Type )
{
    assert( Type == AIG_OBJ_AND || Type == AIG_OBJ_EXOR );
    assert( nArgs > 0 );
    return Aig_Multi_rec( p, pArgs, nArgs, Type );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_Miter( Aig_Man_t * p, Vec_Ptr_t * vPairs )
{
    int i;
    assert( vPairs->nSize > 0 );
    assert( vPairs->nSize % 2 == 0 );
    for ( i = 0; i < vPairs->nSize; i += 2 )
        vPairs->pArray[i/2] = Aig_Not( Aig_Exor( p, vPairs->pArray[i], vPairs->pArray[i+1] ) );
    vPairs->nSize = vPairs->nSize/2;
    return Aig_Not( Aig_Multi_rec( p, (Aig_Obj_t **)vPairs->pArray, vPairs->nSize, AIG_OBJ_AND ) );
}

/**Function*************************************************************

  Synopsis    [Implements the miter.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_MiterTwo( Aig_Man_t * p, Vec_Ptr_t * vNodes1, Vec_Ptr_t * vNodes2 )
{
    int i;
    assert( vNodes1->nSize > 0 && vNodes1->nSize > 0 );
    assert( vNodes1->nSize == vNodes2->nSize );
    for ( i = 0; i < vNodes1->nSize; i++ )
        vNodes1->pArray[i] = Aig_Not( Aig_Exor( p, vNodes1->pArray[i], vNodes2->pArray[i] ) );
    return Aig_Not( Aig_Multi_rec( p, (Aig_Obj_t **)vNodes1->pArray, vNodes1->nSize, AIG_OBJ_AND ) );
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_CreateAnd( Aig_Man_t * p, int nVars )
{
    Aig_Obj_t * pFunc;
    int i;
    pFunc = Aig_ManConst1( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Aig_And( p, pFunc, Aig_IthVar(p, i) );
    return pFunc;
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_CreateOr( Aig_Man_t * p, int nVars )
{
    Aig_Obj_t * pFunc;
    int i;
    pFunc = Aig_ManConst0( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Aig_Or( p, pFunc, Aig_IthVar(p, i) );
    return pFunc;
}

/**Function*************************************************************

  Synopsis    [Creates AND function with nVars inputs.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_CreateExor( Aig_Man_t * p, int nVars )
{
    Aig_Obj_t * pFunc;
    int i;
    pFunc = Aig_ManConst0( p );
    for ( i = 0; i < nVars; i++ )
        pFunc = Aig_Exor( p, pFunc, Aig_IthVar(p, i) );
    return pFunc;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



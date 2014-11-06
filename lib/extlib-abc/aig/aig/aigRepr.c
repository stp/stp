/**CFile****************************************************************

  FileName    [aigRepr.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Handing node representatives.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigRepr.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

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

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Starts the array of representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManReprStart( Aig_Man_t * p, int nIdMax )
{
    assert( Aig_ManBufNum(p) == 0 );
    assert( p->pReprs == NULL );
    p->nReprsAlloc = nIdMax;
    p->pReprs = ALLOC( Aig_Obj_t *, p->nReprsAlloc );
    memset( p->pReprs, 0, sizeof(Aig_Obj_t *) * p->nReprsAlloc );
}

/**Function*************************************************************

  Synopsis    [Stop the array of representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManReprStop( Aig_Man_t * p )
{
    assert( p->pReprs != NULL );
    FREE( p->pReprs );
    p->nReprsAlloc = 0;    
}

/**Function*************************************************************

  Synopsis    [Set the representative.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ObjCreateRepr( Aig_Man_t * p, Aig_Obj_t * pNode1, Aig_Obj_t * pNode2 )
{
    assert( p->pReprs != NULL );
    assert( !Aig_IsComplement(pNode1) );
    assert( !Aig_IsComplement(pNode2) );
    assert( pNode1->Id < p->nReprsAlloc );
    assert( pNode2->Id < p->nReprsAlloc );
    assert( pNode1->Id < pNode2->Id );
    p->pReprs[pNode2->Id] = pNode1;
}

/**Function*************************************************************

  Synopsis    [Set the representative.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Aig_ObjSetRepr( Aig_Man_t * p, Aig_Obj_t * pNode1, Aig_Obj_t * pNode2 )
{
    assert( p->pReprs != NULL );
    assert( !Aig_IsComplement(pNode1) );
    assert( !Aig_IsComplement(pNode2) );
    assert( pNode1->Id < p->nReprsAlloc );
    assert( pNode2->Id < p->nReprsAlloc );
    if ( pNode1 == pNode2 )
        return;
    if ( pNode1->Id < pNode2->Id )
        p->pReprs[pNode2->Id] = pNode1;
    else
        p->pReprs[pNode1->Id] = pNode2;
}

/**Function*************************************************************

  Synopsis    [Find representative.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t * Aig_ObjFindRepr( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    assert( p->pReprs != NULL );
    assert( !Aig_IsComplement(pNode) );
    assert( pNode->Id < p->nReprsAlloc );
//    assert( !p->pReprs[pNode->Id] || p->pReprs[pNode->Id]->Id < pNode->Id );
    return p->pReprs[pNode->Id];
}

/**Function*************************************************************

  Synopsis    [Clears the representative.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline void Aig_ObjClearRepr( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    assert( p->pReprs != NULL );
    assert( !Aig_IsComplement(pNode) );
    assert( pNode->Id < p->nReprsAlloc );
    p->pReprs[pNode->Id] = NULL;
}

/**Function*************************************************************

  Synopsis    [Find representative transitively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t * Aig_ObjFindReprTransitive( Aig_Man_t * p, Aig_Obj_t * pNode )
{
    Aig_Obj_t * pNext, * pRepr;
    if ( (pRepr = Aig_ObjFindRepr(p, pNode)) )
        while ( (pNext = Aig_ObjFindRepr(p, pRepr)) )
            pRepr = pNext;
    return pRepr;
}

/**Function*************************************************************

  Synopsis    [Returns representatives of fanin in approapriate polarity.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline Aig_Obj_t * Aig_ObjRepr( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr;
    if ( (pRepr = Aig_ObjFindRepr(p, pObj)) )
        return Aig_NotCond( pRepr->pData, pObj->fPhase ^ pRepr->fPhase );
    return pObj->pData;
}
static inline Aig_Obj_t * Aig_ObjChild0Repr( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_NotCond( Aig_ObjRepr(p, Aig_ObjFanin0(pObj)), Aig_ObjFaninC0(pObj) ); }
static inline Aig_Obj_t * Aig_ObjChild1Repr( Aig_Man_t * p, Aig_Obj_t * pObj ) { return Aig_NotCond( Aig_ObjRepr(p, Aig_ObjFanin1(pObj)), Aig_ObjFaninC1(pObj) ); }

/**Function*************************************************************

  Synopsis    [Duplicates AIG while substituting representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManTransferRepr( Aig_Man_t * pNew, Aig_Man_t * pOld )
{
    Aig_Obj_t * pObj, * pRepr;
    int k;
    assert( pNew->pReprs != NULL );
    // extend storage to fix pNew
    if ( pNew->nReprsAlloc < Aig_ManObjNumMax(pNew) )
    {
        int nReprsAllocNew = 2 * Aig_ManObjNumMax(pNew);
        pNew->pReprs = REALLOC( Aig_Obj_t *, pNew->pReprs, nReprsAllocNew );
        memset( pNew->pReprs + pNew->nReprsAlloc, 0, sizeof(Aig_Obj_t *) * (nReprsAllocNew-pNew->nReprsAlloc) );
        pNew->nReprsAlloc = nReprsAllocNew;
    }
    // go through the nodes which have representatives
    Aig_ManForEachObj( pOld, pObj, k )
        if ( (pRepr = Aig_ObjFindRepr(pOld, pObj)) )
            Aig_ObjSetRepr( pNew, Aig_Regular(pRepr->pData), Aig_Regular(pObj->pData) ); 
}

/**Function*************************************************************

  Synopsis    [Duplicates the AIG manager recursively.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_ManDupRepr_rec( Aig_Man_t * pNew, Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t * pRepr;
    if ( pObj->pData )
        return pObj->pData;
    if ( (pRepr = Aig_ObjFindRepr(p, pObj)) )
    {
        Aig_ManDupRepr_rec( pNew, p, pRepr );
        return pObj->pData = Aig_NotCond( pRepr->pData, pRepr->fPhase ^ pObj->fPhase );
    }
    Aig_ManDupRepr_rec( pNew, p, Aig_ObjFanin0(pObj) );
    Aig_ManDupRepr_rec( pNew, p, Aig_ObjFanin1(pObj) );
    return pObj->pData = Aig_And( pNew, Aig_ObjChild0Repr(p, pObj), Aig_ObjChild1Repr(p, pObj) );
}

/**Function*************************************************************

  Synopsis    [Duplicates AIG while substituting representatives.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManDupRepr( Aig_Man_t * p, int fOrdered )
{
    Aig_Man_t * pNew;
    Aig_Obj_t * pObj;
    int i;
    // start the HOP package
    pNew = Aig_ManStart( Aig_ManObjNumMax(p) );
    pNew->pName = Aig_UtilStrsav( p->pName );
    pNew->nRegs = p->nRegs;
    if ( p->vFlopNums )
        pNew->vFlopNums = Vec_IntDup( p->vFlopNums );
    // map the const and primary inputs
    Aig_ManCleanData( p );
    Aig_ManConst1(p)->pData = Aig_ManConst1(pNew);
    Aig_ManForEachPi( p, pObj, i )
        pObj->pData = Aig_ObjCreatePi(pNew);
    // map the internal nodes
    if ( fOrdered )
    {
        Aig_ManForEachNode( p, pObj, i )
            pObj->pData = Aig_And( pNew, Aig_ObjChild0Repr(p, pObj), Aig_ObjChild1Repr(p, pObj) );
    }
    else
    {
        Aig_ManForEachPo( p, pObj, i )
            Aig_ManDupRepr_rec( pNew, p, Aig_ObjFanin0(pObj) );
    }
    // transfer the POs
    Aig_ManForEachPo( p, pObj, i )
        Aig_ObjCreatePo( pNew, Aig_ObjChild0Repr(p, pObj) );
    // check the new manager
    if ( !Aig_ManCheck(pNew) )
        printf( "Aig_ManDupRepr: Check has failed.\n" );
    return pNew;
}

/**Function*************************************************************

  Synopsis    [Transfer representatives and return the number of critical fanouts.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManRemapRepr( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pRepr;
    int i, nFanouts = 0;
    Aig_ManForEachNode( p, pObj, i )
    {
        pRepr = Aig_ObjFindReprTransitive( p, pObj );
        if ( pRepr == NULL )
            continue;
        assert( pRepr->Id < pObj->Id );
        Aig_ObjSetRepr( p, pObj, pRepr );
        nFanouts += (pObj->nRefs > 0);
    }
    return nFanouts;
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ObjCheckTfi_rec( Aig_Man_t * p, Aig_Obj_t * pNode, Aig_Obj_t * pOld )
{
    // check the trivial cases
    if ( pNode == NULL )
        return 0;
//    if ( pNode->Id < pOld->Id ) // cannot use because of choices of pNode
//        return 0;
    if ( pNode == pOld )
        return 1;
    // skip the visited node
    if ( Aig_ObjIsTravIdCurrent( p, pNode ) )
        return 0;
    Aig_ObjSetTravIdCurrent( p, pNode );
    // check the children
    if ( Aig_ObjCheckTfi_rec( p, Aig_ObjFanin0(pNode), pOld ) )
        return 1;
    if ( Aig_ObjCheckTfi_rec( p, Aig_ObjFanin1(pNode), pOld ) )
        return 1;
    // check equivalent nodes
    return Aig_ObjCheckTfi_rec( p, p->pEquivs[pNode->Id], pOld );
}

/**Function*************************************************************

  Synopsis    [Returns 1 if pOld is in the TFI of pNew.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ObjCheckTfi( Aig_Man_t * p, Aig_Obj_t * pNew, Aig_Obj_t * pOld )
{
    assert( !Aig_IsComplement(pNew) );
    assert( !Aig_IsComplement(pOld) );
    Aig_ManIncrementTravId( p );
    return Aig_ObjCheckTfi_rec( p, pNew, pOld );
}

/**Function*************************************************************

  Synopsis    [Iteratively rehashes the AIG.]

  Description [The input AIG is assumed to have representatives assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Man_t * Aig_ManRehash( Aig_Man_t * p )
{
    Aig_Man_t * pTemp;
    int i, nFanouts;
    assert( p->pReprs != NULL );
    for ( i = 0; (nFanouts = Aig_ManRemapRepr( p )); i++ )
    {
//        printf( "Iter = %3d. Fanouts = %6d. Nodes = %7d.\n", i+1, nFanouts, Aig_ManNodeNum(p) );
        p = Aig_ManDupRepr( pTemp = p, 1 );
        Aig_ManReprStart( p, Aig_ManObjNumMax(p) );
        Aig_ManTransferRepr( p, pTemp );
        Aig_ManStop( pTemp );
    }
    return p;
}

/**Function*************************************************************

  Synopsis    [Marks the nodes that are Creates choices.]

  Description [The input AIG is assumed to have representatives assigned.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManMarkValidChoices( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pRepr;
    int i;
    assert( p->pReprs != NULL );
    // create equivalent nodes in the manager
    assert( p->pEquivs == NULL );
    p->pEquivs = ALLOC( Aig_Obj_t *, Aig_ManObjNumMax(p) );
    memset( p->pEquivs, 0, sizeof(Aig_Obj_t *) * Aig_ManObjNumMax(p) );
    // make the choice nodes
    Aig_ManForEachNode( p, pObj, i )
    {
        pRepr = Aig_ObjFindRepr( p, pObj );
        if ( pRepr == NULL )
            continue;
        assert( pObj->nRefs == 0 );
        // skip constant and PI classes
        if ( !Aig_ObjIsNode(pRepr) )
        {
            Aig_ObjClearRepr( p, pObj );
            continue;
        }
        // skip choices with combinatinal loops
        if ( Aig_ObjCheckTfi( p, pObj, pRepr ) )
        {
            Aig_ObjClearRepr( p, pObj );
            continue;
        }
//printf( "Node %d is represented by node %d.\n", pObj->Id, pRepr->Id );
        // add choice to the choice node
        p->pEquivs[pObj->Id] = p->pEquivs[pRepr->Id];
        p->pEquivs[pRepr->Id] = pObj;
    }
}


////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



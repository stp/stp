/**CFile****************************************************************
 
  FileName    [aigCheck.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [AIG checking procedures.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigCheck.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

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

  Synopsis    [Checks the consistency of the AIG manager.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_ManCheck( Aig_Man_t * p )
{
    Aig_Obj_t * pObj, * pObj2;
    int i;
    // check primary inputs
    Aig_ManForEachPi( p, pObj, i )
    {
        if ( Aig_ObjFanin0(pObj) || Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The PI node \"%p\" has fanins.\n", pObj );
            return 0;
        }
    }
    // check primary outputs
    Aig_ManForEachPo( p, pObj, i )
    {
        if ( !Aig_ObjFanin0(pObj) )
        {
            printf( "Aig_ManCheck: The PO node \"%p\" has NULL fanin.\n", pObj );
            return 0;
        }
        if ( Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The PO node \"%p\" has second fanin.\n", pObj );
            return 0;
        }
    }
    // check internal nodes
    Aig_ManForEachObj( p, pObj, i )
    {
        if ( !Aig_ObjIsNode(pObj) )
            continue;
        if ( !Aig_ObjFanin0(pObj) || !Aig_ObjFanin1(pObj) )
        {
            printf( "Aig_ManCheck: The AIG has internal node \"%p\" with a NULL fanin.\n", pObj );
            return 0;
        }
        if ( Aig_ObjFanin0(pObj)->Id >= Aig_ObjFanin1(pObj)->Id )
        {
            printf( "Aig_ManCheck: The AIG has node \"%p\" with a wrong ordering of fanins.\n", pObj );
            return 0;
        }
        pObj2 = Aig_TableLookup( p, pObj );
        if ( pObj2 != pObj )
        {
            printf( "Aig_ManCheck: Node \"%p\" is not in the structural hashing table.\n", pObj );
            return 0;
        }
    }
    // count the total number of nodes
    if ( Aig_ManObjNum(p) != 1 + Aig_ManPiNum(p) + Aig_ManPoNum(p) + 
        Aig_ManBufNum(p) + Aig_ManAndNum(p) + Aig_ManExorNum(p) + Aig_ManLatchNum(p) )
    {
        printf( "Aig_ManCheck: The number of created nodes is wrong.\n" );
        printf( "C1 = %d. Pi = %d. Po = %d. Buf = %d. And = %d. Xor = %d. Lat = %d. Total = %d.\n",
            1, Aig_ManPiNum(p), Aig_ManPoNum(p), Aig_ManBufNum(p), Aig_ManAndNum(p), Aig_ManExorNum(p), Aig_ManLatchNum(p), 
            1 + Aig_ManPiNum(p) + Aig_ManPoNum(p) + Aig_ManBufNum(p) + Aig_ManAndNum(p) + Aig_ManExorNum(p) + Aig_ManLatchNum(p) );
        printf( "Created = %d. Deleted = %d. Existing = %d.\n",
            p->nCreated, p->nDeleted, p->nCreated - p->nDeleted );
        return 0;
    }
    // count the number of nodes in the table
    if ( Aig_TableCountEntries(p) != Aig_ManAndNum(p) + Aig_ManExorNum(p) + Aig_ManLatchNum(p) )
    {
        printf( "Aig_ManCheck: The number of nodes in the structural hashing table is wrong.\n" );
        printf( "Entries = %d. And = %d. Xor = %d. Lat = %d. Total = %d.\n", 
            Aig_TableCountEntries(p), Aig_ManAndNum(p), Aig_ManExorNum(p), Aig_ManLatchNum(p),
            Aig_ManAndNum(p) + Aig_ManExorNum(p) + Aig_ManLatchNum(p) );

        return 0;
    }
//    if ( !Aig_ManIsAcyclic(p) )
//        return 0;
    return 1; 
}

/**Function*************************************************************

  Synopsis    [Checks if the markA is reset.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCheckMarkA( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachObj( p, pObj, i )
        assert( pObj->fMarkA == 0 );
}

/**Function*************************************************************

  Synopsis    [Checks the consistency of phase assignment.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_ManCheckPhase( Aig_Man_t * p )
{
    Aig_Obj_t * pObj;
    int i;
    Aig_ManForEachObj( p, pObj, i )
        if ( Aig_ObjIsPi(pObj) )
            assert( (int)pObj->fPhase == 0 );
        else
            assert( (int)pObj->fPhase == (Aig_ObjPhaseReal(Aig_ObjChild0(pObj)) & Aig_ObjPhaseReal(Aig_ObjChild1(pObj))) );
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////



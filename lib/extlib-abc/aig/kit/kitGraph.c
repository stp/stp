/**CFile****************************************************************

  FileName    [kitGraph.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Computation kit.]

  Synopsis    [Decomposition graph representation.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - Dec 6, 2006.]

  Revision    [$Id: kitGraph.c,v 1.00 2006/12/06 00:00:00 alanmi Exp $]

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

#include "kit.h"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Creates a graph with the given number of leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Graph_t * Kit_GraphCreate( int nLeaves )   
{
    Kit_Graph_t * pGraph;
    pGraph = ALLOC( Kit_Graph_t, 1 );
    memset( pGraph, 0, sizeof(Kit_Graph_t) );
    pGraph->nLeaves = nLeaves;
    pGraph->nSize = nLeaves;
    pGraph->nCap = 2 * nLeaves + 50;
    pGraph->pNodes = ALLOC( Kit_Node_t, pGraph->nCap );
    memset( pGraph->pNodes, 0, sizeof(Kit_Node_t) * pGraph->nSize );
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Creates constant 0 graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Graph_t * Kit_GraphCreateConst0()   
{
    Kit_Graph_t * pGraph;
    pGraph = ALLOC( Kit_Graph_t, 1 );
    memset( pGraph, 0, sizeof(Kit_Graph_t) );
    pGraph->fConst = 1;
    pGraph->eRoot.bits.fCompl = 1;
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Creates constant 1 graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Graph_t * Kit_GraphCreateConst1()   
{
    Kit_Graph_t * pGraph;
    pGraph = ALLOC( Kit_Graph_t, 1 );
    memset( pGraph, 0, sizeof(Kit_Graph_t) );
    pGraph->fConst = 1;
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Creates the literal graph.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Graph_t * Kit_GraphCreateLeaf( int iLeaf, int nLeaves, int fCompl )   
{
    Kit_Graph_t * pGraph;
    assert( 0 <= iLeaf && iLeaf < nLeaves );
    pGraph = Kit_GraphCreate( nLeaves );
    pGraph->eRoot.bits.Node   = iLeaf;
    pGraph->eRoot.bits.fCompl = fCompl;
    return pGraph;
}

/**Function*************************************************************

  Synopsis    [Creates a graph with the given number of leaves.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Kit_GraphFree( Kit_Graph_t * pGraph )   
{
    FREE( pGraph->pNodes );
    free( pGraph );
}

/**Function*************************************************************

  Synopsis    [Appends a new node to the graph.]

  Description [This procedure is meant for internal use.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Node_t * Kit_GraphAppendNode( Kit_Graph_t * pGraph )   
{
    Kit_Node_t * pNode;
    if ( pGraph->nSize == pGraph->nCap )
    {
        pGraph->pNodes = REALLOC( Kit_Node_t, pGraph->pNodes, 2 * pGraph->nCap ); 
        pGraph->nCap   = 2 * pGraph->nCap;
    }
    pNode = pGraph->pNodes + pGraph->nSize++;
    memset( pNode, 0, sizeof(Kit_Node_t) );
    return pNode;
}

/**Function*************************************************************

  Synopsis    [Creates an AND node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Edge_t Kit_GraphAddNodeAnd( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1 )
{
    Kit_Node_t * pNode;
    // get the new node
    pNode = Kit_GraphAppendNode( pGraph );
    // set the inputs and other info
    pNode->eEdge0 = eEdge0;
    pNode->eEdge1 = eEdge1;
    pNode->fCompl0 = eEdge0.bits.fCompl;
    pNode->fCompl1 = eEdge1.bits.fCompl;
    return Kit_EdgeCreate( pGraph->nSize - 1, 0 );
}

/**Function*************************************************************

  Synopsis    [Creates an OR node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Edge_t Kit_GraphAddNodeOr( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1 )
{
    Kit_Node_t * pNode;
    // get the new node
    pNode = Kit_GraphAppendNode( pGraph );
    // set the inputs and other info
    pNode->eEdge0 = eEdge0;
    pNode->eEdge1 = eEdge1;
    pNode->fCompl0 = eEdge0.bits.fCompl;
    pNode->fCompl1 = eEdge1.bits.fCompl;
    // make adjustments for the OR gate
    pNode->fNodeOr = 1;
    pNode->eEdge0.bits.fCompl = !pNode->eEdge0.bits.fCompl;
    pNode->eEdge1.bits.fCompl = !pNode->eEdge1.bits.fCompl;
    return Kit_EdgeCreate( pGraph->nSize - 1, 1 );
}

/**Function*************************************************************

  Synopsis    [Creates an XOR node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Edge_t Kit_GraphAddNodeXor( Kit_Graph_t * pGraph, Kit_Edge_t eEdge0, Kit_Edge_t eEdge1, int Type )
{
    Kit_Edge_t eNode0, eNode1, eNode;
    if ( Type == 0 )
    {
        // derive the first AND
        eEdge0.bits.fCompl ^= 1;
        eNode0 = Kit_GraphAddNodeAnd( pGraph, eEdge0, eEdge1 );
        eEdge0.bits.fCompl ^= 1;
        // derive the second AND
        eEdge1.bits.fCompl ^= 1;
        eNode1 = Kit_GraphAddNodeAnd( pGraph, eEdge0, eEdge1 );
        // derive the final OR
        eNode = Kit_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    }
    else
    {
        // derive the first AND
        eNode0 = Kit_GraphAddNodeAnd( pGraph, eEdge0, eEdge1 );
        // derive the second AND
        eEdge0.bits.fCompl ^= 1;
        eEdge1.bits.fCompl ^= 1;
        eNode1 = Kit_GraphAddNodeAnd( pGraph, eEdge0, eEdge1 );
        // derive the final OR
        eNode = Kit_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        eNode.bits.fCompl ^= 1;
    }
    return eNode;
}

/**Function*************************************************************

  Synopsis    [Creates an XOR node.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Kit_Edge_t Kit_GraphAddNodeMux( Kit_Graph_t * pGraph, Kit_Edge_t eEdgeC, Kit_Edge_t eEdgeT, Kit_Edge_t eEdgeE, int Type )
{
    Kit_Edge_t eNode0, eNode1, eNode;
    if ( Type == 0 )
    {
        // derive the first AND
        eNode0 = Kit_GraphAddNodeAnd( pGraph, eEdgeC, eEdgeT );
        // derive the second AND
        eEdgeC.bits.fCompl ^= 1;
        eNode1 = Kit_GraphAddNodeAnd( pGraph, eEdgeC, eEdgeE );
        // derive the final OR
        eNode = Kit_GraphAddNodeOr( pGraph, eNode0, eNode1 );
    }
    else
    {
        // complement the arguments
        eEdgeT.bits.fCompl ^= 1;
        eEdgeE.bits.fCompl ^= 1;
        // derive the first AND
        eNode0 = Kit_GraphAddNodeAnd( pGraph, eEdgeC, eEdgeT );
        // derive the second AND
        eEdgeC.bits.fCompl ^= 1;
        eNode1 = Kit_GraphAddNodeAnd( pGraph, eEdgeC, eEdgeE );
        // derive the final OR
        eNode = Kit_GraphAddNodeOr( pGraph, eNode0, eNode1 );
        eNode.bits.fCompl ^= 1;
    }
    return eNode;
}

/**Function*************************************************************

  Synopsis    [Derives the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
unsigned Kit_GraphToTruth( Kit_Graph_t * pGraph )
{
    unsigned uTruths[5] = { 0xAAAAAAAA, 0xCCCCCCCC, 0xF0F0F0F0, 0xFF00FF00, 0xFFFF0000 };
    unsigned uTruth = 0, uTruth0, uTruth1;
    Kit_Node_t * pNode;
    int i;

    // sanity checks
    assert( Kit_GraphLeaveNum(pGraph) >= 0 );
    assert( Kit_GraphLeaveNum(pGraph) <= pGraph->nSize );
    assert( Kit_GraphLeaveNum(pGraph) <= 5 );

    // check for constant function
    if ( Kit_GraphIsConst(pGraph) )
        return Kit_GraphIsComplement(pGraph)? 0 : ~((unsigned)0);
    // check for a literal
    if ( Kit_GraphIsVar(pGraph) )
        return Kit_GraphIsComplement(pGraph)? ~uTruths[Kit_GraphVarInt(pGraph)] : uTruths[Kit_GraphVarInt(pGraph)];

    // assign the elementary variables
    Kit_GraphForEachLeaf( pGraph, pNode, i )
        pNode->pFunc = (void *)(long)uTruths[i];

    // compute the function for each internal node
    Kit_GraphForEachNode( pGraph, pNode, i )
    {
        uTruth0 = (unsigned)(long)Kit_GraphNode(pGraph, pNode->eEdge0.bits.Node)->pFunc;
        uTruth1 = (unsigned)(long)Kit_GraphNode(pGraph, pNode->eEdge1.bits.Node)->pFunc;
        uTruth0 = pNode->eEdge0.bits.fCompl? ~uTruth0 : uTruth0;
        uTruth1 = pNode->eEdge1.bits.fCompl? ~uTruth1 : uTruth1;
        uTruth = uTruth0 & uTruth1;
        pNode->pFunc = (void *)(long)uTruth;
    }

    // complement the result if necessary
    return Kit_GraphIsComplement(pGraph)? ~uTruth : uTruth;
}

/**Function*************************************************************

  Synopsis    [Derives the factored form from the truth table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
#if 0
Kit_Graph_t * Kit_TruthToGraph( unsigned * pTruth, int nVars, Vec_Int_t * vMemory )
{
    Kit_Graph_t * pGraph;
    int RetValue;
    // derive SOP
    RetValue = Kit_TruthIsop( pTruth, nVars, vMemory, 1 ); // tried 1 and found not useful in "renode"
    if ( RetValue == -1 )
        return NULL;
    if ( Vec_IntSize(vMemory) > 128 )
        return NULL;
//    printf( "Isop size = %d.\n", Vec_IntSize(vMemory) );
    assert( RetValue == 0 || RetValue == 1 );
    // derive factored form
    pGraph = Kit_SopFactor( vMemory, RetValue, nVars, vMemory );
    return pGraph;
}
#endif

/**Function*************************************************************

  Synopsis    [Derives the maximum depth from the leaf to the root.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Kit_GraphLeafDepth_rec( Kit_Graph_t * pGraph, Kit_Node_t * pNode, Kit_Node_t * pLeaf )
{
    int Depth0, Depth1, Depth;
    if ( pNode == pLeaf )
        return 0;
    if ( Kit_GraphNodeIsVar(pGraph, pNode) )
        return -100;
    Depth0 = Kit_GraphLeafDepth_rec( pGraph, Kit_GraphNodeFanin0(pGraph, pNode), pLeaf );
    Depth1 = Kit_GraphLeafDepth_rec( pGraph, Kit_GraphNodeFanin1(pGraph, pNode), pLeaf );
    Depth = KIT_MAX( Depth0, Depth1 );
    Depth = (Depth == -100) ? -100 : Depth + 1;
    return Depth;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef TRANSFORM_H
#define TRANSFORM_H

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

namespace stp
{
class Simplifier;

class ArrayTransformer // not copyable
{
public:
  // These map from array and index to ITE and Symbol.
  struct ArrayRead
  {
    ArrayRead(ASTNode _ite, ASTNode _symbol)
    {
      assert(!_symbol.IsNull());
      assert(_ite.GetValueWidth() == _symbol.GetValueWidth());
      assert((SYMBOL == _symbol.GetKind() || BVCONST == _symbol.GetKind()));

      ite = _ite;
      symbol = _symbol;
    }

    ASTNode ite; // if not using refinement this will be the ITE for the read.
                 // Otherwise == symbol.
    ASTNode symbol;       // each read is allocated a distinct fresh variable.
    ASTNode index_symbol; // A symbol constrained to equal the index expression.
  };

  // MAP: This maps from arrays to their indexes.
  // This map is used by the TransformArray()
  // function ,as well as the counter example, and refinement.
  // This map is useful in converting array reads into
  // nested ITE constructs. Suppose there are two array reads in the
  // input Read(A,i) and Read(A,j). Then Read(A,i) is replaced with
  // a symbolic constant, say v1, and Read(A,j) is replaced with the
  // following ITE: ITE(i=j,v1,v2)

  typedef std::map<ASTNode, ArrayRead> arrTypeMap;
  typedef std::map<ASTNode, arrTypeMap> ArrType;
  typedef std::pair<ASTNode, ASTNode> ReadKey;
  typedef std::vector<ReadKey> ReadKeys;
  typedef std::map<ASTNode, ReadKeys> AckPairMap;

  // One level of an abstracted write chain: the transformed write index
  // and value, each paired with the anchor that carries its bits into the
  // SAT encoding (the term itself when already a symbol or constant).
  struct ChainLevel
  {
    ASTNode index, indexAnchor, value, valueAnchor;
  };

  // A read over a residual write chain, abstracted to `symbol` instead of
  // the expanded if-then-else chain. `levels` lists the chain top-down;
  // the fall-through is `baseReadSymbol`, the ordinary read abstraction of
  // (baseArray, index), whose registry row also anchors the read index.
  // Refinement pins `symbol` with path lemmas over the anchors.
  struct ChainRow
  {
    ASTNode symbol;
    ASTNode index;
    ASTNode indexAnchor;
    ASTNode baseArray;
    ASTNode baseReadSymbol;
    std::vector<ChainLevel> levels;
  };
  typedef std::map<ASTNode, ChainRow> ChainIndexMap; // read index -> row
  typedef std::map<ASTNode, ChainIndexMap> ChainReadsMap; // chain node ->

  // A caller-owned registry whose read abstractions must survive more than
  // one top-level transform. The batch driver continues to use the
  // transformer's own tables; the persistent driver lends one of these to a
  // single transform through TransformFormulaWithRegistry().
  struct Registry
  {
    ArrType reads;
    AckPairMap ackPairs;
    ChainReadsMap chains;
    ASTNodeMap chainAnchors;

    void clear()
    {
      reads.clear();
      ackPairs.clear();
      chains.clear();
      chainAnchors.clear();
    }

    void releaseStorage()
    {
      ArrType emptyReads;
      AckPairMap emptyAckPairs;
      ChainReadsMap emptyChains;
      ASTNodeMap emptyAnchors;
      reads.swap(emptyReads);
      ackPairs.swap(emptyAckPairs);
      chains.swap(emptyChains);
      chainAnchors.swap(emptyAnchors);
    }
  };

  struct TransformResult
  {
    TransformResult(const ASTNode& transformed, ReadKeys& touched,
                    ReadKeys& touchedChainKeys)
        : formula(transformed)
    {
      touchedReads.swap(touched);
      touchedChains.swap(touchedChainKeys);
    }

    ASTNode formula;
    ReadKeys touchedReads;
    ReadKeys touchedChains; // (chain node, read index) of rows visited
  };

  ArrType arrayToIndexToRead;
  ChainReadsMap chainReads;

private:
  // When enabled, every (array, index) read the current transform run
  // visits is appended here (registry hits and inserts alike), so a caller
  // can learn which registry rows one formula's reads occupy.
  bool recordTouchedReads = false;
  ReadKeys touchedReads;
  ReadKeys touchedChains;

  // Anchor variable per transformed chain term (identity for symbols and
  // constants), and the binding equations minted by the current transform,
  // conjoined onto the result at top level. Under a registry the anchor
  // map persists (swapped by RegistryScope); the equations are per-run.
  ASTNodeMap chainAnchorOf;
  ASTVec chainAnchorEquations;

  // Cut points chosen for this transformer's lifetime: reads of
  // (chain node, read index) pairs in here are abstracted. Deliberately
  // not part of the registry: rows themselves persist there, and a fresh
  // walk can pick a different (equally sound) cut for a new read.
  std::map<ASTNode, ASTNodeSet> lazyCutTargets;

  // How many qualified reads (deep enough for a cut) each base array has
  // seen, and each cut's residual may-alias depth: the abstraction
  // activates only once the reads outnumber a share of the depth, which
  // is when the eager levels-times-reads product beats the linear rows.
  std::map<ASTNode, size_t> qualifiedScansOf;
  std::map<ASTNode, size_t> cutDepthOf;

  bool markLazyChainCut(const ASTNode& writeNode, const ASTNode& readIndex);
  ASTNode anchorForChainTerm(const ASTNode& term);

  // Under eager Ackermannisation: each array's reads in the order they
  // were seen, from which a new read's nested if-then-else over the
  // existing reads is built. Persistent callers carry this inside Registry
  // so the two tables can only be installed and restored together.
  AckPairMap ack_pair;

  /****************************************************************
   * Private Typedefs and Data                                    *
   ****************************************************************/

  // Handy defs
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Memo table used by the transformer while it is transforming the
  // formulas and terms
  ASTNodeMap* TransformMap;


  // Ptr to an external simplifier
  Simplifier* simp;

  // Ptr to STPManager
  STPMgr* bm;

  // Ptr to class that records the runtimes for various parts of the
  // code
  RunTimes* runTimes;

  NodeFactory* nf;

  /****************************************************************
   * Private Member Functions                                     *
   ****************************************************************/

  ASTNode TransformTerm(const ASTNode& inputterm);
  ASTNode finishTransformTerm(const ASTNode& term, const ASTNode& result);
  void assertTransformPostConditions(const ASTNode& term, ASTNodeSet& visited);

  ASTNode TransformFormula(const ASTNode& form);

  // Transforming a formula transforms its terms, a term its condition and
  // its children, and a read the array under it -- once per level of the
  // input, which is the input's choice and can be deeper than the stack
  // holds. So the three are one walk with its frames on the heap rather
  // than three sets of call frames. See DeepDag_Test.cpp.
  class TransformDriver;
  class RegistryScope;
  ASTNode transform(bool asFormula, const ASTNode& n);

public:
  // fill the arrayname_readindices vector if e0 is a READ(Arr,index)
  // and index is a BVCONST
  void FillUp_ArrReadIndex_Vec(const ASTNode& e0, const ASTNode& e1);

  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

  ArrayTransformer(STPMgr* bm, Simplifier* s)
      : TransformMap(NULL), simp(s), bm(bm)
  {
    nf = bm->defaultNodeFactory;

    runTimes = bm->GetRunTimes();
    ASTTrue = bm->CreateNode(TRUE);
    ASTFalse = bm->CreateNode(FALSE);
    ASTUndefined = bm->CreateNode(UNDEFINED);
  }

  // Takes a formula, transforms it by replacing array reads with
  // variables, and returns the transformed formula
  ASTNode TransformFormula_TopLevel(const ASTNode& form);

  // Run one transform against a caller-owned persistent registry. The
  // transformer's batch tables are restored on every normal or exceptional
  // exit, while the result reports exactly the rows this formula touched.
  // Swapping keeps the transaction O(1) regardless of registry size.
  TransformResult TransformFormulaWithRegistry(const ASTNode& form,
                                               Registry& registry);

  void ClearAllTables(void)
  {
    arrayToIndexToRead.clear();
    ack_pair.clear();
    chainReads.clear();
    chainAnchorOf.clear();
    chainAnchorEquations.clear();
    lazyCutTargets.clear();
  }

  void ReleaseRunStorage()
  {
    recordTouchedReads = false;
    ReadKeys empty;
    touchedReads.swap(empty);
  }

  void printArrayStats()
  {
    std::cerr << "Array Sizes:";

    for (ArrType::const_iterator iset = arrayToIndexToRead.begin(),
                                 iset_end = arrayToIndexToRead.end();
         iset != iset_end; iset++)
    {
      std::cerr << iset->second.size() << " : ";
    }
    std::cerr << std::endl;

    size_t rows = 0, levels = 0;
    for (ChainReadsMap::const_iterator cit = chainReads.begin();
         cit != chainReads.end(); cit++)
      for (ChainIndexMap::const_iterator rit = cit->second.begin();
           rit != cit->second.end(); rit++)
      {
        rows++;
        levels += rit->second.levels.size();
      }
    if (rows > 0)
      std::cerr << "Abstracted chain reads:" << rows
                << " levels:" << levels << std::endl;
  }
};

} // end of namespace
#endif

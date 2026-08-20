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

  // A caller-owned registry whose read abstractions must survive more than
  // one top-level transform. The batch driver continues to use the
  // transformer's own tables; the persistent driver lends one of these to a
  // single transform through TransformFormulaWithRegistry().
  struct Registry
  {
    ArrType reads;
    AckPairMap ackPairs;

    void clear()
    {
      reads.clear();
      ackPairs.clear();
    }

    void releaseStorage()
    {
      ArrType emptyReads;
      AckPairMap emptyAckPairs;
      reads.swap(emptyReads);
      ackPairs.swap(emptyAckPairs);
    }
  };

  struct TransformResult
  {
    TransformResult(const ASTNode& transformed, ReadKeys& touched)
        : formula(transformed)
    {
      touchedReads.swap(touched);
    }

    ASTNode formula;
    ReadKeys touchedReads;
  };

  ArrType arrayToIndexToRead;

private:
  // When enabled, every (array, index) read the current transform run
  // visits is appended here (registry hits and inserts alike), so a caller
  // can learn which registry rows one formula's reads occupy.
  bool recordTouchedReads = false;
  ReadKeys touchedReads;

  // The sort constraints owed by the read abstractions this run minted, to
  // be conjoined onto the formula that minted them. Emptied at the start of
  // every top-level transform: a row the registry already held was pinned
  // onto the formula it was created for, exactly as its index anchor was,
  // and re-emitting it here would attach the whole table's pins to every
  // formula transformed afterwards. See TransformFormula_TopLevel.
  ASTVec cellSortConstraints;

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
  }
};

} // end of namespace
#endif

#ifndef CONSTANTBITPROPAGATION_H_
#define CONSTANTBITPROPAGATION_H_

#include <vector>
#include <list>
#include <map>
#include "FixedBits.h"
#include "../../AST/AST.h"
#include "NodeToFixedBitsMap.h"

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  class Simplifier;
}

class NodeFactory;

using std::vector;

namespace simplifier
{
  namespace constantBitP
  {

    class FixedBits;
    enum Direction
    {
      UPWARDS_ONLY, BOTH_WAYS
    };

    // This is used for very specific purposes.
    enum Type
    {
      BOOL_TYPE, VALUE_TYPE
    };

    // The only status that's correctly maintained at present is the conflict status.
    enum Result
    {
      NO_CHANGE = 1, CHANGED, CONFLICT, NOT_IMPLEMENTED
    };

    class NodeToFixedBitsMap;
    class MultiplicationStatsMap;
    class WorkList;
    class Dependencies;

    using BEEV::ASTNode;
    using BEEV::Simplifier;

    class ConstantBitPropagation
    {
      void
      printNodeWithFixings();
      NodeFactory *nf;

    public:

      NodeToFixedBitsMap* fixedMap;

#ifdef WITHCBITP
      MultiplicationStatsMap* multiplicationStats;
#endif

      WorkList *workList;
      Dependencies * dependents;
      Simplifier *simplifier;

      ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf)
      {
        simplifier = _sm;
        nf = _nf;
        fixedMap = NULL; // ASTNodes mapped to which of their bits are fixed.
        //multiplicationStats = NULL;
        dependents = NULL;
      }
      ;

      ~ConstantBitPropagation()
      {
        if (fixedMap != NULL)
          delete fixedMap;
      }
      ;

      // Returns the node after writing in simplifications from constant Bit propagation.
      BEEV::ASTNode
      topLevelBothWays(const BEEV::ASTNode& top);

      NodeToFixedBitsMap*
      getFixedMap(const ASTNode & top);
      MultiplicationStatsMap*
      getMultiplicationStats();

      void
      checkAtFixedPoint(const ASTNode& n, BEEV::ASTNodeSet & visited);

      void
      scheduleUp(const ASTNode& n);
      void
      scheduleDown(const ASTNode& n);
      void
      schedule(const ASTNode& n);

      void
      initialiseWorklist(const ASTNode& top);

      void
      prop();
    };

  }
}

#endif /* CONSTANTBITPROPAGATION_H_ */

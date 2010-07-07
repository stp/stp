#ifndef CONSTANTBITPROPAGATION_H_
#define CONSTANTBITPROPAGATION_H_

#include "FixedBits.h"
#include "Dependencies.h"
#include "NodeToFixedBitsMap.h"
#include "WorkList.h"

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  class Simplifier;
}

namespace simplifier
{
  namespace constantBitP
  {

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

    class MultiplicationStatsMap;
    class WorkList;

    using BEEV::ASTNode;
    using BEEV::Simplifier;

    class ConstantBitPropagation
    {
      NodeFactory *nf;

      Result status;
      WorkList *workList;
      Dependencies * dependents;
      Simplifier *simplifier;

#ifdef WITHCBITP
      MultiplicationStatsMap* msm;
#endif

      void
      printNodeWithFixings();

      FixedBits*
      getUpdatedFixedBits(const ASTNode& n);

      FixedBits*
      getCurrentFixedBits(const ASTNode& n);

      void
      scheduleDown(const ASTNode& n);

public:
      NodeToFixedBitsMap* fixedMap;

      bool isUnsatisfiable()
      {
        return status == CONFLICT;
      }

      // propagates.
      ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf, const ASTNode & top);

      /*
      ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf)
      {
        status = NO_CHANGE;

        workList = NULL;
        dependents = NULL;
        fixedMap = NULL; // ASTNodes mapped to which of their bits are fixed.
        msm = NULL;

        simplifier = _sm;
        nf = _nf;
      }
      ;
       */


      ~ConstantBitPropagation()
      {
          delete fixedMap;
          delete dependents;
          delete workList;
      }
      ;

      // Returns the node after writing in simplifications from constant Bit propagation.
      BEEV::ASTNode
      topLevelBothWays(const BEEV::ASTNode& top);



      bool
      checkAtFixedPoint(const ASTNode& n, BEEV::ASTNodeSet & visited);

      void
      propagate();

      void
      scheduleUp(const ASTNode& n);

      void
      scheduleNode(const ASTNode& n);

      void
      setNodeToTrue(const ASTNode& top);
    };
  }
}

#endif /* CONSTANTBITPROPAGATION_H_ */

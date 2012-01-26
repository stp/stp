#include "cpp_interface.h"

namespace BEEV
{
    // Does some simple caching of prior results.
    // Assumes that there is one node for each level!!!
    void
    Cpp_interface::checkSat(const ASTVec & assertionsSMT2)
    {
      bm.GetRunTimes()->stop(RunTimes::Parsing);

      assert(assertionsSMT2.size() == cache.size());

      Entry& cacheEntry = cache.back();

      if ((cacheEntry.result ==  SOLVER_SATISFIABLE || cacheEntry.result == SOLVER_UNSATISFIABLE)
          && (assertionsSMT2.back() == cacheEntry.node))
        { // If we already know the answer then return.
          if (bm.UserFlags.quick_statistics_flag)
            {
              bm.GetRunTimes()->print();
            }

          (GlobalSTP->tosat)->PrintOutput(cache.back().result);
          bm.GetRunTimes()->start(RunTimes::Parsing);
          return;
        }

      bm.ClearAllTables();
      GlobalSTP->ClearAllTables();

      ASTNode query;

      if (assertionsSMT2.size() >= 1)
        query = parserInterface->CreateNode(AND, assertionsSMT2);
      else if (assertionsSMT2.size() == 1)
        query = assertionsSMT2[0];
      else
        query = bm.ASTTrue;

      SOLVER_RETURN_TYPE last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);

      // Write in the answer to the current slot.
      if (last_result ==SOLVER_SATISFIABLE || last_result ==SOLVER_UNSATISFIABLE)
          {
            Entry e(last_result);
            e.node = assertionsSMT2.back();
            cacheEntry = e;
            assert (!cacheEntry.node.IsNull());
          }

      // It's satisfiable, so everything beneath it is satisfiable too.
      if (last_result ==SOLVER_SATISFIABLE)
        {
          for (int i=0; i < cache.size(); i++)
              {
              assert(cache[i].result != SOLVER_UNSATISFIABLE);
              cache[i].result = SOLVER_SATISFIABLE;
              }
        }

      if (bm.UserFlags.quick_statistics_flag)
        {
          bm.GetRunTimes()->print();
        }

      (GlobalSTP->tosat)->PrintOutput(last_result);
      //printStatus();
      bm.GetRunTimes()->start(RunTimes::Parsing);
    }
};

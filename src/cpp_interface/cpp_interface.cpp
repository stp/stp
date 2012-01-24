#include "cpp_interface.h"

namespace BEEV
{


// Does some simple caching of prior results.
    void
    Cpp_interface::checkSat(vector<ASTVec> & assertionsSMT2)
    {
      bm.GetRunTimes()->stop(RunTimes::Parsing);
      assert(assertionsSMT2.size() == cache.size());

      Entry& cacheEntry = cache.back();

      //cerr << "------------" << endl;
      //printStatus();

      if ((cacheEntry.result ==  SOLVER_SATISFIABLE || cacheEntry.result == SOLVER_UNSATISFIABLE)
          && (assertionsSMT2.back().size() ==1 && assertionsSMT2.back()[0] == cacheEntry.node))
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

      // Loop through the set of assertions converting them to single nodes..
      ASTVec v;
      for (int i = 0; i < assertionsSMT2.size(); i++)
        {
          if (assertionsSMT2[i].size() == 1)
            {}
          else if (assertionsSMT2[i].size() == 0)
            assertionsSMT2[i].push_back(bm.ASTTrue);
          else
            {
              ASTNode v = parserInterface->CreateNode(AND, assertionsSMT2[i]);
              assertionsSMT2[i].clear();
              assertionsSMT2[i].push_back(v);
            }
          assert(assertionsSMT2[i].size() ==1);
          v.push_back(assertionsSMT2[i][0]);
        }

      ASTNode query;

      if (v.size() > 1)
        query = parserInterface->CreateNode(AND, v);
      else if (v.size() > 0)
        query = v[0];
      else
        query = bm.ASTTrue;

      SOLVER_RETURN_TYPE last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);

      // Write in the answer to the current slot.
      if (last_result ==SOLVER_SATISFIABLE || last_result ==SOLVER_UNSATISFIABLE)
          {
            Entry e(last_result);
            e.node = assertionsSMT2.back()[0];
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

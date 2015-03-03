/*****************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

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

#include "PartFinder.h"

#include "Solver.h"
#include "Gaussian.h"
#include "GaussianConfig.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "VarReplacer.h"

#include <set>
#include <map>
#include <iomanip>
#include <math.h>
#include "FailedVarSearcher.h"
using std::set;
using std::map;

//#define VERBOSE_DEBUG

using std::cout;
using std::endl;

//#define PART_FINDING

namespace CMSat2
{
using namespace CMSat2;

PartFinder::PartFinder(Solver& _solver) : solver(_solver)
{
}

bool PartFinder::findParts()
{
  assert(solver.performReplace);

  double time = cpuTime();

  table.clear();
  table.resize(solver.nVars(), std::numeric_limits<uint32_t>::max());
  reverseTable.clear();
  part_no = 0;

  solver.clauseCleaner->removeAndCleanAll(true);
  if (!solver.ok)
    return false;
  while (solver.varReplacer->getNewToReplaceVars() > 0)
  {
    if (solver.performReplace && !solver.varReplacer->performReplace(true))
      return false;
    solver.clauseCleaner->removeAndCleanAll(true);
    if (!solver.ok)
      return false;
  }
  assert(solver.varReplacer->getClauses().size() == 0);

  addToPart(solver.clauses);
  addToPart(solver.binaryClauses);
  addToPart(solver.xorclauses);

  const unsigned parts = setParts();

#ifndef NDEBUG
  for (map<unsigned, vector<Var>>::const_iterator it = reverseTable.begin();
       it != reverseTable.end(); it++)
  {
    for (unsigned i2 = 0; i2 < it->second.size(); i2++)
    {
      assert(table[(it->second)[i2]] == it->first);
    }
  }
#endif

  if (solver.verbosity >= 2 || (solver.verbosity >= 1 && parts > 1))
  {
    std::cout << "c | Found parts: " << std::setw(10) << parts
              << " time: " << std::setprecision(2) << std::setw(4)
              << cpuTime() - time << " s" << std::setw(51) << " |" << std::endl;
  }

  return true;
}

template <class T> void PartFinder::addToPart(const vec<T*>& cs)
{
  set<unsigned> tomerge;
  vector<Var> newSet;
  for (T* const* c = cs.getData(), *const* end = c + cs.size(); c != end; c++)
  {
    if ((*c)->learnt())
      continue;
    tomerge.clear();
    newSet.clear();
    for (const Lit* l = (*c)->getData(), *end2 = l + (*c)->size(); l != end2;
         l++)
    {
      if (table[l->var()] != std::numeric_limits<uint32_t>::max())
        tomerge.insert(table[l->var()]);
      else
        newSet.push_back(l->var());
    }
    if (tomerge.size() == 1)
    {
      // no trees to merge, only merge the clause into one tree

      const unsigned into = *tomerge.begin();
      map<unsigned, vector<Var>>::iterator intoReverse = reverseTable.find(into);
      for (unsigned i = 0; i < newSet.size(); i++)
      {
        intoReverse->second.push_back(newSet[i]);
        table[newSet[i]] = into;
      }
      continue;
    }

    for (set<unsigned>::iterator it = tomerge.begin(); it != tomerge.end(); it++)
    {
      newSet.insert(newSet.end(), reverseTable[*it].begin(),
                    reverseTable[*it].end());
      reverseTable.erase(*it);
    }

    for (unsigned i = 0; i < newSet.size(); i++)
      table[newSet[i]] = part_no;
    reverseTable[part_no] = newSet;
    part_no++;
  }
}

unsigned PartFinder::setParts()
{
  vector<unsigned> numClauseInPart(part_no, 0);
  vector<unsigned> sumLitsInPart(part_no, 0);

  calcIn(solver.clauses, numClauseInPart, sumLitsInPart);
  calcIn(solver.binaryClauses, numClauseInPart, sumLitsInPart);
  calcIn(solver.xorclauses, numClauseInPart, sumLitsInPart);

  unsigned parts = 0;
  for (unsigned i = 0; i < numClauseInPart.size(); i++)
  {
    if (sumLitsInPart[i] == 0)
      continue;
    if (solver.verbosity >= 2 ||
        (solver.verbosity >= 1 && reverseTable.size() > 1))
    {
      std::cout << "c | Found part " << std::setw(8) << i
                << " vars: " << std::setw(10) << reverseTable[i].size()
                << " clauses:" << std::setw(10) << numClauseInPart[i]
                << " lits size:" << std::setw(10) << sumLitsInPart[i]
                << std::setw(12) << " | " << std::endl;
    }
    parts++;
  }

  if (parts > 1)
  {
#ifdef VERBOSE_DEBUG
    for (map<unsigned, vector<Var>>::iterator it = reverseTable.begin(),
                                          end = reverseTable.end();
         it != end; it++)
    {
      cout << "-- set begin --" << endl;
      for (vector<Var>::iterator it2 = it->second.begin(),
                                 end2 = it->second.end();
           it2 != end2; it2++)
      {
        cout << *it2 << ", ";
      }
      cout << "-------" << endl;
    }
#endif
  }

  return parts;
}

template <class T>
void PartFinder::calcIn(const vec<T*>& cs, vector<unsigned>& numClauseInPart,
                        vector<unsigned>& sumLitsInPart)
{
  for (T* const* c = cs.getData(), *const* end = c + cs.size(); c != end; c++)
  {
    if ((*c)->learnt())
      continue;
    T& x = **c;
    const unsigned part = table[x[0].var()];
    assert(part < part_no);

    // for stats
    numClauseInPart[part]++;
    sumLitsInPart[part] += x.size();
  }
}

} // NAMESPACE CMSat2

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

#ifndef CLAUSEALLOCATOR_H
#define CLAUSEALLOCATOR_H

#ifdef _MSC_VER
#include "msvc/stdint.h"
#else
#include <stdint.h>
#endif //_MSC_VER

#include "MemoryPool/MemoryPool.h"

#include "mtl/Vec.h"
#include "Clause.h"
#include <map>
#include <vector>
using std::map;
using std::vector;

namespace CMSat2
{
using namespace CMSat2;

class Clause;
class XorClause;
class Solver;

class ClauseAllocator
{
public:
  ClauseAllocator();
  ~ClauseAllocator();

  template <class T>
  Clause* Clause_new(const T& ps, uint32_t group, bool learnt = false);
  template <class T>
  XorClause* XorClause_new(const T& ps, bool inverted, uint32_t group);
  Clause* Clause_new(Clause& c);

  ClauseOffset getOffset(const Clause* ptr) const;

  inline Clause* getPointer(const uint32_t offset)
  {
    return (Clause*)(dataStarts[offset & 15] + (offset >> 4));
  }

  void clauseFree(Clause* c);

  void consolidate(Solver* solver);

private:
  uint32_t getOuterOffset(const Clause* c) const;
  uint32_t getInterOffset(const Clause* c, uint32_t outerOffset) const;
  ClauseOffset combineOuterInterOffsets(uint32_t outerOffset,
                                        uint32_t interOffset) const;

  template <class T>
  void updatePointers(vec<T*>& toUpdate,
                      const map<Clause*, Clause*>& oldToNewPointer);
  void updatePointers(vector<Clause*>& toUpdate,
                      const map<Clause*, Clause*>& oldToNewPointer);
  void updatePointers(vector<XorClause*>& toUpdate,
                      const map<Clause*, Clause*>& oldToNewPointer);

  template <class T>
  void updateOffsets(vec<vec<T>>& watches,
                     const map<ClauseOffset, ClauseOffset>& oldToNewOffset);
  template <class T>
  void updateOffsetsXor(vec<vec<T>>& watches,
                        const map<ClauseOffset, ClauseOffset>& oldToNewOffset);

  vec<uint32_t*> dataStarts;
  vec<size_t> sizes;
  vec<vec<uint32_t>> origClauseSizes;
  vec<size_t> maxSizes;
  vec<size_t> currentlyUsedSize;
  vec<uint32_t> origSizes;

  class BinClTmp
  {
    char dat[sizeof(Clause) + sizeof(Lit) * 2];
  };
  MemoryPool<BinClTmp> clausePoolBin;

  void* allocEnough(uint32_t size);
};

} // NAMESPACE CMSat2

#endif // CLAUSEALLOCATOR_H

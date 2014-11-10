// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 24/03/2010
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

#ifndef COLUMNSTATS_H_
#define COLUMNSTATS_H_

#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <assert.h>
#include <ostream>
using std::endl;

namespace simplifier
{
namespace constantBitP
{

extern const bool debug_multiply;

struct ColumnStats
{
  unsigned columnUnfixed;  // both unfixed.
  unsigned columnOneFixed; // one of the values is fixed to one, the other is
                           // unfixed.
  unsigned columnOnes;     // both are fixed to one.
  unsigned columnZeroes;   // one is fixed to zero.

  ColumnStats(const FixedBits& x, const FixedBits& y, const unsigned index)
  {
    columnUnfixed = 0;
    columnOneFixed = 0;
    columnOnes = 0;
    columnZeroes = 0;

    assert(index < x.getWidth());
    assert(y.getWidth() == x.getWidth());

    if (debug_multiply)
      log << "ColumnStats" << index << " " << x << " " << y << endl;

    for (unsigned i = 0; i <= index; i++)
    {
      bool xIsFixed = x.isFixed(index - i);
      bool yIsFixed;

      if (xIsFixed && !x.getValue(index - i))
        columnZeroes++;
      else if ((yIsFixed = y.isFixed(i)) && !y.getValue(i))
        columnZeroes++;
      else if (xIsFixed && x.getValue(index - i) && yIsFixed && y.getValue(i))
        columnOnes++;
      else if (yIsFixed && y.getValue(i))
        columnOneFixed++;
      else if (xIsFixed && x.getValue(index - i))
        columnOneFixed++;
      else
        columnUnfixed++;
    }

    assert(columnOnes + columnUnfixed + columnOneFixed + columnZeroes ==
           (index + 1));
  }
};

std::ostream& operator<<(std::ostream& o, const ColumnStats& cs)
{
  o << "cUnfixed:" << cs.columnUnfixed << endl; // both unfixed.
  o << "cOneFixed:" << cs.columnOneFixed
    << endl; // one of the values is fixed to one.
  o << "cOnes:" << cs.columnOnes << endl;
  o << "cZero:" << cs.columnZeroes << endl;
  return o;
}
}
}

#endif /* COLUMNSTATS_H_ */

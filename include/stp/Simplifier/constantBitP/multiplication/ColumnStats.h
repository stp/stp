// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 24/03/2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
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
      unsigned columnUnfixed; // both unfixed.
      unsigned columnOneFixed; // one of the values is fixed to one, the other is unfixed.
      unsigned columnOnes; // both are fixed to one.
      unsigned columnZeroes; // one is fixed to zero.

      ColumnStats(const FixedBits & x, const FixedBits & y, const unsigned index)
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

        assert(columnOnes + columnUnfixed + columnOneFixed + columnZeroes == (index + 1));
      }

    };

    std::ostream&
    operator<<(std::ostream& o, const ColumnStats& cs)
    {
      o << "cUnfixed:" << cs.columnUnfixed << endl; // both unfixed.
      o << "cOneFixed:" << cs.columnOneFixed << endl; // one of the values is fixed to one.
      o << "cOnes:" << cs.columnOnes << endl;
      o << "cZero:" << cs.columnZeroes << endl;
      return o;
    }
  }
}

#endif /* COLUMNSTATS_H_ */

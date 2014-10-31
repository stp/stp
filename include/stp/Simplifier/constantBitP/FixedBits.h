// -*- c++ -*-
/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef FIXEDBITS_H_
#define FIXEDBITS_H_

#include <vector>
#include <iostream>
#include <cassert>

class MTRand;

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  void FatalError(const char * str);
}

namespace simplifier
{
  namespace constantBitP
  {

    // Gives the file and line number as a string.
#define CONSTANTBITP_UTILITY_STR(s) #s
#define CONSTANTBITP_UTILITY_XSTR(s) CONSTANTBITP_UTILITY_STR(s)
#define LOCATION __FILE__ ":"  CONSTANTBITP_UTILITY_XSTR(__LINE__) ": "

    static int staticUniqueId = 1;

    // Bits can be fixed, or unfixed. Fixed bits are fixed to either zero or one.
    class FixedBits
    {
    private:
      bool* fixed;
      bool* values;
      unsigned width;
      bool representsBoolean;

      void
      init(const FixedBits& copy);
      int uniqueId;

      bool
      unsignedHolds_new(unsigned val);
      bool
      unsignedHolds_old(unsigned val);


    public:
      FixedBits(unsigned n, bool isBoolean);

      FixedBits(const FixedBits& copy)
      {
        assert(this != &copy);
        init(copy);
        uniqueId = staticUniqueId++;
      }

      bool
      isBoolean() const
      {
        return representsBoolean;
      }

      ~FixedBits()
      {
        delete[] fixed;
        delete[] values;
      }

      bool
      operator<=(const FixedBits& copy) const
      {
        return uniqueId <= copy.uniqueId;
      }

      char
      operator[] (const unsigned n) const
      {
        assert(n < width);
        if (!isFixed(n))
            return '*';
        else if (getValue(n))
            return '1';
        else
            return '0';
      }

      // Equality when I was a java programmer sorry!~.
      bool
      operator==(const FixedBits& other) const
      {
        return this == &(other);
      }

      FixedBits&
      operator=(const FixedBits& copy)
      {
        if (this == &copy)
          return *this;

        delete[] fixed;
        delete[] values;
        init(copy);
        return *this;
      }

      //All values are fixed to false.
      void
      fixToZero();

      unsigned
      getWidth() const
      {
        return width;
      }

      // the value contained in the fixed thingy.
      unsigned
      getUnsignedValue() const
      {
        assert(isTotallyFixed());
        assert(getWidth() <= 32);
        unsigned result = 0;

        for (unsigned i = 0; i < width; i++) {
          if (getValue(i))
            result += (1 << i);
        }

        return result;
      }

      // True if all bits are fixed (irrespective of what value they are fixed to).
      bool
      isTotallyFixed() const;

      // set value of bit "n" to the value.
      void
      setValue(unsigned n, bool value)
      {
        assert(((char)value) == 0 || (char)value ==1 );
        assert(n < width && fixed[n]);
        values[n] = value;
      }

      bool
      getValue(unsigned n) const
      {
        assert(n < width && fixed[n]);
        return values[n];
      }

      //returns -1 if it's zero.
      int
      topmostPossibleLeadingOne()
      {
        int i;
        for (i = (int)getWidth() - 1; i >= 0; i--)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      unsigned
      minimum_trailingOne()
      {
        unsigned i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      unsigned
      maximum_trailingOne()
      {
        unsigned i = 0;
        for (; i < getWidth(); i++)
          {
            if (isFixed(i) && getValue(i))
              break;
          }
        return i;
      }



      unsigned
      minimum_numberOfTrailingZeroes()
      {
        unsigned i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      unsigned
      maximum_numberOfTrailingZeroes()
      {
        unsigned i = 0;
        for (; i < getWidth(); i++)
          {
            if (isFixed(i) && getValue(i))
              break;
          }
        return i;
      }

      //Returns the position of the first non-fixed value.
      unsigned
      leastUnfixed() const
      {
        unsigned i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i))
              break;
          }
        return i;
      }

      int
      mostUnfixed() const
      {
        int i = (int)getWidth()-1;
        for (; i >=0; i--)
          {
            if (!isFixed(i))
              break;
          }
        return i;
      }

      // is this bit fixed to zero?
      bool
      isFixedToZero(int n) const
      {
        return isFixed(n) && !getValue(n);
      }

      // is this bit fixed to one?
      bool
      isFixedToOne(int n) const
      {
        return isFixed(n) && getValue(n);
      }

      // is this bit fixed to either zero or one?
      bool
      isFixed(unsigned n) const
      {
        assert(n <width);
        return fixed[n];
      }

      // set bit n to either fixed or unfixed.
      void
      setFixed(unsigned n, bool value)
      {
        assert(n <width);
        fixed[n] = value;
      }


      // Whether the set of values contains this one.
      bool
      unsignedHolds(unsigned val);

      void
      replaceWithContents(const FixedBits& a)
      {
        assert(getWidth() >= a.getWidth());

        for (unsigned i = 0; i < a.getWidth(); i++)
          {
            if (a.isFixed(i))
              {
                setFixed(i, true);
                setValue(i, a.getValue(i));
              }
            else
              {
                setFixed(i, false);
              }
          }
      }


      void
      copyIn(const FixedBits& a)
      {
        unsigned to = std::min(getWidth(), a.getWidth());
        for (unsigned i = 0; i < to; i++)
          {
            assert(!isFixed(i));
            if (a.isFixed(i))
              {
                setFixed(i, true);
                setValue(i, a.getValue(i));
              }
          }
      }

      //todo merger with unsignedHolds()
      bool
      containsZero() const
      {
        for (unsigned i = 0; i < getWidth(); i++) {
          if (isFixed(i) && getValue(i))
            return false;
        }

        return true;
      }

      unsigned
      countFixed() const
      {
        unsigned result = 0;
        for (unsigned i = 0; i < width; i++) {
          if (isFixed(i))
            result++;
        }

        return result;
      }

      // Result needs to be explicitly deleted.
      BEEV::CBV
      GetBVConst() const;

      // Result needs to be explicitly deleted.
      BEEV::CBV
      GetBVConst(unsigned to, unsigned from) const;

      void
      getUnsignedMinMax(unsigned &minShift, unsigned &maxShift) const;

      void
      mergeIn(const FixedBits& a)
      {
        assert(a.getWidth() == getWidth());
        for (unsigned i= 0; i < width;i++)
          {
          if (a.isFixed(i) && !isFixed(i))
            {
            setFixed(i,true);
            setValue(i,a.getValue(i));
            }
          }
      }


      static FixedBits
      meet(const FixedBits& a, const FixedBits& b);

      void
      join(const FixedBits& a);

      void
      join(unsigned int a);


      static FixedBits
      createRandom(const unsigned length, const unsigned probabilityOfSetting,
          MTRand& rand);

      void
      fromUnsigned(unsigned val);

      static FixedBits
      fromUnsignedInt(unsigned width, unsigned val);

      static FixedBits
      concreteToAbstract(const BEEV::ASTNode& n);

      static bool
      equals(const FixedBits& a, const FixedBits& b);

      static bool
      updateOK(const FixedBits& o, const FixedBits & n);

      static bool
      updateOK(const FixedBits& o, const FixedBits &n, const int upTo);

      static bool
      in(const FixedBits& a, const FixedBits& b);

    };

    std::ostream&
    operator<<(std::ostream& output, const FixedBits& h);

  }
}
#endif /*FIXED_H_*/

/****************************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef BITARRAY_H
#define BITARRAY_H

//#define DEBUG_BITARRAY

#include <string.h>
#include <assert.h>
#ifdef _MSC_VER
#include "msvc/stdint.h"
#else
#include <stdint.h>
#endif //_MSC_VER

namespace MINISAT
{
using namespace MINISAT;

class BitArray
{
public:
    BitArray() :
        size(0)
        , mp(NULL)
    {
    }

    BitArray(const BitArray& b) :
        size(b.size)
    {
        mp = new uint64_t[size];
        memcpy(mp, b.mp, sizeof(uint64_t)*size);
    }

    BitArray& operator=(const BitArray& b)
    {
        if (size != b.size) {
            delete[] mp;
            size = b.size;
            mp = new uint64_t[size];
        }
        memcpy(mp, b.mp, sizeof(uint64_t)*size);

        return *this;
    }

    BitArray& operator&=(const BitArray& b)
    {
        assert(size == b.size);
        uint64_t* t1 = mp;
        uint64_t* t2 = b.mp;
        for (uint64_t i = 0; i < size; i++) {
            *t1 &= *t2;
            t1++;
            t2++;
        }

        return *this;
    }

    bool nothingInCommon(const BitArray& b) const
    {
        assert(size == b.size);
        const uint64_t* t1 = mp;
        const uint64_t* t2 = b.mp;
        for (uint64_t i = 0; i < size; i++) {
            if ((*t1)&(*t2)) return false;
            t1++;
            t2++;
        }

        return true;
    }

    BitArray& removeThese(const BitArray& b)
    {
        assert(size == b.size);
        uint64_t* t1 = mp;
        uint64_t* t2 = b.mp;
        for (uint64_t i = 0; i < size; i++) {
            *t1 &= ~(*t2);
            t1++;
            t2++;
        }

        return *this;
    }

    template<class T>
    BitArray& removeThese(const T& rem)
    {
        for (uint32_t i = 0; i < rem.size(); i++) {
            clearBit(rem[i]);
        }

        return *this;
    }

    void resize(uint _size, const bool fill)
    {
        _size = _size/64 + (bool)(_size%64);
        if (size != _size) {
            delete[] mp;
            size = _size;
            mp = new uint64_t[size];
        }
        if (fill) setOne();
        else setZero();
    }

    ~BitArray()
    {
        delete[] mp;
    }

    inline bool isZero() const
    {
        const uint64_t*  mp2 = (const uint64_t*)mp;

        for (uint i = 0; i < size; i++) {
            if (mp2[i]) return false;
        }
        return true;
    }

    inline void setZero()
    {
        memset(mp, 0, size*sizeof(uint64_t));
    }

    inline void setOne()
    {
        memset(mp, 0, size*sizeof(uint64_t));
    }

    inline void clearBit(const uint i)
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        mp[i/64] &= ~((uint64_t)1 << (i%64));
    }

    inline void setBit(const uint i)
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        mp[i/64] |= ((uint64_t)1 << (i%64));
    }

    inline bool operator[](const uint& i) const
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        return (mp[i/64] >> (i%64)) & 1;
    }

    inline uint getSize() const
    {
        return size*64;
    }

private:

    uint size;
    uint64_t* mp;
};

}; //NAMESPACE MINISAT

#endif //BITARRAY_H


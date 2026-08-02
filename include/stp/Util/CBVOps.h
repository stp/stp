/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

// Moving values between CONSTANTBV bit-vectors and machine words.
//
// Several analyses run a fast 64-bit path beside the bit-vector one and
// need to cross between them. They each used to carry their own copy of
// these, under different names and -- worse -- with different methods:
// one read the vector's words through a raw pointer cast, which bakes in
// both the width of the storage word and its endianness. Everything here
// goes through the CONSTANTBV chunk interface instead, so the storage
// layout stays CONSTANTBV's business.
//
// The chunk interface is the reason for the doubled-up reads and writes
// below: a chunk carries at most an `unsigned long`, which isn't 64 bits
// everywhere (Windows and 32-bit targets), so 64 bits move in two halves
// of 32. Both chunk calls clamp: a chunk that runs past the vector's
// width is cut back to the width, and one that starts at or beyond the
// width does nothing and reads as zero. That clamping is what lets these
// be free of width guards, and it is also what makes the constructor
// below truncate rather than corrupt when handed too large a value.

#ifndef CBVOPS_H_
#define CBVOPS_H_

#include "extlib-constbv/constantbv.h"
#include <cstdint>

namespace stp
{

// Same spelling as the one in AST/UsefulDefs.h, so that this header can
// be used without dragging the AST in.
typedef unsigned int* CBV;

// The low `width` bits set, as a machine word. Saturates: a width of 64
// or more gives all ones, so callers needn't special-case the shift
// (shifting a 64-bit value by 64 is undefined).
inline uint64_t mask64(unsigned width)
{
  return width >= 64 ? ~0ull : (1ull << width) - 1;
}

// A fresh all-ones vector of the given width. The caller owns it.
inline CBV allOnes(unsigned width)
{
  CBV result = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Fill(result);
  return result;
}

// The 64 bits of x starting at any bit offset, as a machine word. Bits
// at or above the vector's width read as zero, so no guards are needed
// and any offset is allowed.
inline uint64_t chunkAt(const CBV x, unsigned offset)
{
  uint64_t r = CONSTANTBV::BitVector_Chunk_Read(x, 32, offset);
  r |= (uint64_t)CONSTANTBV::BitVector_Chunk_Read(x, 32, offset + 32) << 32;
  return r;
}

// Bits [64k, 64k+63] of x as a machine word.
inline uint64_t chunk64(const CBV x, unsigned k)
{
  return chunkAt(x, 64 * k);
}

// The inverse of chunk64. Bits of the value that fall above the vector's
// width are dropped.
inline void setChunk64(CBV x, unsigned k, uint64_t value)
{
  const unsigned offset = 64 * k;
  CONSTANTBV::BitVector_Chunk_Store(x, 32, offset, value);
  CONSTANTBV::BitVector_Chunk_Store(x, 32, offset + 32, value >> 32);
}

// The low (up to 64) bits of x as a machine word. A wider vector keeps
// only its bottom 64 bits.
inline uint64_t low64(const CBV x)
{
  return chunk64(x, 0);
}

// A fresh vector of the given width holding a machine word. The caller
// owns it. Truncating: bits of the value at or above the width are
// dropped, as are bits above 64 of a wider vector, which is left zero
// there.
inline CBV cbvFromU64(unsigned width, uint64_t value)
{
  CBV r = CONSTANTBV::BitVector_Create(width, true);
  setChunk64(r, 0, value);
  return r;
}

} // end namespace stp

#endif

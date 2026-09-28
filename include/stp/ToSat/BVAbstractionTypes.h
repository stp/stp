/********************************************************************
 * AUTHORS: Andrew Teylu
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

#ifndef BVABSTRACTIONTYPES_H
#define BVABSTRACTIONTYPES_H

#include <cstdint>

namespace stp
{

// Identity of one Boolean or bit-vector result introduced by BV abstraction.
//
// This is deliberately not a record-vector index. Records are copied from the
// bit-blaster into more than one consumer, and the incremental SAT backend can
// be rebuilt while the bit-blaster remains alive. The ID stays attached to the
// producer for the lifetime of that word-to-AIG encoding epoch. A memory-relief
// epoch rotation destroys every producer and every consumer together, after
// which numbering may start over safely.
class BVAbstractionId
{
  uint64_t value_;

public:
  BVAbstractionId() : value_(0) {}
  explicit BVAbstractionId(uint64_t value) : value_(value) {}

  bool valid() const { return value_ != 0; }
  uint64_t value() const { return value_; }

  bool operator==(const BVAbstractionId& other) const
  {
    return value_ == other.value_;
  }
  bool operator!=(const BVAbstractionId& other) const
  {
    return !(*this == other);
  }
  bool operator<(const BVAbstractionId& other) const
  {
    return value_ < other.value_;
  }
};

} // namespace stp

#endif

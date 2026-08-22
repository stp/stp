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

#include "stp/AST/SourceSort.h"

namespace stp
{

std::string sourceSortToSMTLib(const SourceSort& sort)
{
  switch (sort.kind())
  {
    case SourceSort::Kind::Bool:
      return "Bool";
    case SourceSort::Kind::BitVector:
      return "(_ BitVec " + std::to_string(sort.bitVectorWidth()) + ")";
    case SourceSort::Kind::FloatingPoint:
      return "(_ FloatingPoint " + std::to_string(sort.exponentWidth()) +
             " " + std::to_string(sort.significandWidth()) + ")";
    case SourceSort::Kind::RoundingMode:
      return "RoundingMode";
    case SourceSort::Kind::Array:
      return "(Array " + sourceSortToSMTLib(sort.index()) + " " +
             sourceSortToSMTLib(sort.element()) + ")";
    case SourceSort::Kind::Unknown:
      return "Unknown";
  }
  return "Unknown";
}

} // namespace stp

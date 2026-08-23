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
#include <mutex>
#include <vector>

namespace stp
{

namespace
{

// The declared-sort name table. Process-global, append-only, never recycled;
// see registerUninterpretedSort in the header for why each of those three is
// forced rather than chosen. Guarded by a mutex because a manager per thread
// is a supported use and declare-sort is a parse-time event, so contention is
// a handful of locks per query.
struct UninterpretedSortNames
{
  std::mutex guard;
  std::vector<std::string> byId; // index 0 unused: id 0 means "not a sort"
};

UninterpretedSortNames& sortNames()
{
  static UninterpretedSortNames names;
  return names;
}

} // namespace

namespace
{

// SMT-LIB 2's simple symbols: these characters, and not starting with a digit.
// Anything else has to be written between vertical bars.
bool needsQuoting(const std::string& name)
{
  static const std::string extra = "~!@$%^&*_-+=<>.?/";
  if (name.empty() || (name[0] >= '0' && name[0] <= '9'))
    return true;
  for (const char c : name)
  {
    const bool simple = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                        (c >= '0' && c <= '9') ||
                        extra.find(c) != std::string::npos;
    if (!simple)
      return true;
  }
  return false;
}

} // namespace

SourceSort registerUninterpretedSort(const std::string& name, unsigned width)
{
  UninterpretedSortNames& names = sortNames();
  std::lock_guard<std::mutex> held(names.guard);
  if (names.byId.empty())
    names.byId.push_back(std::string());
  names.byId.push_back(name);
  return SourceSort::uninterpreted((unsigned)(names.byId.size() - 1), width);
}

std::string uninterpretedSortName(unsigned id)
{
  UninterpretedSortNames& names = sortNames();
  std::lock_guard<std::mutex> held(names.guard);
  if (id == 0 || id >= names.byId.size())
    return std::string();
  return names.byId[id];
}

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
    case SourceSort::Kind::Uninterpreted:
    {
      // The name it was declared under. An id this process did not issue
      // cannot be spelled, and saying so is better than printing a carrier
      // width that the sort deliberately is not.
      const std::string name = uninterpretedSortName(sort.uninterpretedId());
      if (name.empty())
        return "Unknown";
      // A sort name is an SMT-LIB symbol and does not have to be a simple one:
      // (declare-sort |my sort| 0) is legal, and printing it bare produced a
      // model and diagnostics that could not be read back. Quoted here rather
      // than at each printer, because every printer reaches the name through
      // this function.
      return needsQuoting(name) ? "|" + name + "|" : name;
    }
    case SourceSort::Kind::Unknown:
      return "Unknown";
  }
  return "Unknown";
}

} // namespace stp

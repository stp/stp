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

#include "stp/UninterpretedFunctions/UFDecl.h"

namespace stp
{

const char* UFSignature::supportedSortsPhrase()
{
  return "only Bool, RoundingMode, FloatingPoint, nonzero-width bit-vector "
         "sorts and sorts introduced by declare-sort are supported";
}

bool UFSignature::isSupportedSort(const SourceSort& sort)
{
  // RoundingMode joins Bool and BitVec because its carrier's bit-equality is
  // its own equality: each of the five modes is exactly one 5-bit one-hot
  // pattern, so nothing in the checker or the lemma encoder has to learn a
  // second notion of "equal". What it does need is the pin -- see
  // UFLowering::lowerCompletedRoot -- because the carrier has thirty-two
  // patterns and the sort has five.
  //
  // FloatingPoint is admitted on the opposite basis: its carrier's
  // bit-equality is *not* its equality, so it is never solved at its own
  // sort. See loweringSort.
  //
  // A sort declared by declare-sort is in RoundingMode's camp, not
  // FloatingPoint's: equality is its only operation and bit equality on its
  // carrier is exactly that, so it too is solved at its own sort. It differs
  // from RoundingMode in the direction of the inequality between sort and
  // carrier -- RoundingMode has more carrier patterns than elements and is
  // pinned to the legal ones, while a declared sort is unbounded and has more
  // elements than any carrier -- which is why there is no pin to write here
  // and why the carrier's capacity is a separate problem.
  if (sort.kind() == SourceSort::Kind::Bool ||
      sort.kind() == SourceSort::Kind::RoundingMode ||
      sort.kind() == SourceSort::Kind::FloatingPoint ||
      sort.kind() == SourceSort::Kind::Uninterpreted)
    return true;
  return sort.kind() == SourceSort::Kind::BitVector &&
         sort.bitVectorWidth() > 0;
}

SourceSort UFSignature::loweringSort(const SourceSort& sort)
{
  // Only FloatingPoint is quotiented onto its carrier, and only because its
  // carrier's bit-equality is not its equality. Everything else is solved at
  // its own sort -- a declared sort included, deliberately: erasing it here
  // would put a sort-losing step in the middle of the pipeline, after which
  // the sort is re-derived from the value width as a bit-vector and the model
  // can no longer be printed at the sort the query asked about.
  if (sort.kind() == SourceSort::Kind::FloatingPoint)
    return SourceSort::bitVector(sort.packedWidth());
  return sort;
}

bool UFSignature::validate(const std::vector<SourceSort>& domain,
                           const SourceSort& codomain, std::string* error)
{
  if (domain.empty())
  {
    if (error != NULL)
      *error = "a zero-arity declaration is an ordinary symbol, not an "
               "uninterpreted function";
    return false;
  }

  for (size_t i = 0; i < domain.size(); ++i)
  {
    if (!isSupportedSort(domain[i]))
    {
      if (error != NULL)
        *error = "unsupported domain sort " +
                 sourceSortToSMTLib(domain[i]) + " at argument " +
                 std::to_string(i) + " (" + supportedSortsPhrase() + ")";
      return false;
    }
  }

  if (!isSupportedSort(codomain))
  {
    if (error != NULL)
      *error = "unsupported result sort " + sourceSortToSMTLib(codomain) +
               " (" + supportedSortsPhrase() + ")";
    return false;
  }
  return true;
}

UFSignature::UFSignature(std::vector<SourceSort> domain,
                         SourceSort codomain)
    : domain_(std::move(domain)), codomain_(std::move(codomain))
{
  std::string error;
  if (!validate(domain_, codomain_, &error))
    throw std::invalid_argument(error);
}

} // namespace stp

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

#include "stp/UninterpretedFunctions/UFLemma.h"
#include <set>

namespace stp
{

namespace
{

struct EqualityKey
{
  ASTNode left;
  ASTNode right;
  SourceSort sort;

  bool operator<(const EqualityKey& other) const
  {
    if (sort.kind() != other.sort.kind())
      return static_cast<int>(sort.kind()) <
             static_cast<int>(other.sort.kind());
    // Bool is the one admitted sort with no carrier width to compare;
    // everything else is separated by its packed width within a kind.
    if (sort.kind() != SourceSort::Kind::Bool &&
        sort.packedWidth() != other.sort.packedWidth())
      return sort.packedWidth() < other.sort.packedWidth();
    if (left != other.left)
      return left < other.left;
    return right < other.right;
  }
};

EqualityKey keyFor(ASTNode left, ASTNode right, const SourceSort& sort)
{
  if (right < left)
    std::swap(left, right);
  EqualityKey key;
  key.left = left;
  key.right = right;
  key.sort = sort;
  return key;
}

// What a lemma atom may be stated over. This is the *lowering* sort list, not
// the signature one: FloatingPoint is an admitted signature sort but is never
// a lemma sort, because a float is quotiented to its packed carrier before it
// reaches the checker at all.
bool supported(const SourceSort& sort)
{
  return UFSignature::isSupportedSort(sort) &&
         sort.kind() != SourceSort::Kind::FloatingPoint;
}

} // namespace

bool UFAbstractLemma::evaluate(
    bool conclusionEquality,
    const std::vector<bool>& premiseEqualities) const
{
  if (premiseEqualities.size() != premise.size())
    return false;
  bool premiseValue = true;
  for (const bool value : premiseEqualities)
    premiseValue = premiseValue && value;
  return !premiseValue || conclusionEquality;
}

bool UFLemmaOracle::buildAndValidate(const UFCongruenceConflict& conflict,
                                     UFAbstractLemma& lemma,
                                     std::string& diagnostic)
{
  lemma = UFAbstractLemma();
  diagnostic.clear();
  if (conflict.declaration == NULL || conflict.leftResult.IsNull() ||
      conflict.rightResult.IsNull() ||
      conflict.leftResultValue == conflict.rightResultValue)
  {
    diagnostic = "UF lemma certificate has no result conflict";
    return false;
  }
  // Certificates are stated at the lowering sort, which is what the CNF
  // encoder can build equalities over. It differs from the declared sort only
  // for FloatingPoint, whose bit-equality is not its equality -- so a float
  // reaches this oracle already quotiented to its canonical packed bits, and
  // never as a float.
  const SourceSort codomain = UFSignature::loweringSort(
      conflict.declaration->signature().codomain());
  const SourceSort resultSort = conflict.leftResult.GetSourceSort();
  const bool narrowedBV =
      codomain.kind() == SourceSort::Kind::BitVector &&
      resultSort.kind() == SourceSort::Kind::BitVector &&
      resultSort.bitVectorWidth() <= codomain.bitVectorWidth();
  if (!supported(resultSort) ||
      (resultSort != codomain && !narrowedBV) ||
      conflict.rightResult.GetSourceSort() != resultSort ||
      conflict.leftResultValue.sort() != resultSort ||
      conflict.rightResultValue.sort() != resultSort)
  {
    diagnostic = "UF lemma certificate has an invalid result sort";
    return false;
  }

  std::set<EqualityKey> seen;
  size_t expectedPosition = 0;
  for (const UFCongruenceArgument& argument : conflict.arguments)
  {
    if (argument.position != expectedPosition++ ||
        argument.position >= conflict.declaration->signature().arity() ||
        argument.sort != UFSignature::loweringSort(
                             conflict.declaration->signature()
                                 .domain()[argument.position]) ||
        argument.concreteValue.sort() != argument.sort ||
        argument.leftTheory.IsNull() || argument.rightTheory.IsNull() ||
        argument.leftTheory.GetSourceSort() != argument.sort ||
        argument.rightTheory.GetSourceSort() != argument.sort ||
        argument.leftScalar.IsNull() || argument.rightScalar.IsNull() ||
        argument.leftScalar.GetSourceSort() != argument.sort ||
        argument.rightScalar.GetSourceSort() != argument.sort ||
        (argument.leftScalar.GetKind() != SYMBOL &&
         !argument.leftScalar.isConstant()) ||
        (argument.rightScalar.GetKind() != SYMBOL &&
         !argument.rightScalar.isConstant()))
    {
      diagnostic = "UF lemma certificate has an invalid argument pair";
      return false;
    }

    // Exact identity makes this premise a reflexive true atom. Concrete
    // equality alone is deliberately insufficient to omit it.
    if (argument.leftScalar == argument.rightScalar)
      continue;

    // A constant/constant atom is decided without a SAT circuit. The
    // collided tuple says every premise is true, so unequal constants expose
    // a corrupt certificate; equal constants are canonical `true` and drop.
    if (argument.leftScalar.isConstant() &&
        argument.rightScalar.isConstant())
    {
      UFConcreteValue left;
      UFConcreteValue right;
      if (!UFConcreteValue::fromConstant(argument.leftScalar, argument.sort,
                                         left, diagnostic) ||
          !UFConcreteValue::fromConstant(argument.rightScalar, argument.sort,
                                         right, diagnostic))
        return false;
      if (left != right)
      {
        diagnostic = "UF lemma contains a structurally false constant "
                     "premise";
        return false;
      }
      continue;
    }

    const EqualityKey key = keyFor(argument.leftScalar, argument.rightScalar,
                                   argument.sort);
    if (!seen.insert(key).second)
      continue;

    UFEqualityAtom atom;
    atom.left = key.left;
    atom.right = key.right;
    atom.sort = argument.sort;
    atom.originalPosition = argument.position;
    lemma.premise.push_back(atom);
  }

  const EqualityKey conclusion =
      keyFor(conflict.leftResult, conflict.rightResult, resultSort);
  if (conclusion.left == conclusion.right)
  {
    diagnostic = "UF lemma conflict has a reflexive result equality";
    return false;
  }
  lemma.conclusion.left = conclusion.left;
  lemma.conclusion.right = conclusion.right;
  lemma.conclusion.sort = resultSort;
  lemma.conclusion.originalPosition = conflict.arguments.size();
  lemma.candidateVersion = conflict.candidateVersion;

  // The tuple collision proves every retained premise true; the distinct
  // result values prove the conclusion false. Evaluate the abstract clause
  // explicitly so validate-before-mutate is exercised in every build mode,
  // with assertions providing an additional debug audit rather than the only
  // enforcement.
  const std::vector<bool> premiseValues(lemma.premise.size(), true);
  if (lemma.evaluate(false, premiseValues))
  {
    diagnostic = "UF lemma does not reject its triggering candidate";
    return false;
  }
  return true;
}

} // namespace stp

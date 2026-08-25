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

#include "stp/UninterpretedFunctions/UFChecker.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "extlib-constbv/constantbv.h"
#include <ankerl/unordered_dense.h>
#include <algorithm>

namespace stp
{

namespace
{

bool supportedSort(const SourceSort& sort)
{
  return UFSignature::isSupportedSort(sort);
}

// Bool occupies one byte; every other admitted sort is stored as its packed
// carrier, so RoundingMode is five bits in one byte and a float is its IEEE
// interchange width.
size_t byteWidth(const SourceSort& sort)
{
  return sort.kind() == SourceSort::Kind::Bool
             ? 1
             : (sort.packedWidth() + 7) / 8;
}

int compareSort(const SourceSort& left, const SourceSort& right)
{
  const int lk = left.kind() == SourceSort::Kind::Bool ? 0 : 1;
  const int rk = right.kind() == SourceSort::Kind::Bool ? 0 : 1;
  if (lk != rk)
    return lk < rk ? -1 : 1;
  if (lk == 0)
    return 0;
  // Two values of the same packed width but different sorts never meet in
  // one comparison: a tuple position has one signature sort, and the model
  // order this feeds only ever sorts tuples of the same signature.
  if (left.packedWidth() == right.packedWidth())
    return 0;
  return left.packedWidth() < right.packedWidth() ? -1 : 1;
}

bool readScalar(const ASTNode& scalar, const SourceSort& expected,
                const UFScalarCandidate& candidate, UFConcreteValue& value,
                std::string& diagnostic)
{
  if (scalar.IsNull() ||
      (scalar.GetKind() != SYMBOL && !scalar.isConstant()) ||
      scalar.GetSourceSort() != expected)
  {
    diagnostic = "UFCHK scalar is not a canonical leaf of the expected "
                 "SourceSort";
    return false;
  }
  if (scalar.isConstant())
    return UFConcreteValue::fromConstant(scalar, expected, value, diagnostic);
  if (!candidate.read(scalar, expected, value, diagnostic))
    return false;
  if (value.sort() != expected)
  {
    diagnostic = "UFCHK candidate returned a value at the wrong SourceSort";
    return false;
  }
  return true;
}

struct Observation
{
  const LoweredApplicationRecord* record = NULL;
  UFConcreteValue result;
};

// Position-sensitive value hashing. Equality remains full typed tuple
// equality, so even adversarial collisions are semantically harmless. The
// hash owns no AST identity and does not assume constant interning.
struct ConcreteTupleHasher
{
  size_t operator()(const UFConcreteTuple& tuple) const
  {
    size_t hash = static_cast<size_t>(0x9e3779b97f4a7c15ULL);
    for (size_t i = 0; i < tuple.size(); ++i)
    {
      const UFConcreteValue& value = tuple[i];
      size_t component = value.sort().hash();
      for (const uint8_t byte : value.bytes())
        component = component * 1315423911u + byte;
      hash = (hash * 1315423911u) ^ ((i + 1) * 2654435761u) ^
             component;
      hash = hash * 1315423911u + i;
    }
    return hash;
  }
};

typedef ankerl::unordered_dense::map<UFConcreteTuple, Observation,
                                     ConcreteTupleHasher>
    ObservationTable;

} // namespace

UFConcreteValue UFConcreteValue::boolean(bool value)
{
  UFConcreteValue out;
  out.sort_ = SourceSort::boolean();
  out.bytes_.push_back(value ? 1 : 0);
  return out;
}

UFConcreteValue UFConcreteValue::scalar(const SourceSort& sort,
                                        const std::vector<uint8_t>& bytes)
{
  assert(sort.isScalar() && sort.packedWidth() > 0);
  const unsigned width = sort.packedWidth();
  UFConcreteValue out;
  out.sort_ = sort;
  out.bytes_ = bytes;
  out.bytes_.resize((width + 7) / 8, 0);
  const unsigned used = width % 8;
  if (used != 0)
    out.bytes_.back() &= static_cast<uint8_t>((1u << used) - 1u);
  return out;
}

UFConcreteValue UFConcreteValue::bitVector(
    unsigned width, const std::vector<uint8_t>& bytes)
{
  assert(width > 0);
  return scalar(SourceSort::bitVector(width), bytes);
}

UFConcreteValue UFConcreteValue::fromUInt(unsigned width, uint64_t value)
{
  std::vector<uint8_t> bytes((width + 7) / 8, 0);
  for (size_t i = 0; i < bytes.size() && i < sizeof(value); ++i)
    bytes[i] = static_cast<uint8_t>((value >> (8 * i)) & 0xffu);
  return bitVector(width, bytes);
}

UFConcreteValue UFConcreteValue::zero(const SourceSort& sort)
{
  if (sort.kind() == SourceSort::Kind::Bool)
    return boolean(false);
  assert(supportedSort(sort));
  // All-zeros is a value of every admitted sort but one. A rounding mode is
  // one-hot, so the all-zero carrier denotes no mode: it would print as the
  // else branch of a generated define-fun that is then not a legal term, and
  // it would be handed to an enclosing operator as a constant operand when a
  // nested application falls through to the default. RNE is the arbitrary
  // choice SMT-LIB itself makes wherever a mode is implied.
  if (sort.kind() == SourceSort::Kind::RoundingMode)
    return fromMode(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  return scalar(sort, std::vector<uint8_t>(byteWidth(sort), 0));
}

UFConcreteValue UFConcreteValue::fromMode(unsigned encoding)
{
  assert(symbolic_fp::isRoundingModeEncoding(encoding));
  std::vector<uint8_t> bytes(1, static_cast<uint8_t>(encoding));
  return scalar(SourceSort::roundingMode(), bytes);
}

bool UFConcreteValue::fromConstant(const ASTNode& constant,
                                   const SourceSort& sort,
                                   UFConcreteValue& value,
                                   std::string& diagnostic)
{
  if (!supportedSort(sort))
  {
    diagnostic = "UFCHK constant was requested at an unsupported SourceSort";
    return false;
  }
  // A model answers with the *carrier* of a source-sorted leaf -- a plain
  // BVCONST -- because that is what the SAT assignment materialises, while a
  // constant written in the query still carries its own sort. Both spell the
  // same value, so accept either: the leaf node's sort has already been
  // checked by whoever asked, and what is converted here is that leaf's
  // value. Widths must still agree exactly.
  const SourceSort constantSort = constant.GetSourceSort();
  const bool isCarrier = sort.kind() != SourceSort::Kind::Bool &&
                         constantSort.kind() == SourceSort::Kind::BitVector &&
                         constantSort.bitVectorWidth() == sort.packedWidth();
  if (constantSort != sort && !isCarrier)
  {
    diagnostic = "UFCHK constant does not match its expected SourceSort";
    return false;
  }
  if (sort.kind() == SourceSort::Kind::Bool)
  {
    if (constant.GetKind() != TRUE && constant.GetKind() != FALSE)
    {
      diagnostic = "UFCHK expected a concrete Boolean value";
      return false;
    }
    value = boolean(constant.GetKind() == TRUE);
    return true;
  }
  const unsigned width = sort.packedWidth();
  if (constant.GetKind() != BVCONST || constant.GetValueWidth() != width)
  {
    diagnostic = "UFCHK expected a concrete scalar value";
    return false;
  }
  // Bucketing by raw bytes is only the sort's own equality where every
  // representable carrier denotes a value. RoundingMode is the one admitted
  // sort where it is not: twenty-seven of its thirty-two patterns denote no
  // mode. Every RoundingMode scalar the checker can reach is pinned one-hot
  // -- by its declaration, by UF lowering, and again by FpTotalise -- so a
  // value that is not is a broken invariant, not an input the checker should
  // quietly bucket.
  if (sort.kind() == SourceSort::Kind::RoundingMode &&
      !symbolic_fp::isRoundingModeEncoding(constant.GetUnsignedConst()))
  {
    diagnostic = "UFCHK read a RoundingMode carrier that denotes no mode";
    return false;
  }
  std::vector<uint8_t> bytes(byteWidth(sort), 0);
  const CBV bits = constant.GetBVConst();
  for (unsigned i = 0; i < width; ++i)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      bytes[i / 8] |= static_cast<uint8_t>(1u << (i % 8));
  value = scalar(sort, bytes);
  return true;
}

bool UFConcreteValue::booleanValue() const
{
  assert(sort_.kind() == SourceSort::Kind::Bool && bytes_.size() == 1);
  return bytes_[0] != 0;
}

bool operator==(const UFConcreteValue& left, const UFConcreteValue& right)
{
  return left.sort_ == right.sort_ && left.bytes_ == right.bytes_;
}

bool operator<(const UFConcreteValue& left, const UFConcreteValue& right)
{
  const int sortOrder = compareSort(left.sort_, right.sort_);
  if (sortOrder != 0)
    return sortOrder < 0;
  // Numeric order: compare the most significant byte first.
  return std::lexicographical_compare(left.bytes_.rbegin(), left.bytes_.rend(),
                                      right.bytes_.rbegin(),
                                      right.bytes_.rend());
}

UFCheckPlan UFChecker::validate(
    const std::vector<const UFDecl*>& activeDeclarations,
    const LoweredApplicationView& view)
{
  UFCheckPlan plan;
  plan.view_ = &view;
  plan.declarations_ = activeDeclarations;
  std::sort(plan.declarations_.begin(), plan.declarations_.end(),
            [](const UFDecl* left, const UFDecl* right)
            {
              if (left == NULL || right == NULL)
                return left < right;
              return left->id() < right->id();
            });
  if (std::find(plan.declarations_.begin(), plan.declarations_.end(),
                nullptr) != plan.declarations_.end())
  {
    plan.diagnostic_ = "UFCHK received a null active declaration";
    return plan;
  }
  if (std::adjacent_find(plan.declarations_.begin(),
                         plan.declarations_.end()) !=
      plan.declarations_.end())
  {
    plan.diagnostic_ = "UFCHK received a duplicate active declaration";
    return plan;
  }
  const STPMgr* declarationOwner = NULL;
  for (size_t i = 0; i < plan.declarations_.size(); ++i)
  {
    const UFDecl* declaration = plan.declarations_[i];
    if (declaration->owner() == NULL)
    {
      plan.diagnostic_ = "UFCHK received an ownerless active declaration";
      return plan;
    }
    if (i != 0 && plan.declarations_[i - 1]->id() == declaration->id())
    {
      plan.diagnostic_ = "UFCHK received duplicate declaration identities";
      return plan;
    }
    if (declarationOwner == NULL)
      declarationOwner = declaration->owner();
    else if (declarationOwner != declaration->owner())
    {
      plan.diagnostic_ =
          "UFCHK active declarations cross manager ownership";
      return plan;
    }
    if (!supportedSort(declaration->signature().codomain()))
    {
      plan.diagnostic_ =
          "UFCHK active declaration has an unsupported codomain";
      return plan;
    }
    for (const SourceSort& sort : declaration->signature().domain())
      if (!supportedSort(sort))
      {
        plan.diagnostic_ =
            "UFCHK active declaration has an unsupported domain";
        return plan;
      }
  }

  plan.recordsByDecl_.resize(plan.declarations_.size());
  ankerl::unordered_dense::map<const UFDecl*, size_t> declarationIndex;
  declarationIndex.reserve(plan.declarations_.size());
  for (size_t i = 0; i < plan.declarations_.size(); ++i)
    declarationIndex.emplace(plan.declarations_[i], i);

  ankerl::unordered_dense::set<ASTNode, ASTNode::ASTNodeHasher,
                               ASTNode::ASTNodeEqual>
      handles;
  handles.reserve(view.applications.size());
  if (view.handleToResult.size() != view.applications.size())
  {
    plan.diagnostic_ =
        "UFCHK durable-handle result mapping has the wrong size";
    return plan;
  }
  size_t previousOrder = 0;
  bool firstRecord = true;
  for (const LoweredApplicationRecord& record : view.applications)
  {
    if (record.declaration == NULL || record.durableHandle.IsNull() ||
        record.resultSymbol.IsNull() ||
        record.durableHandle.GetKind() != UF_APPLY ||
        record.resultSymbol.GetKind() != SYMBOL ||
        !record.durableHandle.IsOwnedBy(record.declaration->owner()) ||
        !record.resultSymbol.IsOwnedBy(record.declaration->owner()) ||
        record.loweredActuals.size() != record.declaration->signature().arity() ||
        record.namedActuals.size() !=
            (record.observableArguments ? record.declaration->signature().arity()
                                        : 0))
    {
      plan.diagnostic_ =
          "UFCHK received a malformed lowered application view";
      return plan;
    }
    if (!firstRecord && record.stableOrder <= previousOrder)
    {
      plan.diagnostic_ = "UFCHK application order is not strictly stable";
      return plan;
    }
    firstRecord = false;
    previousOrder = record.stableOrder;
    if (!handles.insert(record.durableHandle).second)
    {
      plan.diagnostic_ = "UFCHK received a duplicate durable application";
      return plan;
    }
    const auto declarationIt = declarationIndex.find(record.declaration);
    if (declarationIt == declarationIndex.end())
    {
      plan.diagnostic_ = "UFCHK view references an inactive declaration";
      return plan;
    }
    const UFSignature& signature = record.declaration->signature();
    // Every scalar in a record is at the *lowering* sort. It coincides with
    // the declared sort everywhere but FloatingPoint, which the core never
    // sees: it is solved as its canonical packed carrier and only becomes a
    // float again at the model boundary.
    //
    // uf_narrow_results may have reduced the result width; the symbol then
    // carries a BitVector sort narrower than the declared codomain, and that
    // is legal as long as the kind stays BitVector.
    {
      const SourceSort expected =
          UFSignature::loweringSort(signature.codomain());
      const SourceSort actual = record.resultSymbol.GetSourceSort();
      if (actual != expected)
      {
        const bool narrowedBV =
            expected.kind() == SourceSort::Kind::BitVector &&
            actual.kind() == SourceSort::Kind::BitVector &&
            actual.bitVectorWidth() < expected.bitVectorWidth();
        if (!narrowedBV)
        {
          plan.diagnostic_ = "UFCHK result symbol has the wrong SourceSort";
          return plan;
        }
      }
    }
    for (size_t i = 0; i < signature.arity(); ++i)
    {
      const SourceSort solved =
          UFSignature::loweringSort(signature.domain()[i]);
      if (record.loweredActuals[i].IsNull() ||
          !record.loweredActuals[i].IsOwnedBy(record.declaration->owner()) ||
          record.loweredActuals[i].GetSourceSort() != solved)
      {
        plan.diagnostic_ = "UFCHK argument record is not a typed canonical "
                           "scalar pair";
        return plan;
      }
      // An unobservable record has no scalar tuple at all; the canonical-leaf
      // obligation applies to the records a candidate round actually reads.
      if (!record.observableArguments)
        continue;
      if (record.namedActuals[i].IsNull() ||
          !record.namedActuals[i].IsOwnedBy(record.declaration->owner()) ||
          record.namedActuals[i].GetSourceSort() != solved ||
          (record.namedActuals[i].GetKind() != SYMBOL &&
           !record.namedActuals[i].isConstant()))
      {
        plan.diagnostic_ = "UFCHK argument record is not a typed canonical "
                           "scalar pair";
        return plan;
      }
    }
    const ASTNodeMap::const_iterator resultIt =
        view.handleToResult.find(record.durableHandle);
    if (resultIt == view.handleToResult.end() ||
        resultIt->second != record.resultSymbol)
    {
      plan.diagnostic_ =
          "UFCHK durable-handle result mapping is inconsistent";
      return plan;
    }
    plan.recordsByDecl_[declarationIt->second].push_back(&record);
  }

  // Lowering withholds a scalar tuple only where no congruence lemma can ever
  // mention it. Once a declaration reaches two applications every one of them
  // must be readable, or a real conflict would go unnoticed and an unsound
  // model would be certified.
  for (const std::vector<const LoweredApplicationRecord*>& records :
       plan.recordsByDecl_)
  {
    if (records.size() < 2)
      continue;
    for (const LoweredApplicationRecord* record : records)
      if (!record->observableArguments)
      {
        plan.diagnostic_ = "UFCHK found a comparable declaration with an "
                           "unreadable application";
        return plan;
      }
  }

  plan.valid_ = true;
  return plan;
}

UFCheckResult UFChecker::check(const UFCheckPlan& plan,
                               const UFScalarCandidate& candidate,
                               const size_t maxConflicts)
{
  UFCheckResult out;
  const uint64_t candidateVersion = candidate.version();
  out.modelSeed.candidateVersion = candidateVersion;
  if (!plan.valid_ || plan.view_ == NULL)
  {
    out.diagnostic = plan.diagnostic_.empty()
                         ? "UFCHK received an unvalidated check plan"
                         : plan.diagnostic_;
    return out;
  }

  size_t conflictOrder = 0;
  for (size_t declarationIndex = 0;
       declarationIndex < plan.declarations_.size(); ++declarationIndex)
  {
    const UFDecl* declaration = plan.declarations_[declarationIndex];
    const std::vector<const LoweredApplicationRecord*>& records =
        plan.recordsByDecl_[declarationIndex];
    ObservationTable table;
    table.reserve(records.size());
    // A declaration whose single application has no readable argument tuple is
    // interpreted by the constant its result took: total, and by construction
    // in agreement with that one application, which is all any interpretation
    // of it has to satisfy.
    bool constantInterpretation = false;
    UFConcreteValue constantValue;
    const SourceSort resultSort = records.empty()
        ? UFSignature::loweringSort(declaration->signature().codomain())
        : records[0]->resultSymbol.GetSourceSort();
    for (const LoweredApplicationRecord* record : records)
    {
      if (!record->observableArguments)
      {
        if (!readScalar(record->resultSymbol, resultSort,
                        candidate, constantValue, out.diagnostic))
          return out;
        constantInterpretation = true;
        continue;
      }

      UFConcreteTuple tuple;
      tuple.reserve(record->namedActuals.size());
      for (size_t i = 0; i < record->namedActuals.size(); ++i)
      {
        UFConcreteValue value;
        if (!readScalar(record->namedActuals[i],
                        UFSignature::loweringSort(
                            declaration->signature().domain()[i]),
                        candidate, value, out.diagnostic))
          return out;
        tuple.push_back(value);
      }
      UFConcreteValue result;
      if (!readScalar(record->resultSymbol, resultSort,
                      candidate, result, out.diagnostic))
        return out;

      const ObservationTable::iterator found = table.find(tuple);
      if (found == table.end())
      {
        Observation observation;
        observation.record = record;
        observation.result = result;
        table.insert(std::make_pair(tuple, observation));
        out.stats.insertions++;
        continue;
      }

      out.stats.comparisons++;
      conflictOrder++;
      // Each record is compared against the one before it in the bucket, not
      // against the bucket's first record. Both relate every member of a
      // bucket after n-1 lemmas, but they differ in which pair a round that
      // hits the lemma cap actually emits. Against the first record, a
      // decisive pair of two adjacent late members is never stated directly:
      // if each of them happens to agree with the first record it yields no
      // conflict at all, and the pair only surfaces once every other member
      // has been forced out of the bucket. Chaining states it in the round it
      // appears.
      //
      // The property the encoder relies on is unchanged: a record is still
      // the right-hand side of at most one conflict, so two conflicts from one
      // candidate still cannot canonicalise to the same lemma and no duplicate
      // filter is needed. The bucket entry is updated whether or not the two
      // agreed, so the comparison is always against the immediate predecessor.
      const LoweredApplicationRecord& representative = *found->second.record;
      const UFConcreteValue previousResult = found->second.result;
      found->second.record = record;
      found->second.result = result;
      if (previousResult == result)
        continue;
      out.status = UFCheckResult::Status::Conflict;
      UFCongruenceConflict conflict;
      conflict.declaration = declaration;
      conflict.representativeHandle = representative.durableHandle;
      conflict.conflictingHandle = record->durableHandle;
      conflict.leftResult = representative.resultSymbol;
      conflict.rightResult = record->resultSymbol;
      conflict.leftResultValue = previousResult;
      conflict.rightResultValue = result;
      conflict.candidateVersion = candidateVersion;
      conflict.stableConflictOrder = conflictOrder;
      for (size_t i = 0; i < tuple.size(); ++i)
      {
        UFCongruenceArgument argument;
        argument.position = i;
        argument.sort =
            UFSignature::loweringSort(declaration->signature().domain()[i]);
        argument.leftTheory = representative.loweredActuals[i];
        argument.rightTheory = record->loweredActuals[i];
        argument.leftScalar = representative.namedActuals[i];
        argument.rightScalar = record->namedActuals[i];
        argument.concreteValue = tuple[i];
        conflict.arguments.push_back(argument);
      }
      out.conflicts.push_back(conflict);
      if (maxConflicts != 0 && out.conflicts.size() >= maxConflicts)
        break;
    }

    if (maxConflicts != 0 && out.conflicts.size() >= maxConflicts)
      break;

    // A conflicting candidate publishes no model, so stop paying for one --
    // including the case sort -- from the first conflict onwards.
    if (!out.conflicts.empty())
      continue;

    UFFunctionModelSeed function;
    function.declaration = declaration;
    function.defaultValue =
        constantInterpretation
            ? constantValue
            : UFConcreteValue::zero(resultSort);
    function.cases.reserve(table.size());
    for (const auto& entry : table)
    {
      UFModelCase modelCase;
      modelCase.arguments = entry.first;
      modelCase.result = entry.second.result;
      modelCase.representativeHandle =
          entry.second.record->durableHandle;
      function.cases.push_back(modelCase);
    }
    // Dense-table iteration is an implementation detail. Preserve the old
    // typed lexicographic model order explicitly, and pay this O(n log n)
    // cost only for the final consistent candidate rather than every round.
    std::sort(function.cases.begin(), function.cases.end(),
              [](const UFModelCase& left, const UFModelCase& right)
              { return left.arguments < right.arguments; });
    // Publish the commonest observed value as the else branch and drop every
    // case that agrees with it. The published interpretation is unchanged --
    // a dropped case falls through to exactly the value it named -- but a
    // function that took one value at all but a few of its observed points
    // now prints those few rather than one ite per point.
    //
    // A declaration interpreted by a constant keeps that constant: the record
    // that produced it has no readable tuple, so it has no case of its own and
    // only the else branch can satisfy it. Ties go to the smaller value, so
    // the choice stays a function of the candidate alone.
    if (!constantInterpretation && !function.cases.empty())
    {
      std::map<UFConcreteValue, size_t> byResult;
      for (const UFModelCase& modelCase : function.cases)
        byResult[modelCase.result]++;
      // std::map orders by UFConcreteValue, so scanning it forwards and
      // keeping a strict improvement makes ties go to the smaller value.
      size_t bestCount = 0;
      UFConcreteValue chosen;
      for (const std::pair<const UFConcreteValue, size_t>& entry : byResult)
        if (entry.second > bestCount)
        {
          bestCount = entry.second;
          chosen = entry.first;
        }
      if (bestCount > 1)
      {
        function.defaultValue = chosen;
        std::vector<UFModelCase> kept;
        kept.reserve(function.cases.size() - bestCount);
        for (const UFModelCase& modelCase : function.cases)
          if (modelCase.result != chosen)
            kept.push_back(modelCase);
        function.cases.swap(kept);
      }
    }
    out.modelSeed.functions.push_back(function);
  }

  // One version test covers the whole scan, conflicting or not: a candidate
  // that moved under it invalidates every conflict collected as well as any
  // seed, because the lemmas are only false against the assignment they were
  // read from.
  if (candidate.version() != candidateVersion)
  {
    out.status = UFCheckResult::Status::InternalError;
    out.diagnostic = "UFCHK candidate changed during one logical check";
    out.conflicts.clear();
    out.modelSeed = UFFunctionModelSeedSet();
    return out;
  }
  if (!out.conflicts.empty())
  {
    out.modelSeed = UFFunctionModelSeedSet();
    out.modelSeed.candidateVersion = candidateVersion;
    return out; // status is already Conflict
  }
  out.status = UFCheckResult::Status::Consistent;
  return out;
}

UFCheckResult UFChecker::check(
    const std::vector<const UFDecl*>& activeDeclarations,
    const LoweredApplicationView& view, const UFScalarCandidate& candidate,
    const size_t maxConflicts)
{
  return check(validate(activeDeclarations, view), candidate, maxConflicts);
}

} // namespace stp

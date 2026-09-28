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

/********************************************************************
 * Pure dynamic-Ackermann consistency checker.
 ********************************************************************/
#ifndef STP_UFCHECKER_H
#define STP_UFCHECKER_H

#include "stp/UninterpretedFunctions/UFLowering.h"
#include <cstdint>
#include <string>
#include <vector>

namespace stp
{

// Normalized, width-aware scalar value. The byte vector is little-endian;
// unused high bits are always zero. It owns no AST or SAT object.
class DLL_PUBLIC UFConcreteValue final
{
public:
  UFConcreteValue() = default;

  static UFConcreteValue boolean(bool value);
  // Any non-Bool admitted sort, stored as its packed carrier: a bit-vector's
  // own bits, a rounding mode's one-hot five, a float's IEEE interchange
  // encoding. The sort travels with the bytes, so two values of different
  // sorts never compare equal however their carriers line up.
  static UFConcreteValue scalar(const SourceSort& sort,
                                const std::vector<uint8_t>& bytes);
  static UFConcreteValue bitVector(unsigned width,
                                   const std::vector<uint8_t>& bytes);
  static UFConcreteValue fromUInt(unsigned width, uint64_t value);
  // One of the five one-hot RoundingMode encodings, as a value of that sort.
  static UFConcreteValue fromMode(unsigned encoding);
  // The interpretation to give a case nothing observed: all-zeros, except for
  // RoundingMode, whose all-zero carrier denotes no mode at all and which
  // therefore defaults to RNE.
  static UFConcreteValue zero(const SourceSort& sort);
  static bool fromConstant(const ASTNode& constant, const SourceSort& sort,
                           UFConcreteValue& value, std::string& diagnostic);

  const SourceSort& sort() const { return sort_; }
  const std::vector<uint8_t>& bytes() const { return bytes_; }
  bool booleanValue() const;

  friend bool operator==(const UFConcreteValue& left,
                         const UFConcreteValue& right);
  friend bool operator!=(const UFConcreteValue& left,
                         const UFConcreteValue& right)
  {
    return !(left == right);
  }
  friend bool operator<(const UFConcreteValue& left,
                        const UFConcreteValue& right);

private:
  SourceSort sort_;
  std::vector<uint8_t> bytes_;
};

typedef std::vector<UFConcreteValue> UFConcreteTuple;

// Read-only host bridge. Implementations may read a batch model map or a
// persistent totalized assignment, but the checker neither knows nor mutates
// either representation.
class DLL_PUBLIC UFScalarCandidate
{
public:
  virtual ~UFScalarCandidate() = default;
  virtual uint64_t version() const = 0;
  virtual bool read(const ASTNode& scalar, const SourceSort& expected,
                    UFConcreteValue& value,
                    std::string& diagnostic) const = 0;
};

struct DLL_PUBLIC UFCongruenceArgument
{
  size_t position = 0;
  SourceSort sort;
  ASTNode leftTheory;
  ASTNode rightTheory;
  ASTNode leftScalar;
  ASTNode rightScalar;
  UFConcreteValue concreteValue;
};

struct DLL_PUBLIC UFCongruenceConflict
{
  const UFDecl* declaration = NULL;
  ASTNode representativeHandle;
  ASTNode conflictingHandle;
  std::vector<UFCongruenceArgument> arguments;
  ASTNode leftResult;
  ASTNode rightResult;
  UFConcreteValue leftResultValue;
  UFConcreteValue rightResultValue;
  uint64_t candidateVersion = 0;
  size_t stableConflictOrder = 0;
};

struct DLL_PUBLIC UFModelCase
{
  UFConcreteTuple arguments;
  UFConcreteValue result;
  ASTNode representativeHandle;
};

struct DLL_PUBLIC UFFunctionModelSeed
{
  const UFDecl* declaration = NULL;
  std::vector<UFModelCase> cases;
  UFConcreteValue defaultValue;
};

struct DLL_PUBLIC UFFunctionModelSeedSet
{
  uint64_t candidateVersion = 0;
  std::vector<UFFunctionModelSeed> functions;
};

struct DLL_PUBLIC UFCheckStats
{
  size_t insertions = 0;
  size_t comparisons = 0;
};

class DLL_PUBLIC UFCheckResult final
{
public:
  enum class Status
  {
    Consistent,
    Conflict,
    InternalError
  };

  Status status = Status::InternalError;
  // Every conflict the candidate exposes, in the deterministic order the scan
  // met them. A conflicting candidate has no model seed.
  std::vector<UFCongruenceConflict> conflicts;
  UFFunctionModelSeedSet modelSeed;
  UFCheckStats stats;
  std::string diagnostic;

  bool consistent() const { return status == Status::Consistent; }
  bool hasConflict() const { return status == Status::Conflict; }
};

// Immutable, validated indexing of one lowered view. Adapters construct this
// once at beginQuery/beginBlock; candidate rounds therefore never repeat
// declaration sorting, ownership/type validation, or record grouping.
class DLL_PUBLIC UFCheckPlan final
{
public:
  bool valid() const { return valid_; }
  const std::string& diagnostic() const { return diagnostic_; }

private:
  friend class UFChecker;
  bool valid_ = false;
  const LoweredApplicationView* view_ = NULL;
  std::vector<const UFDecl*> declarations_;
  std::vector<std::vector<const LoweredApplicationRecord*>> recordsByDecl_;
  std::string diagnostic_;
};

// Stateless logical core. Every model-dependent tuple table is local to
// check(), making reset across refinement rounds a structural property rather
// than a caller obligation. The immutable structural work lives in a plan.
class DLL_PUBLIC UFChecker final
{
public:
  static UFCheckPlan
  validate(const std::vector<const UFDecl*>& activeDeclarations,
           const LoweredApplicationView& view);

  // maxConflicts caps how many conflicts one candidate may yield; 0 is
  // unlimited. Stopping early costs nothing but extra refinement rounds, so
  // the cap exists to bound clause growth, not to keep the scan cheap.
  static UFCheckResult check(const UFCheckPlan& plan,
                             const UFScalarCandidate& candidate,
                             size_t maxConflicts = 0);

  // Convenience for isolated callers and unit tests. Solve-mode adapters use
  // validate() once and the prepared overload above for every candidate.
  static UFCheckResult
  check(const std::vector<const UFDecl*>& activeDeclarations,
        const LoweredApplicationView& view,
        const UFScalarCandidate& candidate, size_t maxConflicts = 0);
};

} // namespace stp

#endif

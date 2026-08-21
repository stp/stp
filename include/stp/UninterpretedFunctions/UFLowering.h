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
 * Completed-root lowering for durable uninterpreted-function nodes.
 ********************************************************************/
#ifndef STP_UFLOWERING_H
#define STP_UFLOWERING_H

#include "stp/AST/AST.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <vector>

namespace stp
{

class STPMgr;
class UFContext;

// The semantic owner of one lowering. Batch scopes live for one fresh SAT
// query. Persistent scopes identify one exact-stack block in one encoding
// epoch; the block guard is filled by the persistent adapter once encoded.
struct DLL_PUBLIC UFSolveScope
{
  enum class Mode
  {
    Batch,
    Persistent
  };

  Mode mode = Mode::Batch;
  uint64_t id = 0;
  uint64_t epoch = 0;
  ASTNode blockGuard;

  static UFSolveScope batch(uint64_t id_)
  {
    UFSolveScope scope;
    scope.mode = Mode::Batch;
    scope.id = id_;
    return scope;
  }

  static UFSolveScope persistent(uint64_t id_, uint64_t epoch_)
  {
    UFSolveScope scope;
    scope.mode = Mode::Persistent;
    scope.id = id_;
    scope.epoch = epoch_;
    return scope;
  }
};

// One application as seen after all frontend substitution and after nested
// UF applications in its actuals have themselves been lowered.
struct DLL_PUBLIC LoweredApplicationRecord
{
  ASTNode durableHandle;
  const UFDecl* declaration = NULL;
  ASTVec loweredActuals;
  ASTVec namedActuals;
  ASTNode resultSymbol;
  UFSolveScope scope;
  size_t stableOrder = 0;
  // Whether the checker can read this application's argument tuple, i.e.
  // whether every actual is a constant or a registered solve scalar. False
  // when lowering declined to name a compound actual because the declaration
  // has too few applications for any congruence lemma to mention it; such a
  // record carries no namedActuals and is interpreted by a constant.
  bool observableArguments = true;
};

// Value object owned by a solve-mode adapter. It deliberately contains no SAT
// state: M3's checker consumes it as immutable semantic input, while the batch
// and persistent adapters own their distinct clause/cache lifetimes.
class DLL_PUBLIC LoweredApplicationView final
{
public:
  UFSolveScope scope;
  ASTNode publicRoot;
  ASTNode semanticRoot;
  std::vector<LoweredApplicationRecord> applications;
  ASTNodeMap handleToResult;
  ASTNodeMap nameToTerm;
  ASTVec namingDefinitions;
  // Side conditions without which a solve scalar would denote nothing. Only
  // RoundingMode needs one today: its 5-bit carrier has thirty-two patterns
  // and the sort has five values, so every RoundingMode scalar this lowering
  // registers is pinned one-hot here. FpTotalise pins the same symbols when
  // it runs, and the constraint is idempotent, but relying on that would make
  // a model's legality depend on a pass ordering rather than on lowering.
  ASTVec sortConstraints;
  ASTNodeSet protectedSymbols;
  // Every symbolic checker leaf has exactly one concrete candidate
  // authority: its complete Bool/BV mapping in the live SAT backend.  This
  // is deliberately explicit rather than inferred from formula reachability;
  // preprocessing may leave a result or name only in future UF lemmas.
  ASTNodeSet solveScalars;

  bool active() const { return !applications.empty(); }
  size_t size() const { return applications.size(); }

  // Attach the query/block-local name definitions to the lowered semantic
  // formula. Result symbols intentionally have no eager UF definition.
  ASTNode semanticRootWithDefinitions(STPMgr* manager) const;
};

class DLL_PUBLIC UFLowering final
{
public:
  explicit UFLowering(STPMgr* manager);

  UFLowering(const UFLowering&) = delete;
  UFLowering& operator=(const UFLowering&) = delete;

  LoweredApplicationView lowerCompletedRoot(const ASTNode& publicRoot,
                                            const UFSolveScope& scope) const;

private:
  STPMgr* const manager_;
};

} // namespace stp

#endif

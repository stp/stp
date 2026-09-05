// -*- c++ -*-
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

#ifndef INCREMENTALSCOPESTATE_H_
#define INCREMENTALSCOPESTATE_H_

#include "stp/AST/AST.h"

#include <cstdint>
#include <utility>
#include <vector>

namespace stp
{

// One definition removed by a semantic preprocessing transaction. `witness`
// distinguishes a satisfying value chosen by RemoveUnconstrained from an
// equation implied by the input; witness restoration therefore uses the raw
// roots in `originals`, never an asserted equality to the chosen value.
struct ScopedElimination
{
  ASTNode symbol;
  ASTNode value;
  bool witness;
  ASTVec originals;

  ScopedElimination() : witness(false) {}

  ScopedElimination(const ASTNode& symbol_, const ASTNode& value_,
                    bool witness_ = false)
      : symbol(symbol_), value(value_), witness(witness_)
  {
  }
};

// A justification emitted by scoped constant propagation. The assertion is
// encoded in the same scope as the rewritten formula; domain records which
// substitution entry it justifies and is used to prevent duplicate facts.
struct ScopedFact
{
  ASTNode domain;
  ASTNode assertion;

  ScopedFact(const ASTNode& domain_, const ASTNode& assertion_)
      : domain(domain_), assertion(assertion_)
  {
  }
};

enum class PreprocessingMode
{
  Raw,
  PerLevel,
  ExactStack,
  PermanentBase
};

// The atomic output of one semantic preprocessing decision. Formula output,
// eliminated definitions and justification facts travel together: callers
// commit the whole value to its scope or discard the whole value. This keeps
// model replay and encoded strength from being advanced by different code
// paths when a trial is rejected, times out, or routes elsewhere.
struct PreprocessingTransaction
{
  PreprocessingMode mode;
  ASTNode source;
  ASTVec conjuncts;
  std::vector<ScopedElimination> eliminated;
  ASTNodeSet eliminatedVariables;
  std::vector<ScopedFact> facts;
  bool accepted;

  explicit PreprocessingTransaction(
      PreprocessingMode mode_ = PreprocessingMode::Raw,
      const ASTNode& source_ = ASTNode())
      : mode(mode_), source(source_), accepted(true)
  {
  }

  void addElimination(const ASTNode& symbol, const ASTNode& value,
                      bool witness = false)
  {
    eliminated.push_back(ScopedElimination(symbol, value, witness));
    if (symbol.GetKind() == SYMBOL)
      eliminatedVariables.insert(symbol);
  }

  size_t eliminatedSymbolCount() const
  {
    size_t count = 0;
    for (const ScopedElimination& e : eliminated)
      if (e.symbol.GetKind() == SYMBOL)
        ++count;
    return count;
  }
};

// Single owner of assertion-scope identity and every semantic view whose
// validity is scoped to a stack prefix. Structural AST/AIG/CNF caches remain
// content-addressed and session-persistent; this class owns only activation,
// preprocessing and consumer-cursor state.
class IncrementalScopeState
{
public:
  struct Level
  {
    uint64_t id;
    ASTNode rawConjunction;
    size_t stableSolves;
    bool promoted;
    ASTVec promotedConjuncts;
    PreprocessingTransaction activePreprocessing;

    Level(uint64_t id_, const ASTNode& raw_)
        : id(id_), rawConjunction(raw_), stableSolves(0), promoted(false),
          activePreprocessing(PreprocessingMode::Raw, raw_)
    {
    }
  };

  struct CbpMemo
  {
    ASTNode rawConjunction;
    std::vector<std::pair<ASTNode, ASTNode>> rewrites;
    std::vector<ScopedFact> facts;
  };

  struct ReconcileResult
  {
    size_t commonPrefix;
    bool promotedPrefixRetracted;
  };

private:
  std::vector<Level> levels;
  uint64_t nextLevelId;
  size_t lastCommonPrefixValue;

  // Independent processed-prefix cursors. They deliberately do not truncate
  // in reconcile(): a route which does not invoke CBP still owes a later CBP
  // call the divergence between its old processed prefix and the new ledger.
  struct ConsumerLevel
  {
    uint64_t scopeId;
    ASTNode rawConjunction;

    ConsumerLevel(uint64_t scopeId_, const ASTNode& raw_)
        : scopeId(scopeId_), rawConjunction(raw_)
    {
    }
  };
  std::vector<ConsumerLevel> cbpFedLevels;
  std::vector<CbpMemo> cbpMemos;

  size_t promotedDepthValue;
  bool promotionDriftPending;

  bool wholeStackActive;
  PreprocessingTransaction wholeStackPreprocessing;
  std::vector<ScopedElimination> currentEliminations;
  ASTNodeSet currentEliminatedVariables;
  ASTVec currentSemanticKeys;

  void clearCurrentPreprocessing();
  void aggregate(const PreprocessingTransaction& transaction);

public:
  IncrementalScopeState();

  ReconcileResult reconcile(const ASTVec& rawStack);

  size_t size() const { return levels.size(); }
  const Level& levelAt(size_t index) const { return levels.at(index); }
  Level& levelAt(size_t index) { return levels.at(index); }
  size_t lastCommonPrefix() const { return lastCommonPrefixValue; }

  void commitLevel(size_t level,
                   const PreprocessingTransaction& transaction);
  void commitWholeStack(const PreprocessingTransaction& transaction);

  const std::vector<ScopedElimination>& activeEliminations() const
  {
    return currentEliminations;
  }
  const ASTNodeSet& activeEliminatedVariables() const
  {
    return currentEliminatedVariables;
  }
  const ASTVec& activeSemanticKeys() const { return currentSemanticKeys; }

  size_t promotedDepth() const { return promotedDepthValue; }
  size_t stableSolves(size_t level) const
  {
    return levels.at(level).stableSolves;
  }
  bool promotedConjunctsChanged(size_t level,
                                const ASTVec& conjuncts) const;
  void promote(size_t level, const ASTVec& conjuncts);
  void notePromotionDrift() { promotionDriftPending = true; }
  void clearPromotions();

  size_t cbpFedDepth() const { return cbpFedLevels.size(); }
  size_t cbpFedCommonPrefix() const;
  void markCbpFed(size_t level);
  void rollbackCbpFedTo(size_t depth);
  void resetCbpFed() { cbpFedLevels.clear(); }
  // Preserve the live raw level ledger, but release storage belonging to
  // consumers and preprocessing transactions from the retiring encoding
  // epoch. Called only after reconcile(), before this solve commits a new
  // transaction.
  void releaseEpochStorage();

  size_t trimCbpMemoToCurrent();
  size_t cbpMemoDepth() const { return cbpMemos.size(); }
  bool hasCbpMemo(size_t level) const { return level < cbpMemos.size(); }
  CbpMemo& startCbpMemo(size_t level);
  CbpMemo& cbpMemo(size_t level) { return cbpMemos.at(level); }
  const CbpMemo& cbpMemo(size_t level) const { return cbpMemos.at(level); }
};

} // namespace stp

#endif

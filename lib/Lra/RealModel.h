#ifndef STP_LRA_REAL_MODEL_H
#define STP_LRA_REAL_MODEL_H

#include "ExactRational.h"
#include "stp/AST/AST.h"

#include <iosfwd>
#include <functional>
#include <unordered_map>
#include <string>
#include <utility>
#include <vector>

namespace stp::lra {

struct RealModelSeed final
{
  ASTNode symbol;
  std::string numerator_decimal;
  std::string denominator_decimal;
};


struct RealModelStrings final
{
  std::string canonical_fraction;
  std::string numerator_decimal;
  std::string denominator_decimal;
  std::string smtlib;
};

// Manager-owned, solve-independent exact Real model.  Every exact value is
// reconstructed under this object's own NumberBudget, so no solve-context
// budget, core object, registry ID, SAT literal, witness, or producer pointer
// survives publication.  ASTNode values are owning references to the public
// symbols they name, not borrowed raw pointers.
class RealModel final
{
public:
  RealModel(NumberLimits limits, const std::vector<RealModelSeed>& staged,
            const ASTVec& required_symbols);
  ~RealModel() noexcept = default;

  RealModel(const RealModel&) = delete;
  RealModel& operator=(const RealModel&) = delete;

  /* How to decide the Boolean part of a Real ite's condition.
   *
   * A model of the Real variables cannot answer a condition that mentions
   * Boolean ones, and the calendar-automata families guard their min/max
   * with exactly that. The verifier does have somewhere to ask -- the
   * counterexample carries every Boolean value -- so it lends this model an
   * oracle for the duration. Left unset, such a condition is refused rather
   * than guessed, which is what a bare model query should do. */
  using ConditionOracle = std::function<bool(const ASTNode&)>;
  void setConditionOracle(ConditionOracle oracle)
  {
    // A term through a Real ite reads the oracle, so its cached value is
    // only valid for the oracle that produced it. Changing the oracle
    // invalidates the memo; setting it once, as the verifier does, costs
    // nothing.
    condition_oracle_ = std::move(oracle);
    eval_cache_.clear();
  }

  bool hasConditionOracle() const noexcept
  {
    return static_cast<bool>(condition_oracle_);
  }

  bool hasValue(const ASTNode& term) const noexcept;
  RealModelStrings stringsFor(const ASTNode& term) const;
  int compareTerms(const ASTNode& left, const ASTNode& right) const;
  bool predicateValue(const ASTNode& predicate) const;
  std::size_t size() const noexcept { return entries_.size(); }

  void printSmtlibDefinitions(std::ostream& out,
                              const ASTVec& visible_symbols) const;

private:
  struct Entry final
  {
    Entry(ASTNode source_symbol, ExactRational exact_value)
        : symbol(std::move(source_symbol)), value(std::move(exact_value))
    {
    }

    ASTNode symbol;
    ExactRational value;
  };

  // Give one entry its place in symbol_index_. Every insertion into entries_
  // goes through here, so the two cannot drift apart.
  void indexLastEntry();

  const ExactRational* findSymbol(const ASTNode& symbol) const noexcept;
  // The value of a Real term under this model, memoised. The model is a
  // fixed assignment and the evaluation is a pure function of the term, so
  // a term (and every shared subterm) is evaluated once; a source-predicate
  // check that shares subterms across predicates then pays for each once.
  ExactRational evaluateTermInScope(const ASTNode& term) const;
  ExactRational evaluateTermUncached(const ASTNode& term) const;
  bool conditionValue(const ASTNode& condition) const;
  ConditionOracle condition_oracle_;
  static std::string smtlibValue(const ExactRational& value);

  // Values are destroyed before their allocation budget (reverse member
  // order), which is the structural lifetime required by ExactRational.
  mutable NumberBudget budget_;
  std::vector<Entry> entries_;
  // Where each entry sits in entries_, by symbol node number.
  //
  // This was a linear scan, and findSymbol is the innermost thing the
  // verifier does: once per symbol leaf of every term it evaluates, against
  // a model that carries one entry per Real symbol of the query. On a
  // cpachecker-induction file that is 2 321 entries scanned for each of the
  // symbol occurrences in 10 172 source predicates, three times over as the
  // congruence rounds recommit -- and it inlined into evaluateTermUncached,
  // which is why the profile charged 24.5% of the solve to that function's
  // own instructions while every ExactRational operation beneath it came to
  // about 1.5%. The lookup carries no arithmetic; it was pure search.
  //
  // Node number rather than the node: hash-consing puts the pointer and the
  // number in bijection, so this is the same key operator== compares, and it
  // is the key eval_cache_ already uses.
  std::unordered_map<std::uint64_t, std::size_t> symbol_index_;
  // Declared after the budget, so its exact values are destroyed before it.
  // Keyed by node number: hash-consing gives structurally equal terms the
  // same number, which is exactly the sharing this memoises.
  mutable std::unordered_map<uint64_t, ExactRational> eval_cache_;
};

} // namespace stp::lra

#endif

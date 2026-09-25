#ifndef STP_LRA_REAL_MODEL_H
#define STP_LRA_REAL_MODEL_H

#include "ExactRational.h"
#include "stp/AST/AST.h"

#include <iosfwd>
#include <functional>
#include <unordered_map>
#include <map>
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
  // A required symbol the solve never valued -- one no arithmetic mentions
  // -- is given zero, unless it is named in `spread_symbols`, in which case
  // it is given a value distinct from every other value in the model. Any
  // value is a model value for such a symbol; the ones named are the
  // arguments of uninterpreted applications, which would otherwise all sit
  // at zero and be taken for equal by every congruence check.
  RealModel(NumberLimits limits, const std::vector<RealModelSeed>& staged,
            const ASTVec& required_symbols,
            const ASTVec& spread_symbols = ASTVec());
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

  // The other model's value key for a non-Real UF argument. Install before
  // defineApplicationValues, so indexed observations and later queries use
  // exactly the same interpretation. A failed evaluation must throw.
  using ScalarKeyOracle = std::function<std::string(const ASTNode&)>;
  void setScalarKeyOracle(ScalarKeyOracle oracle)
  {
    scalar_key_oracle_ = std::move(oracle);
    eval_cache_.clear();
  }

  /* Give the applications of uninterpreted functions their model values.
   *
   * A Real-sorted application is not evaluated structurally the way a sum or
   * an ite is: the UF lowering replaced it with a result symbol before the
   * arithmetic ever saw it, and that symbol is what the solve valued. So the
   * value exists and is already in this model -- it just answers to the
   * wrong name. `handle_to_result` is UFLowering's own mapping from each
   * application to its result symbol; this copies the value across so the
   * application a caller holds is a term this model can be asked about.
   *
   * Applications at other sorts are ignored: their values are read through
   * the UF checker's certified model, which compares packed carriers.
   */
  void defineApplicationValues(const ASTNodeMap& handle_to_result);

  // This model is the committed answer rather than a candidate under
  // verification. Until it is, an uninterpreted-function application is not
  // its to decide: see the UF_APPLY arm of evaluateTermUncached.
  void markCommitted() noexcept { committed_ = true; }

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
  /* The value of an uninterpreted-function application, by congruence.
   *
   * An application the solve never lowered has no value of its own -- a
   * get-value may ask about a term the assertions never mentioned, and the
   * lowering only reaches the ones they did. Any value satisfies such an
   * application, but not independently of the others: two applications of one
   * function whose arguments have equal values must agree, whether or not
   * either was lowered.
   *
   * So they are keyed on what congruence is actually about -- the function,
   * and the *values* its arguments take in this model, rather than the syntax
   * of those arguments. An application that matches a lowered one answers
   * with its value; one that matches nothing is unconstrained in this model
   * and answers zero, as an unvalued required symbol does.
   */
  std::string applicationKey(const ASTNode& application) const;
  ExactRational applicationValue(const ASTNode& application) const;
  // The value of a Real term under this model, memoised. The model is a
  // fixed assignment and the evaluation is a pure function of the term, so
  // a term (and every shared subterm) is evaluated once; a source-predicate
  // check that shares subterms across predicates then pays for each once.
  ExactRational evaluateTermInScope(const ASTNode& term) const;
  ExactRational evaluateTermUncached(const ASTNode& term) const;
  bool conditionValue(const ASTNode& condition) const;
  ConditionOracle condition_oracle_;
  ScalarKeyOracle scalar_key_oracle_;
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
  // Built by defineApplicationValues from the applications the solve lowered;
  // read by applicationValue for the ones it did not.
  std::map<std::string, ExactRational> applications_;
  // Set when this model is installed as the committed one. See
  // markCommitted, and the UF_APPLY arm of evaluateTermUncached.
  bool committed_ = false;
  // Declared after the budget, so its exact values are destroyed before it.
  // Keyed by node number: hash-consing gives structurally equal terms the
  // same number, which is exactly the sharing this memoises.
  mutable std::unordered_map<uint64_t, ExactRational> eval_cache_;
};

} // namespace stp::lra

#endif

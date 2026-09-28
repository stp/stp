#include "RealModel.h"

#include "ASTRealConst.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <cstring>
#include <map>
#include <ostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace printer {
void SMTLIB2_Print1(std::ostream& out, stp::ASTNode node, int indentation,
                    bool letize);
}

namespace stp::lra {

namespace {

bool realSymbol(const ASTNode& node) noexcept
{
  return !node.IsNull() && node.GetKind() == SYMBOL &&
         node.GetSourceSort().kind() == SourceSort::Kind::Real;
}

bool symbolOrder(const ASTNode& left, const ASTNode& right)
{
  const int name_order = std::strcmp(left.GetName(), right.GetName());
  if (name_order != 0)
    return name_order < 0;
  return left.GetNodeNum() < right.GetNodeNum();
}

} // namespace

RealModel::RealModel(NumberLimits limits,
                     const std::vector<RealModelSeed>& staged,
                     const ASTVec& required_symbols,
                     const ASTVec& spread_symbols)
    : budget_(limits)
{
  NumberOperationScope operation(budget_);
  std::map<ASTNode, std::pair<std::string, std::string>, ExprLess> exact_text;
  for (const RealModelSeed& seed : staged)
  {
    if (!realSymbol(seed.symbol) || seed.numerator_decimal.empty() ||
        seed.denominator_decimal.empty() ||
        seed.denominator_decimal.front() == '-' ||
        seed.denominator_decimal == "0")
      throw std::runtime_error("invalid staged Real model seed");
    if (!exact_text
             .emplace(seed.symbol,
                      std::make_pair(seed.numerator_decimal,
                                     seed.denominator_decimal))
             .second)
      throw std::runtime_error("duplicate staged Real model symbol");
  }

  std::set<ASTNode, ExprLess> symbols;
  for (const auto& seed : exact_text)
    symbols.insert(seed.first);
  for (const ASTNode& symbol : required_symbols)
  {
    if (!realSymbol(symbol))
      throw std::runtime_error("Real model requirement is not a Real symbol");
    symbols.insert(symbol);
  }

  std::vector<ASTNode> ordered(symbols.begin(), symbols.end());
  std::sort(ordered.begin(), ordered.end(), symbolOrder);
  entries_.reserve(ordered.size());
  symbol_index_.reserve(ordered.size());

  // Every value the solve produced, by canonical text, so that a spread
  // symbol can be given the smallest positive integer none of them holds --
  // deterministic in symbol order, and distinct from the other spread symbols
  // because each one takes its value out of the pool as it goes.
  const std::set<ASTNode, ExprLess> spread(spread_symbols.begin(),
                                           spread_symbols.end());
  std::set<std::string> taken;
  for (const auto& seed : exact_text)
    taken.insert(seed.second.first + "/" + seed.second.second);
  std::int64_t next_spread = 1;

  for (const ASTNode& symbol : ordered)
  {
    const auto found = exact_text.find(symbol);
    ExactRational value = ExactRational(std::int64_t{0});
    if (found != exact_text.end())
      value = ExactRational::fromCanonicalIntegers(found->second.first,
                                                   found->second.second);
    else if (spread.count(symbol) != 0)
    {
      for (;; ++next_spread)
        if (taken.insert(std::to_string(next_spread) + "/1").second)
          break;
      value = ExactRational(next_spread++);
    }
    if (!value.invariantHolds() || value.denominatorDecimal().empty() ||
        value.denominatorDecimal().front() == '-' ||
        value.denominatorDecimal() == "0")
      throw std::runtime_error("published Real model value is not canonical");
    entries_.emplace_back(symbol, std::move(value));
    indexLastEntry();
  }

}

void RealModel::reconstruct(const std::vector<RealModelDefinition>& definitions)
{
  if (committed_)
    throw std::runtime_error("cannot reconstruct a committed model");
  eval_cache_.clear();
  std::set<ASTNode, ExprLess> pending;
  for (const auto& definition : definitions)
    if (!realSymbol(definition.symbol) ||
        !pending.insert(definition.symbol).second)
      throw std::runtime_error("invalid or duplicate reconstruction target");
  for (const auto& definition : definitions)
  {
    using DefinitionKind = RealModelDefinition::Kind;
    const bool affine = definition.kind == DefinitionKind::Affine;
    if ((affine && (definition.term.IsNull() || !definition.bounds.empty())) ||
        (!affine && (!definition.term.IsNull() || definition.bounds.empty() ||
                     (definition.kind != DefinitionKind::AboveMaximum &&
                      definition.kind != DefinitionKind::BelowMinimum))))
      throw std::runtime_error("invalid reconstruction expression");
    // Validate the dependency order at the publication boundary, including
    // self-reference. Do not silently use a required symbol's default zero.
    ASTVec todo = affine ? ASTVec{definition.term} : definition.bounds;
    ASTNodeSet seen;
    while (!todo.empty())
    {
      const auto node = todo.back();
      todo.pop_back();
      if (node.IsNull())
        throw std::runtime_error("null reconstruction expression");
      if (!seen.insert(node).second)
        continue;
      if (pending.count(node))
        throw std::runtime_error("cyclic or unordered reconstruction");
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    }
    auto value = evaluateTermInScope(affine ? definition.term
                                          : definition.bounds.front());
    if (!affine)
    {
      const bool lower = definition.kind == DefinitionKind::AboveMaximum;
      for (std::size_t i = 1; i < definition.bounds.size(); ++i)
      {
        auto bound = evaluateTermInScope(definition.bounds[i]);
        NumberOperationScope operation(budget_);
        const int comparison = bound.compare(value);
        if (lower ? comparison > 0 : comparison < 0)
          value = std::move(bound);
      }
      NumberOperationScope operation(budget_);
      value += ExactRational(std::int64_t{lower ? 1 : -1});
    }
    const auto found = symbol_index_.find(definition.symbol.GetNodeNum());
    if (found == symbol_index_.end())
    {
      entries_.emplace_back(definition.symbol, std::move(value));
      indexLastEntry();
    }
    else
      entries_[found->second].value = std::move(value);
    pending.erase(definition.symbol);
  }
  // Queries following publication must see only reconstructed values.
  eval_cache_.clear();
}

void RealModel::indexLastEntry()
{
  // Positions are stable: entries_ is only ever appended to, never erased
  // from or reordered, so an index recorded here stays correct for the life
  // of the model. A duplicate symbol would silently shadow, so refuse it --
  // the constructor already rejects duplicate seeds, and
  // defineApplicationValues checks findSymbol before it appends.
  const ASTNode& symbol = entries_.back().symbol;
  if (!symbol_index_.emplace(symbol.GetNodeNum(), entries_.size() - 1).second)
    throw std::runtime_error("duplicate symbol in the exact Real model");
}

const ExactRational* RealModel::findSymbol(const ASTNode& symbol) const noexcept
{
  // A null node has no number to ask for; the scan this replaced answered
  // such a query with "not here", so keep that.
  if (symbol.IsNull())
    return nullptr;
  const auto found = symbol_index_.find(symbol.GetNodeNum());
  if (found == symbol_index_.end())
    return nullptr;
  return &entries_[found->second].value;
}


std::string RealModel::applicationKey(const ASTNode& application) const
{
  // One value-based interpretation at every sort. The scalar oracle uses
  // UFModel's canonical keys, also used by solver-side lazy congruence.
  // Evaluate outside an arithmetic scope: a scalar expression can itself
  // ask this model about a Real predicate or application.
  const std::size_t arity = application.Degree();
  std::string key = std::to_string(application[0].GetNodeNum());
  for (std::size_t i = 1; i != arity; ++i)
  {
    const ASTNode& argument = application[i];
    std::string value;
    if (argument.GetSourceSort().kind() == SourceSort::Kind::Real)
      value = "r:" + stringsFor(argument).canonical_fraction;
    else
    {
      if (!scalar_key_oracle_)
        throw std::runtime_error("exact Real model has no scalar argument oracle");
      value = scalar_key_oracle_(argument);
    }
    key += '|' + std::to_string(value.size()) + ':' + value;
  }
  return key;
}

ExactRational RealModel::applicationValue(const ASTNode& application) const
{
  if (application.Degree() < 2)
    throw std::runtime_error("malformed uninterpreted-function application");
  // Failure to evaluate an argument is not evidence that its tuple differs
  // from every observed tuple. Refuse that query; only a successfully read,
  // unmatched tuple may take the default below.
  const std::string key = applicationKey(application);
  const auto found = applications_.find(key);
  if (found != applications_.end())
  {
    NumberOperationScope operation(budget_);
    return found->second;
  }
  // Congruent to nothing the solve valued, so nothing in this model
  // constrains it. Zero, as an unvalued required symbol gets: any value
  // would do, and a fixed one keeps repeated queries agreeing with each
  // other as well as with congruence.
  NumberOperationScope operation(budget_);
  return ExactRational(std::int64_t{0});
}

ExactRational RealModel::evaluateTermInScope(const ASTNode& term) const
{
  // A symbol is O(1) -- one lookup in symbol_index_ -- so caching it would
  // only add a map entry and a copy. Cache the compound terms, whose
  // re-evaluation over a shared subtree is what this exists to avoid.
  //
  // A constant is cached with them, and is not the O(1) leaf it reads as.
  // Its arm cannot simply copy the node's value: the AST owns that under the
  // manager's budget and this model accounts to its own, and the two are
  // never active at once, so the value crosses as decimal text and is
  // rebuilt from it. That is two string allocations and a parse, paid once
  // per occurrence where the memo makes it once per distinct constant.
  const Kind kind = term.IsNull() ? UNDEFINED : term.GetKind();
  const bool cacheable = kind != UNDEFINED && kind != SYMBOL;
  if (cacheable)
  {
    const auto cached = eval_cache_.find(term.GetNodeNum());
    if (cached != eval_cache_.end())
    {
      NumberOperationScope operation(budget_);
      return cached->second;
    }
  }
  ExactRational value = evaluateTermUncached(term);
  if (cacheable)
  {
    NumberOperationScope operation(budget_);
    eval_cache_.emplace(term.GetNodeNum(), value);
  }
  return value;
}

ExactRational RealModel::evaluateTermUncached(const ASTNode& term) const
{
  if (term.IsNull() ||
      term.GetSourceSort().kind() != SourceSort::Kind::Real)
    throw std::runtime_error("exact model evaluation requires a Real term");

  switch (term.GetKind())
  {
    case SYMBOL:
    {
      const ExactRational* value = findSymbol(term);
      if (value == nullptr)
        throw std::runtime_error("exact Real model has no value for symbol");
      NumberOperationScope operation(budget_);
      return *value;
    }
    case UF_APPLY:
    {
      // A leaf like a symbol, and for the same reason: the arithmetic never
      // saw inside it. If the solve lowered this application,
      // defineApplicationValues put its value here directly.
      if (const ExactRational* value = findSymbol(term))
      {
        NumberOperationScope operation(budget_);
        return *value;
      }
      // Otherwise it is an application the assertions never mentioned -- a
      // get-value may ask about one -- and congruence decides it. See
      // applicationValue.
      //
      // Only once this model is the committed one. Deciding an application in
      // a candidate is neither wanted nor possible: the argument values that
      // congruence is keyed on may need a Real ite's condition, which is
      // answered by walking the counterexample, which comes back here for the
      // Real terms in it -- and finds no installed model to ask, because this
      // candidate is not installed yet. Refusing, as this arm always did
      // before there was a congruence index, leaves the verifier to reject
      // the candidate and the refinement loop to carry on.
      if (!committed_)
        throw std::runtime_error(
            "exact Real model has no value for this uninterpreted-function "
            "application");
      return applicationValue(term);
    }
    case REAL_CONST:
    {
      // AST constants own values under the manager's independent budget.
      // Copy their decimal DTO outside our scope, then reconstruct under the
      // model budget; two arithmetic budgets are never active at once.
      const std::string numerator = term.GetRealNumerator();
      const std::string denominator = term.GetRealDenominator();
      NumberOperationScope operation(budget_);
      return ExactRational::fromCanonicalIntegers(numerator, denominator);
    }
    case REAL_ADD:
    {
      if (term.Degree() < 2)
        throw std::runtime_error("malformed Real addition in model query");
      ExactRational sum = [&]() {
        NumberOperationScope operation(budget_);
        return ExactRational(std::int64_t{0});
      }();
      for (const ASTNode& child : term.GetChildren())
      {
        ExactRational addend = evaluateTermInScope(child);
        NumberOperationScope operation(budget_);
        sum += addend;
      }
      return sum;
    }
    case REAL_SUB:
    {
      if (term.Degree() < 1)
        throw std::runtime_error("malformed Real subtraction in model query");
      ExactRational value = evaluateTermInScope(term[0]);
      if (term.Degree() == 1)
      {
        NumberOperationScope operation(budget_);
        return -value;
      }
      for (std::size_t i = 1; i < term.Degree(); ++i)
      {
        ExactRational subtrahend = evaluateTermInScope(term[i]);
        NumberOperationScope operation(budget_);
        value -= subtrahend;
      }
      return value;
    }
    case REAL_NEG:
      if (term.Degree() == 1)
      {
        ExactRational value = evaluateTermInScope(term[0]);
        NumberOperationScope operation(budget_);
        return -value;
      }
      throw std::runtime_error("malformed Real negation in model query");
    case REAL_MUL:
    {
      if (term.Degree() != 2)
        throw std::runtime_error("malformed Real multiplication in model query");
      const bool left_constant = term[0].GetKind() == REAL_CONST;
      const bool right_constant = term[1].GetKind() == REAL_CONST;
      if (left_constant == right_constant)
        throw std::runtime_error("nonlinear Real multiplication in model query");
      ExactRational left = evaluateTermInScope(term[0]);
      ExactRational right = evaluateTermInScope(term[1]);
      NumberOperationScope operation(budget_);
      return left * right;
    }
    case REAL_DIV:
    {
      if (term.Degree() != 2 || term[1].GetKind() != REAL_CONST)
        throw std::runtime_error("symbolic Real division in model query");
      ExactRational divisor = evaluateTermInScope(term[1]);
      const bool divisor_zero = [&]() {
        NumberOperationScope operation(budget_);
        return divisor.isZero();
      }();
      if (divisor_zero)
        throw std::runtime_error("zero Real divisor in model query");
      ExactRational dividend = evaluateTermInScope(term[0]);
      NumberOperationScope operation(budget_);
      return dividend / divisor;
    }
    case ITE:
    {
      /* The frontend names a Real ite and states what it stands for on each
       * branch, but the formula this model is checked against is the one the
       * caller submitted, which still holds the ite. So it has to be
       * evaluated here too, and it must agree with the naming -- that
       * agreement is exactly what the verification is for. */
      if (term.Degree() != 3)
        throw std::runtime_error("Real ite is not ternary in model query");
      return evaluateTermInScope(conditionValue(term[0]) ? term[1] : term[2]);
    }
    default:
      throw std::runtime_error("unsupported Real term in exact model query");
  }
}

/* The Boolean skeleton an ite condition is allowed to be. Anything else --
 * a bit-vector predicate, say -- has no meaning against a Real model, and
 * saying so is better than guessing. */
bool RealModel::conditionValue(const ASTNode& condition) const
{
  switch (condition.GetKind())
  {
    case TRUE: return true;
    case FALSE: return false;
    case NOT:
      if (condition.Degree() != 1)
        throw std::runtime_error("Real ite condition NOT is not unary");
      return !conditionValue(condition[0]);
    case AND:
      for (const ASTNode& child : condition.GetChildren())
        if (!conditionValue(child))
          return false;
      return true;
    case OR:
      for (const ASTNode& child : condition.GetChildren())
        if (conditionValue(child))
          return true;
      return false;
    case IFF:
    {
      if (condition.Degree() != 2)
        throw std::runtime_error("Real ite condition IFF is not binary");
      return conditionValue(condition[0]) == conditionValue(condition[1]);
    }
    case XOR:
    {
      bool value = false;
      for (const ASTNode& child : condition.GetChildren())
        value = value != conditionValue(child);
      return value;
    }
    case ITE:
    {
      if (condition.Degree() != 3)
        throw std::runtime_error("Boolean ite is not ternary");
      return conditionValue(condition[0]) ? conditionValue(condition[1])
                                          : conditionValue(condition[2]);
    }
    case SYMBOL:
      // A Boolean variable: only the oracle below can say.
      break;
    case REAL_LT:
    case REAL_LE:
    case REAL_GT:
    case REAL_GE:
      return predicateValue(condition);
    case EQ:
      if (condition.Degree() == 2 &&
          condition[0].GetSourceSort().kind() == SourceSort::Kind::Real &&
          condition[1].GetSourceSort().kind() == SourceSort::Kind::Real)
        return predicateValue(condition);
      break;
    default:
      break;
  }
  // Not part of the Real skeleton. If the verifier lent us somewhere to ask,
  // ask; otherwise this model genuinely cannot answer.
  if (condition_oracle_)
    return condition_oracle_(condition);
  throw std::runtime_error("unsupported Real ite condition in model query");
}

void RealModel::defineApplicationValues(const ASTNodeMap& handle_to_result)
{
  for (const std::pair<const ASTNode, ASTNode>& entry : handle_to_result)
  {
    const ASTNode& application = entry.first;
    const ASTNode& result_symbol = entry.second;
    if (application.IsNull() || result_symbol.IsNull() ||
        application.GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    // Already named, from an earlier publication in the same solve.
    if (findSymbol(application) != nullptr)
      continue;
    const ExactRational* value = findSymbol(result_symbol);
    // A result symbol the solve never valued is not an error here: the
    // application it stands for has no value to publish, and asking for one
    // then fails in evaluateTermUncached, where the caller can see it.
    if (value == nullptr)
      continue;
    NumberOperationScope operation(budget_);
    entries_.emplace_back(application, *value);
    indexLastEntry();
  }
  // An application that gained a value changes what a term over it evaluates
  // to, and the memo predates that.
  eval_cache_.clear();

  // Index them by congruence, so an application the solve never lowered can
  // be answered consistently with the ones it did. Built after every direct
  // value is in place, because a key holds the argument values and an
  // argument may itself be an application published above.
  //
  // With the congruence path closed for the duration: building a key
  // evaluates the arguments, and an argument may hold an application of its
  // own. Answering that one from a half-built index would let the order the
  // entries happen to be visited in decide the answer.
  const bool was_committed = committed_;
  committed_ = false;
  struct Restore
  {
    bool& flag;
    bool value;
    ~Restore() { flag = value; }
  } restore{committed_, was_committed};
  std::map<std::string, ExactRational> applications;
  for (const std::pair<const ASTNode, ASTNode>& entry : handle_to_result)
  {
    const ASTNode& application = entry.first;
    if (application.IsNull() || application.Degree() < 2 ||
        application.GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    const ExactRational* value = findSymbol(application);
    if (value == nullptr)
      continue;
    // Key evaluation can call either model, so it precedes the arithmetic
    // scope needed to copy and compare the exact result.
    std::string key = applicationKey(application);
    NumberOperationScope operation(budget_);
    const auto inserted = applications.emplace(std::move(key), *value);
    if (!inserted.second && inserted.first->second != *value)
      throw std::runtime_error(
          "congruent applications have different exact Real model values");
  }
  applications_.swap(applications);
}

bool RealModel::hasValue(const ASTNode& term) const noexcept
{
  try
  {
    (void)evaluateTermInScope(term);
    return true;
  }
  catch (...)
  {
    return false;
  }
}

std::string RealModel::smtlibValue(const ExactRational& value)
{
  const std::string numerator = value.numeratorDecimal();
  const std::string denominator = value.denominatorDecimal();
  const bool negative = !numerator.empty() && numerator.front() == '-';
  const std::string magnitude = negative ? numerator.substr(1) : numerator;
  if (denominator == "1")
    return negative ? "(- " + magnitude + ")" : magnitude;
  const std::string fraction = "(/ " + magnitude + " " + denominator + ")";
  return negative ? "(- " + fraction + ")" : fraction;
}

RealModelStrings RealModel::stringsFor(const ASTNode& term) const
{
  const ExactRational value = evaluateTermInScope(term);
  NumberOperationScope operation(budget_);
  const std::string numerator = value.numeratorDecimal();
  const std::string denominator = value.denominatorDecimal();
  if (denominator.empty() || denominator.front() == '-' || denominator == "0")
    throw std::runtime_error("exact Real model denominator is invalid");
  return RealModelStrings{value.canonicalFraction(), numerator, denominator,
                          smtlibValue(value)};
}

int RealModel::compareTerms(const ASTNode& left, const ASTNode& right) const
{
  const ExactRational left_value = evaluateTermInScope(left);
  const ExactRational right_value = evaluateTermInScope(right);
  NumberOperationScope operation(budget_);
  return left_value.compare(right_value);
}

bool RealModel::predicateValue(const ASTNode& predicate) const
{
  if (predicate.Degree() != 2)
    throw std::runtime_error("exact Real predicate is not binary");
  const Kind kind = predicate.GetKind();
  if (kind != REAL_LT && kind != REAL_LE && kind != REAL_GT &&
      kind != REAL_GE && kind != EQ)
    throw std::runtime_error("unsupported exact Real predicate kind");
  if (predicate[0].GetSourceSort().kind() != SourceSort::Kind::Real ||
      predicate[1].GetSourceSort().kind() != SourceSort::Kind::Real)
    throw std::runtime_error("exact Real predicate has a non-Real operand");

  const ExactRational left = evaluateTermInScope(predicate[0]);
  const ExactRational right = evaluateTermInScope(predicate[1]);
  NumberOperationScope operation(budget_);
  const int comparison = left.compare(right);
  switch (kind)
  {
    case REAL_LT: return comparison < 0;
    case REAL_LE: return comparison <= 0;
    case REAL_GT: return comparison > 0;
    case REAL_GE: return comparison >= 0;
    case EQ: return comparison == 0;
    default: break;
  }
  throw std::runtime_error("unreachable exact Real predicate kind");
}

void RealModel::printSmtlibDefinitions(
    std::ostream& out, const ASTVec& visible_symbols) const
{
  std::set<ASTNode, ExprLess> visible;
  for (const ASTNode& symbol : visible_symbols)
    if (realSymbol(symbol))
      visible.insert(symbol);

  for (const Entry& entry : entries_)
  {
    if (visible.find(entry.symbol) == visible.end())
      continue;
    out << "  (define-fun ";
    printer::SMTLIB2_Print1(out, entry.symbol, 0, false);
    NumberOperationScope operation(budget_);
    out << " () Real " << smtlibValue(entry.value) << ")\n";
  }
}

} // namespace stp::lra

namespace stp {

void STPMgr::InstallRealModel(lra::RealModel* model)
{
  if (model == nullptr)
    throw std::runtime_error("cannot install a null exact Real model");
  if (lra_ast_state == nullptr)
  {
    delete model;
    throw std::runtime_error("cannot install a Real model without LRA state");
  }
  delete lra_ast_state->real_model;
  lra_ast_state->real_model = model;
  // From here it is the answer, not a candidate.
  model->markCommitted();
}

void STPMgr::InvalidateRealModel() noexcept
{
  if (lra_ast_state == nullptr)
    return;
  delete lra_ast_state->real_model;
  lra_ast_state->real_model = nullptr;
}

bool STPMgr::HasRealModel() const noexcept
{
  return lra_ast_state != nullptr && lra_ast_state->real_model != nullptr;
}

void STPMgr::PublishRealApplicationValues(const ASTNodeMap& handle_to_result)
{
  if (!HasRealModel())
    return;
  lra_ast_state->real_model->defineApplicationValues(handle_to_result);
}

bool STPMgr::RealModelValueNode(const ASTNode& term, ASTNode& value)
{
  if (!HasRealModelValue(term))
    return false;
  try
  {
    value = CreateRealConst(GetRealModelNumerator(term),
                            GetRealModelDenominator(term));
    return true;
  }
  catch (const std::exception&)
  {
    return false;
  }
}

void STPMgr::SetRealConditionOracle(
    const std::function<bool(const ASTNode&)>& oracle)
{
  if (!HasRealModel())
    return;
  lra_ast_state->real_model->setConditionOracle(oracle);
}

void STPMgr::SetRealScalarKeyOracle(
    const std::function<std::string(const ASTNode&)>& oracle)
{
  if (!HasRealModel())
    return;
  lra_ast_state->real_model->setScalarKeyOracle(oracle);
}

bool STPMgr::EvaluateRealPredicate(
    const ASTNode& predicate, bool& value,
    const std::function<bool(const ASTNode&)>& condition_oracle) const noexcept
{
  if (!HasRealModel() || predicate.IsNull() || predicate.Degree() != 2)
    return false;
  const Kind kind = predicate.GetKind();
  if (kind != REAL_LT && kind != REAL_LE && kind != REAL_GT &&
      kind != REAL_GE && kind != EQ)
    return false;
  if (predicate[0].GetSourceSort().kind() != SourceSort::Kind::Real ||
      predicate[1].GetSourceSort().kind() != SourceSort::Kind::Real)
    return false;
  // Lent for this call and taken back after, so no oracle outlives the model
  // of Booleans it reads from. Installing one clears the model's memo, which
  // is why it is not installed unconditionally: a predicate with no ite in it
  // needs no oracle and should not pay for one.
  lra::RealModel& model = *lra_ast_state->real_model;
  // Only if the model has none already: one installed for the model's whole
  // life is the better answer, and taking it back at the end of this call
  // would be the wrong thing to do to it.
  const bool lend =
      static_cast<bool>(condition_oracle) && !model.hasConditionOracle();
  if (lend) model.setConditionOracle(condition_oracle);
  struct Restore
  {
    lra::RealModel& model;
    bool lend;
    ~Restore()
    {
      if (lend) model.setConditionOracle(lra::RealModel::ConditionOracle());
    }
  } restore{model, lend};
  try
  {
    value = model.predicateValue(predicate);
    return true;
  }
  catch (const std::exception&)
  {
    // A predicate over a term the model cannot reach -- an application the
    // solve never lowered, say. Not decided, and not this function's error
    // to raise.
    return false;
  }
}

bool STPMgr::HasRealModelValue(const ASTNode& term) const noexcept
{
  return HasRealModel() && lra_ast_state->real_model->hasValue(term);
}

std::string STPMgr::GetRealModelValue(const ASTNode& term) const
{
  if (!HasRealModel())
    throw std::runtime_error("no current exact Real model");
  return lra_ast_state->real_model->stringsFor(term).canonical_fraction;
}

std::string STPMgr::GetRealModelNumerator(const ASTNode& term) const
{
  if (!HasRealModel())
    throw std::runtime_error("no current exact Real model");
  return lra_ast_state->real_model->stringsFor(term).numerator_decimal;
}

std::string STPMgr::GetRealModelDenominator(const ASTNode& term) const
{
  if (!HasRealModel())
    throw std::runtime_error("no current exact Real model");
  return lra_ast_state->real_model->stringsFor(term).denominator_decimal;
}

std::string STPMgr::GetRealModelSMTLIB(const ASTNode& term) const
{
  if (!HasRealModel())
    throw std::runtime_error("no current exact Real model");
  return lra_ast_state->real_model->stringsFor(term).smtlib;
}

void STPMgr::PrintRealModelSMTLIB2(std::ostream& out,
                                   const ASTVec& visible_symbols) const
{
  if (!HasRealModel())
    throw std::runtime_error("no current exact Real model");
  lra_ast_state->real_model->printSmtlibDefinitions(out, visible_symbols);
}

ASTVec STPMgr::AllRealSymbols() const
{
  return lra_ast_state == nullptr ? ASTVec{} : lra_ast_state->real_symbols;
}

} // namespace stp

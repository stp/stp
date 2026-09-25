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
                     const ASTVec& required_symbols)
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
  for (const ASTNode& symbol : ordered)
  {
    const auto found = exact_text.find(symbol);
    ExactRational value = ExactRational(std::int64_t{0});
    if (found != exact_text.end())
      value = ExactRational::fromCanonicalIntegers(found->second.first,
                                                   found->second.second);
    if (!value.invariantHolds() || value.denominatorDecimal().empty() ||
        value.denominatorDecimal().front() == '-' ||
        value.denominatorDecimal() == "0")
      throw std::runtime_error("published Real model value is not canonical");
    entries_.emplace_back(symbol, std::move(value));
    indexLastEntry();
  }

}

void RealModel::indexLastEntry()
{
  // Positions are stable: entries_ is only ever appended to, never erased
  // from or reordered, so an index recorded here stays correct for the life
  // of the model. A duplicate symbol would silently shadow, so refuse it --
  // the constructor already rejects duplicate seeds.
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
    // A predicate over a term the model cannot reach. Not decided, and not
    // this function's error to raise.
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

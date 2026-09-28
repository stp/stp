#include "ASTRealConst.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <cassert>
#include <cstdint>
#include <limits>
#include <sstream>
#include <string>

namespace stp {

namespace {

lra::NumberLimits frontendNumberLimits()
{
  // These are the generous exact-rational limits: 64 KiBit operands
  // and results, 256 MiB live arithmetic allocation, and 16 MiB text. Later
  // resource plumbing may lower them per solve; it must never make them
  // unbounded or switch arithmetic representation.
  return lra::NumberLimits{UINT64_C(65536), UINT64_C(65536),
                           UINT64_C(268435456), UINT64_C(16777216)};
}

std::string smtlibReal(const lra::ExactRational& value)
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

std::string realOperatorSignature(Kind kind, const ASTVec& children)
{
  std::ostringstream out;
  out << _kind_names[kind] << '(';
  for (std::size_t i = 0; i < children.size(); ++i)
  {
    if (i != 0)
      out << ", ";
    out << children[i].GetSourceSort();
  }
  return out.str() + ')';
}

[[noreturn]] void invalidRealOperator(Kind kind, const ASTVec& children,
                                      const char* detail)
{
  const std::string diagnostic =
      "CreateRealTerm " + realOperatorSignature(kind, children) + ": " +
      detail;
  FatalError(diagnostic.c_str());
}

} // namespace

const ASTVec ASTRealConst::empty_children_;

ASTRealConst::ASTRealConst(STPMgr* manager,
                           const lra::ExactRational& value)
    : ASTInternal(manager, REAL_CONST), value_(value),
      stable_hash_(value_.stableHash())
{
}

ASTRealConst::ASTRealConst(const ASTRealConst& other)
    : ASTInternal(other.nodeManager, REAL_CONST), value_(other.value_),
      stable_hash_(other.stable_hash_)
{
}

void ASTRealConst::CleanUp()
{
  nodeManager->EraseRealConst(this);
  delete this;
}

void ASTRealConst::nodeprint(ostream& os, bool /*c_friendly*/)
{
  lra::NumberOperationScope operation(nodeManager->lra_ast_state->number_budget);
  os << smtlibReal(value_);
}

void ASTRealConst::setIndexWidth(uint32_t)
{
  FatalError("ASTRealConst has no array index width");
}

void ASTRealConst::setValueWidth(uint32_t)
{
  FatalError("ASTRealConst has no bit-vector width");
}

void ASTRealConst::setExpWidth(uint32_t)
{
  FatalError("ASTRealConst has no floating-point exponent width");
}

void ASTRealConst::setSigWidth(uint32_t)
{
  FatalError("ASTRealConst has no floating-point significand width");
}

std::string ASTRealConst::canonicalText() const
{
  lra::NumberOperationScope operation(
      nodeManager->lra_ast_state->number_budget);
  return value_.canonicalFraction();
}

std::string ASTRealConst::numeratorText() const
{
  lra::NumberOperationScope operation(
      nodeManager->lra_ast_state->number_budget);
  return value_.numeratorDecimal();
}

std::string ASTRealConst::denominatorText() const
{
  lra::NumberOperationScope operation(
      nodeManager->lra_ast_state->number_budget);
  return value_.denominatorDecimal();
}

std::size_t ASTRealConstHash::operator()(const ASTRealConst* value) const
{
  return static_cast<std::size_t>(value->stable_hash_) ^
         static_cast<std::size_t>(SourceSort::real().hash() *
                                  UINT64_C(0x9e3779b97f4a7c15));
}

bool ASTRealConstEqual::operator()(const ASTRealConst* lhs,
                                   const ASTRealConst* rhs) const
{
  return lhs->value_ == rhs->value_;
}

LraAstState::LraAstState() : number_budget(frontendNumberLimits()) {}

void STPMgr::RecordRealSymbol(const ASTNode& symbol)
{
  if (symbol.GetKind() != SYMBOL ||
      symbol.GetSourceSort().kind() != SourceSort::Kind::Real ||
      symbol.GetSTPMgr() != this)
    FatalError("RecordRealSymbol requires a manager-owned Real symbol");
  if (lra_ast_state == nullptr)
    lra_ast_state = new LraAstState();
  const auto inserted =
      lra_ast_state->real_symbol_ids.insert(symbol.GetNodeNum());
  if (!inserted.second)
    return;
  try
  {
    lra_ast_state->real_symbols.push_back(symbol);
  }
  catch (...)
  {
    // A failed vector growth must not make a retry look like a duplicate.
    lra_ast_state->real_symbol_ids.erase(inserted.first);
    throw;
  }
  InvalidateRealModel();
}

ASTRealConst* STPMgr::LookupOrCreateRealConst(ASTRealConst& value)
{
  assert(lra_ast_state != nullptr);
  const auto found = lra_ast_state->real_constants.find(&value);
  if (found != lra_ast_state->real_constants.end())
    return *found;

  ASTRealConst* copy = new ASTRealConst(value);
  try
  {
    lra_ast_state->real_constants.insert(copy);
  }
  catch (...)
  {
    delete copy;
    throw;
  }
  return copy;
}

void STPMgr::EraseRealConst(ASTRealConst* value)
{
  assert(lra_ast_state != nullptr);
  lra_ast_state->real_constants.erase(value);
}

ASTNode STPMgr::CreateRealConst(const std::string& decimal_or_fraction)
{
  if (lra_ast_state == nullptr)
    lra_ast_state = new LraAstState();

  lra::NumberOperationScope operation(lra_ast_state->number_budget);
  const lra::ExactRational value =
      lra::ExactRational::parseDecimalOrFraction(decimal_or_fraction);
  ASTRealConst key(this, value);
  ASTNode result(LookupOrCreateRealConst(key));
  noteReal();
  return result;
}

ASTNode STPMgr::CreateRealConst(const std::string& numerator,
                                const std::string& denominator)
{
  if (lra_ast_state == nullptr)
    lra_ast_state = new LraAstState();

  lra::NumberOperationScope operation(lra_ast_state->number_budget);
  const lra::ExactRational value =
      lra::ExactRational::fromCanonicalIntegers(numerator, denominator);
  ASTRealConst key(this, value);
  ASTNode result(LookupOrCreateRealConst(key));
  noteReal();
  return result;
}

ASTNode STPMgr::CreateRealTerm(Kind kind, const ASTVec& children)
{
  switch (kind)
  {
    case REAL_ADD:
    case REAL_SUB:
    case REAL_NEG:
    case REAL_MUL:
    case REAL_DIV:
    case ITE:
      break;
    default:
      FatalError("CreateRealTerm requires a Real arithmetic kind");
  }

  const std::size_t degree = children.size();
  const bool arity_ok =
      (kind == REAL_ADD && degree >= 2) ||
      (kind == REAL_SUB && degree >= 1) ||
      (kind == REAL_NEG && degree == 1) ||
      ((kind == REAL_MUL || kind == REAL_DIV) && degree == 2) ||
      (kind == ITE && degree == 3);
  if (!arity_ok)
    invalidRealOperator(kind, children, "invalid arithmetic arity");
  for (std::size_t index = 0; index != children.size(); ++index)
  {
    const ASTNode& child = children[index];
    if (child.GetSTPMgr() != this)
      invalidRealOperator(kind, children,
                          "every operand must belong to this manager");
    // An ite selects between two Real branches on a Boolean condition, so
    // its first operand is the one place a non-Real operand belongs.
    const bool condition_position = kind == ITE && index == 0;
    const SourceSort::Kind required =
        condition_position ? SourceSort::Kind::Bool : SourceSort::Kind::Real;
    if (child.GetSourceSort().kind() != required)
      invalidRealOperator(kind, children,
                          condition_position
                              ? "an ite condition must have Boolean sort"
                              : "every operand must have mathematical Real "
                                "sort");
  }
  /* Linearity is the requirement, so what has to be refused is a product of
   * two symbolic operands. A product of two constants is a constant and is
   * folded below; demanding *exactly* one constant refused that too, which
   * a let binding reaches easily -- (* ?a ?b) where both names are bound to
   * literals is how the termination-analysis families spell a scaled
   * coefficient. */
  if (kind == REAL_MUL && children[0].GetKind() != REAL_CONST &&
      children[1].GetKind() != REAL_CONST)
    invalidRealOperator(kind, children,
                        "multiplication requires an exact concrete "
                        "coefficient");
  if (kind == REAL_DIV && children[1].GetKind() != REAL_CONST)
    invalidRealOperator(kind, children,
                        "division requires an exact concrete divisor");
  if (kind == REAL_DIV && children[1].GetRealCanonical() == "0")
    invalidRealOperator(kind, children, "division by exact zero");

  if (lra_ast_state == nullptr)
    lra_ast_state = new LraAstState();

  // Fold concrete arithmetic after enforcing the fragment's structural
  // rules, multiplication included: two concrete operands make a concrete
  // product, and refusing it only pushed the same value into a shape the
  // normaliser would have to fold anyway.
  lra::NumberOperationScope operation(lra_ast_state->number_budget);
  const auto exact_value = [](const ASTNode& node)
      -> const lra::ExactRational& {
    if (node.GetKind() != REAL_CONST)
      FatalError("exact Real folding requires an exact Real constant");
    return static_cast<ASTRealConst*>(node._int_node_ptr)->value_;
  };
  const auto intern = [this](const lra::ExactRational& value) {
    ASTRealConst key(this, value);
    ASTNode result(LookupOrCreateRealConst(key));
    noteReal();
    return result;
  };
  bool all_constants = !children.empty() && kind != ITE;
  for (const ASTNode& child : children)
    all_constants = all_constants && child.GetKind() == REAL_CONST;

  if (all_constants)
  {
    lra::ExactRational value = exact_value(children.front());
    switch (kind)
    {
      case REAL_ADD:
        for (std::size_t i = 1; i < children.size(); ++i)
          value += exact_value(children[i]);
        break;
      case REAL_SUB:
        if (children.size() == 1)
          value.negate();
        else
          for (std::size_t i = 1; i < children.size(); ++i)
            value -= exact_value(children[i]);
        break;
      case REAL_NEG:
        value.negate();
        break;
      case REAL_MUL:
        value *= exact_value(children[1]);
        break;
      case REAL_DIV:
        value /= exact_value(children[1]);
        break;
      default:
        break;
    }
    return intern(value);
  }

  noteReal();
  return defaultNodeFactory->CreateNode(kind, children);
}

ASTNode STPMgr::CreateRealPredicate(Kind kind, const ASTNode& lhs,
                                    const ASTNode& rhs)
{
  switch (kind)
  {
    case REAL_LT:
    case REAL_LE:
    case REAL_GT:
    case REAL_GE:
    case EQ:
      break;
    default:
      FatalError("CreateRealPredicate requires a Real comparison kind");
  }
  if (lhs.GetSTPMgr() != this || rhs.GetSTPMgr() != this)
  {
    const ASTVec operands{lhs, rhs};
    invalidRealOperator(kind, operands,
                        "every operand must belong to this manager");
  }
  if (lhs.GetSourceSort().kind() != SourceSort::Kind::Real ||
      rhs.GetSourceSort().kind() != SourceSort::Kind::Real)
  {
    const ASTVec operands{lhs, rhs};
    const std::string diagnostic =
        "CreateRealPredicate " + realOperatorSignature(kind, operands) +
        ": both operands must have mathematical Real sort";
    FatalError(diagnostic.c_str());
  }
  noteReal();
  return defaultNodeFactory->CreateNode(kind, lhs, rhs);
}

void STPMgr::DestroyLraAstState()
{
  if (lra_ast_state == nullptr)
    return;
  // The check this used to make here now lives at the end of ~LraAstState,
  // which is the first moment it can be true: the state's own members --
  // the committed model, the atom registry and the frontend registry -- hold
  // ASTNode references to exact constants, and it is that destructor which
  // releases them. Asking before the delete asked one line too early, so a
  // constant the frontend registry was still holding read as one that had
  // outlived its references.
  delete lra_ast_state;
  lra_ast_state = nullptr;
}

std::string lra::detail::realCanonical(const ASTInternal* node)
{
  const ASTRealConst* value = static_cast<const ASTRealConst*>(node);
  return value->canonicalText();
}

std::string lra::detail::realNumerator(const ASTInternal* node)
{
  const ASTRealConst* value = static_cast<const ASTRealConst*>(node);
  return value->numeratorText();
}

std::string lra::detail::realDenominator(const ASTInternal* node)
{
  const ASTRealConst* value = static_cast<const ASTRealConst*>(node);
  return value->denominatorText();
}

} // namespace stp

#ifndef STP_LRA_AFFINE_NORMALIZATION_H
#define STP_LRA_AFFINE_NORMALIZATION_H

#include "LraFrontend.h"

#include <map>
#include <optional>
#include <unordered_map>
#include <vector>

namespace stp::lra {

struct AffinePolynomial final
{
  std::map<std::uint64_t, ExactRational> coefficients;
  ExactRational constant;
};

struct AffineNormalizationOptions final
{
  bool allow_applications = false;
};

/* Accumulate an affine expression over the AST DAG, not over its paths.
 * First validate it and find a postorder, resolving symbols on their first
 * left-to-right visit. Then send each node's accumulated scale to its
 * children in reverse postorder. Every parent contributes before a shared
 * child is evaluated, so t = (+ u u) visits u once and gives it twice t's
 * scale. Only one scalar per node is retained, rather than a potentially
 * growing polynomial for every intermediate sum.
 *
 * The frontend validates even subterms whose final scale cancels to zero.
 * Applications, when enabled, are opaque leaves.
 */
template <typename ResolveSymbol, typename Visit, typename Poll>
AffinePolynomial normalizeAffineDag(
    const ASTNode& root, const ExactRational& initial_scale,
    ResolveSymbol resolve_symbol, Visit visit, Poll& poll,
    AffineNormalizationOptions options = {})
{
  struct Node final
  {
    explicit Node(const ASTNode& value) : term(value) {}

    ASTNode term;
    std::size_t first_child = 0;
    std::size_t end_child = 0;
    std::uint64_t symbol = 0;
    // A constant's value, or the multiplier/divisor's exact scale.
    std::optional<ExactRational> factor;
    ExactRational scale;
  };
  struct Frame final
  {
    std::size_t index;
    std::size_t next_child;
  };
  std::vector<Node> nodes;
  std::unordered_map<std::uint64_t, std::size_t> indices;
  std::vector<Frame> pending;
  std::vector<std::size_t> postorder;
  const auto constant = [](const ASTNode& term) {
    return ExactRational::fromCanonicalIntegers(term.GetRealNumerator(),
                                               term.GetRealDenominator());
  };
  const auto open = [&](const ASTNode& term) {
    poll();
    visit(term);
    if (term.GetSourceSort().kind() != SourceSort::Kind::Real)
      throw FrontendFailure(
          FrontendFailureKind::WrongSort,
          std::string("linear normalization requires Real operands, got ") +
              term.GetSourceSort().name());
    Node node{term};
    const auto malformed = [](const char* message) {
      throw FrontendFailure(FrontendFailureKind::Malformed, message);
    };
    switch (term.GetKind())
    {
      case SYMBOL:
        node.symbol = resolve_symbol(term);
        break;
      case UF_APPLY:
        if (!options.allow_applications)
          throw FrontendFailure(FrontendFailureKind::Unsupported,
                                "unsupported Real operator UF_APPLY");
        node.symbol = resolve_symbol(term);
        break;
      case REAL_CONST:
        node.factor.emplace(constant(term));
        break;
      case REAL_ADD:
        if (term.Degree() < 2)
          malformed("real + requires at least two operands");
        node.end_child = term.Degree();
        break;
      case REAL_SUB:
        if (term.Degree() < 1)
          malformed("real - requires at least one operand");
        node.end_child = term.Degree();
        break;
      case REAL_NEG:
        if (term.Degree() != 1)
          malformed("real unary - requires one operand");
        node.end_child = 1;
        break;
      case REAL_MUL:
      {
        if (term.Degree() != 2)
          malformed("real * requires exactly two operands");
        const bool left_constant = term[0].GetKind() == REAL_CONST;
        const bool right_constant = term[1].GetKind() == REAL_CONST;
        if (left_constant == right_constant)
          throw FrontendFailure(
              FrontendFailureKind::Unsupported,
              "real * requires exactly one concrete exact rational operand");
        node.factor.emplace(constant(term[left_constant ? 0 : 1]));
        node.first_child = left_constant ? 1 : 0;
        node.end_child = node.first_child + 1;
        break;
      }
      case REAL_DIV:
        if (term.Degree() != 2)
          malformed("real / requires exactly two operands");
        if (term[1].GetKind() != REAL_CONST)
          throw FrontendFailure(
              FrontendFailureKind::Unsupported,
              "real / requires a concrete exact rational divisor");
        node.factor.emplace(constant(term[1]));
        if (node.factor->isZero())
          malformed("real / has an exact zero divisor");
        *node.factor = node.factor->inverse();
        node.end_child = 1;
        break;
      case ITE:
        throw FrontendFailure(
            FrontendFailureKind::Unsupported,
            "Real-term ite is outside the exact linear Real fragment");
      default:
        throw FrontendFailure(
            FrontendFailureKind::Unsupported,
            std::string("unsupported Real operator ") +
                _kind_names[term.GetKind()]);
    }
    const std::size_t index = nodes.size();
    const std::size_t first_child = node.first_child;
    nodes.push_back(std::move(node));
    indices.emplace(term.GetNodeNum(), index);
    pending.push_back(Frame{index, first_child});
  };

  open(root);
  while (!pending.empty())
  {
    poll();
    Frame& frame = pending.back();
    const Node& node = nodes[frame.index];
    if (frame.next_child < node.end_child)
    {
      const ASTNode child = node.term[frame.next_child++];
      if (indices.find(child.GetNodeNum()) == indices.end())
        open(child);
    }
    else
    {
      postorder.push_back(frame.index);
      pending.pop_back();
    }
  }

  AffinePolynomial result;
  nodes.front().scale = initial_scale;
  for (auto position = postorder.rbegin(); position != postorder.rend();
       ++position)
  {
    poll();
    const Node& node = nodes[*position];
    if (node.scale.isZero())
      continue;
    const Kind kind = node.term.GetKind();
    if (kind == SYMBOL || kind == UF_APPLY)
    {
      auto found = result.coefficients.find(node.symbol);
      if (found == result.coefficients.end())
        result.coefficients.emplace(node.symbol, node.scale);
      else
      {
        found->second += node.scale;
        if (found->second.isZero())
          result.coefficients.erase(found);
      }
    }
    else if (kind == REAL_CONST)
      result.constant += node.scale * *node.factor;
    else
      for (std::size_t child = node.first_child; child < node.end_child;
           ++child)
      {
        poll();
        ExactRational& scale =
            nodes[indices.at(node.term[child].GetNodeNum())].scale;
        if (kind == REAL_MUL || kind == REAL_DIV)
          scale += node.scale * *node.factor;
        else if (kind == REAL_NEG ||
                 (kind == REAL_SUB && (child != 0 || node.end_child == 1)))
          scale -= node.scale;
        else
          scale += node.scale;
      }
  }
  return result;
}

} // namespace stp::lra

#endif

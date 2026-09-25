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

#include "stp/FloatBlaster/FpAbstraction.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpAbstractionRules.h"
#include "stp/FloatBlaster/literal_fp.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/BVExactEncoder.h"
#include "stp/ToSat/ToSATBase.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <iostream>
#include <set>
#include <sstream>
#include <tuple>

namespace stp
{

bool parseFpAbstractionOps(const std::string& text, unsigned& mask)
{
  unsigned out = 0;
  std::string item;
  std::istringstream in(text);
  while (std::getline(in, item, ','))
  {
    item.erase(0, item.find_first_not_of(" \t"));
    item.erase(item.find_last_not_of(" \t") + 1);
    if (item.empty())
      continue;
    if (item == "mul")
      out |= FP_ABSTRACT_MUL;
    else if (item == "div")
      out |= FP_ABSTRACT_DIV;
    else if (item == "sqrt")
      out |= FP_ABSTRACT_SQRT;
    else if (item == "add")
      out |= FP_ABSTRACT_ADD;
    else if (item == "sub")
      out |= FP_ABSTRACT_SUB;
    else if (item == "fma")
      out |= FP_ABSTRACT_FMA;
    else if (item == "rem")
      out |= FP_ABSTRACT_REM;
    else if (item == "rti")
      out |= FP_ABSTRACT_RTI;
    else if (item == "to_sbv")
      out |= FP_ABSTRACT_TO_SBV;
    else if (item == "to_ubv")
      out |= FP_ABSTRACT_TO_UBV;
    else if (item == "default")
      out |= FP_ABSTRACT_DEFAULT;
    else if (item == "all")
      out |= FP_ABSTRACT_MUL | FP_ABSTRACT_DIV | FP_ABSTRACT_SQRT |
             FP_ABSTRACT_ADD | FP_ABSTRACT_SUB | FP_ABSTRACT_FMA |
             FP_ABSTRACT_REM | FP_ABSTRACT_RTI | FP_ABSTRACT_TO_SBV |
             FP_ABSTRACT_TO_UBV;
    else if (item == "none")
      out |= 0;
    else
      return false;
  }
  mask = out;
  return true;
}

class FpAbstraction::Impl
{
public:
  Impl(STPMgr* bm_, FpAbstraction& owner_, const std::set<ASTNode>& exact_)
      : bm(bm_), owner(owner_), encoder(new BVExactEncoder(bm_)), exact(exact_)
  {
  }

  STPMgr* bm;
  FpAbstraction& owner;
  std::unique_ptr<BVExactEncoder> encoder;
  std::set<ASTNode> exact; // applications a previous run released

  // Replacement state, per solve.
  ASTNodeMap rewritten;                 // node -> its rewritten form
  std::vector<ASTNode> definitions;     // proxy equalities and rules
  typedef std::tuple<Kind, unsigned, unsigned, uint64_t, uint64_t, uint64_t,
                     uint64_t>
      Key;
  std::map<Key, Application*> byKey;
  ASTNodeMap proxyOf;                   // child node -> its proxy symbol
  ASTNodeMap proxyDefOf;                // proxy symbol -> its definition
  std::map<ASTNode, Application*> bySurrogateView;
  std::map<ASTNode, Application*> bySurrogate;
  std::set<ASTNode> relationalEmitted; // monotonicity facts already asserted
  // ... of them, the ones the current check queued: a repaired candidate
  // drops its queue unasserted, and these must leave the set with it, or
  // the next candidate to violate one of them would find it "emitted" and
  // fall through to a value lemma.
  std::vector<ASTNode> relationalThisCheck;
  std::vector<Application*> pendingReleases;
  struct RefinementBudget
  {
    Application* app;
    unsigned values;
    unsigned shapes;
  };
  std::vector<RefinementBudget> budgetsThisCheck;
  bool budgetSpentBeforeCheck = false;
  // Each FMA/partner/role relationship is emitted once. A later piece can
  // introduce another partner, including a sum filling both factor roles.
  std::set<std::tuple<ASTNode, ASTNode, unsigned>> crossRuled;
  // Search advice for the next solve (--fp-abstraction-phase-hints): a
  // symbol and the value its bits should be tried at first.
  std::vector<std::pair<ASTNode, ASTNode>> hints;

  // ---------------------------------------------------------- selection
  static unsigned opBit(Kind k)
  {
    switch (k)
    {
      case FP_MUL:
        return FP_ABSTRACT_MUL;
      case FP_DIV:
        return FP_ABSTRACT_DIV;
      case FP_SQRT:
        return FP_ABSTRACT_SQRT;
      case FP_ADD:
        return FP_ABSTRACT_ADD;
      case FP_SUB:
        return FP_ABSTRACT_SUB;
      case FP_FMA:
        return FP_ABSTRACT_FMA;
      case FP_REM:
        return FP_ABSTRACT_REM;
      case FP_ROUNDTOINTEGRAL:
        return FP_ABSTRACT_RTI;
      case FP_TO_SBV:
        return FP_ABSTRACT_TO_SBV;
      case FP_TO_UBV:
        return FP_ABSTRACT_TO_UBV;
      default:
        return 0;
    }
  }

  // The conversions to a machine integer: (width, rm, x, unspecified) after
  // FpTotalise, a bit-vector result over one float operand.
  static bool conversionKind(Kind k) { return k == FP_TO_SBV || k == FP_TO_UBV; }

  // Whether an application could be abstracted at all: an abstractable
  // kind, at a format the rules cover and above the width floor, over
  // floats and modes. Which of these are abstracted is admitted() and
  // chained() below.
  bool admissible(const ASTNode& n) const
  {
    if (opBit(n.GetKind()) == 0)
      return false;
    if (conversionKind(n.GetKind()))
    {
      // The totalised form (width, rm, x, unspecified): the float operand
      // carries the format the rules read, and the width floor gates on
      // its packed width, which is what the exact circuit's size follows.
      if (n.Degree() != 4)
        return false;
      if (n[1].GetSourceSort().kind() != SourceSort::Kind::RoundingMode)
        return false;
      const SourceSort xs = n[2].GetSourceSort();
      if (xs.kind() != SourceSort::Kind::FloatingPoint)
        return false;
      const unsigned xeb = xs.exponentWidth();
      const unsigned xsb = xs.significandWidth();
      return xeb >= 2 && xsb >= 2 &&
             xeb + xsb >= bm->UserFlags.fp_abstraction_width && xeb <= 56 &&
             xsb <= 4096;
    }
    const SourceSort sort = n.GetSourceSort();
    if (sort.kind() != SourceSort::Kind::FloatingPoint)
      return false;
    const unsigned eb = sort.exponentWidth();
    const unsigned sb = sort.significandWidth();
    if (eb < 2 || sb < 2 || eb + sb < bm->UserFlags.fp_abstraction_width)
      return false;
    // The exponent arithmetic of the rules is host-width; formats past
    // this are lowered exactly, as they always were.
    if (eb > 56 || sb > 4096)
      return false;
    if (n.GetKind() == FP_REM && !FloatBlaster::remSupported(eb, sb))
      return false;
    // Every child a float or a mode (the totaliser has already run, so a
    // partial operation's extra child would be a bit-vector; none of the
    // admitted kinds is partial).
    for (size_t i = 0; i < n.Degree(); ++i)
    {
      const SourceSort cs = n[i].GetSourceSort();
      if (cs.kind() != SourceSort::Kind::FloatingPoint &&
          cs.kind() != SourceSort::Kind::RoundingMode)
        return false;
    }
    return true;
  }

  // The operations the query pins outright -- a direct equality between
  // an admissible operation and a constant or a conversion -- and the
  // budget clock (--fp-abstraction-budget), both batch-side concerns.
  std::set<ASTNode> pinned;
  // Applications left exact for a constant float operand, for the report,
  // and the policy that put them there (see UserDefinedFlags): resolved by
  // both entry points before anything is rewritten.
  mutable std::set<ASTNode> constantOperandDeclined;
  bool declineConstantOperands = false;
  bool budgetSpent = false;
  std::chrono::steady_clock::time_point budgetStart =
      std::chrono::steady_clock::now();

  // Collect `pinned` from the prepared formula: for every equality, an
  // admissible operand whose sibling is a constant or a conversion is the
  // witness-hunt signature: the solve must produce that operation's exact
  // value, and a surrogate only defers the circuit
  // through refinement rounds. Iterative: the formula may be deeper than
  // the stack.
  void collectPinned(const ASTNode& root)
  {
    std::set<ASTNode> seen;
    std::vector<ASTNode> stack(1, root);
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (n.Degree() == 0 || !seen.insert(n).second)
        continue;
      const Kind k = n.GetKind();
      if ((k == EQ || k == FP_SMT_EQ || k == FP_EQ) && n.Degree() == 2)
      {
        for (size_t i = 0; i < 2; ++i)
        {
          const ASTNode& op = n[i];
          const ASTNode& other = n[1 - i];
          const Kind ok = other.GetKind();
          if (admissible(op) &&
              (other.isConstant() || ok == FP_TOFP || ok == FP_TOFP_SIGNED ||
               ok == FP_TOFP_UNSIGNED || ok == FP_TO_UBV ||
               ok == FP_TO_SBV || ok == FP_TO_IEEE_BV))
            pinned.insert(op);
        }
      }
      for (size_t i = 0; i < n.Degree(); ++i)
        stack.push_back(n[i]);
    }
  }

  // Admitted outright: its kind is in --fp-abstraction-ops.
  // Declined for a constant float operand
  // (--fp-abstraction-constant-operands=0): the exact circuit of an
  // operation the blast knows an operand of is small and propagates, where
  // a record puts a free result under rules the solver has to search.
  // Policy rather than structure, so it sits here and not in admissible(),
  // whose answer the pinned analysis also asks for. Kept as the set of
  // declined applications: the report counts them, and one application can
  // be offered to both admission paths.
  // Whether this configuration's records would do anything a coefficient
  // does not: abstract an operation with two float operands the blast does
  // not know, or one whose operand is another abstracted operation. Either
  // is a sign that the query computes with its unknowns -- a product of two
  // of them, or a chain whose result feeds the next link and which the
  // order and band rules carry along. A query with neither is linear over
  // its coefficients: every abstracted operation would be one coefficient
  // times one unknown, standing alone, and a record there replaces a
  // shift-and-add the blast prunes to the constant's set bits, and the
  // solver propagates through, with a free result it has to search under.
  // Read off the prepared formula, once, over the kinds
  // --fp-abstraction-ops admits -- an operation this configuration is not
  // going to abstract neither chains nor searches.
  bool abstractsMoreThanCoefficients(const ASTNode& root) const
  {
    const auto abstracts = [&](const ASTNode& n) {
      return (bm->UserFlags.fp_abstraction_ops & opBit(n.GetKind())) != 0 &&
             admissible(n);
    };
    ASTNodeSet seen;
    std::vector<ASTNode> stack(1, root);
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (!seen.insert(n).second)
        continue;
      if (abstracts(n))
      {
        unsigned unknown = 0;
        for (size_t i = 0; i < n.Degree(); ++i)
        {
          const ASTNode& child = n[i];
          if (child.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
            continue;
          if (!child.isConstant())
            ++unknown;
          if (abstracts(child))
            return true; // a chain: this record's operand is another's result
        }
        if (unknown >= 2)
          return true;
      }
      for (const ASTNode& child : n.GetChildren())
        stack.push_back(child);
    }
    return false;
  }

  // --fp-abstraction-constant-operands for this solve, before rewriting.
  void resolveConstantOperandPolicy(const ASTNode& prepared)
  {
    typedef UserDefinedFlags::FpConstantOperandMode Mode;
    const Mode mode = bm->UserFlags.fp_abstraction_constant_operands;
    if (mode != Mode::AUTO)
    {
      declineConstantOperands = (mode == Mode::OFF);
      return;
    }
    declineConstantOperands = !abstractsMoreThanCoefficients(prepared);
    if (declineConstantOperands && bm->UserFlags.stats_flag)
      std::cerr << "FpAbstraction: nothing abstracted here computes with two "
                   "unknowns or with another record's result, so operations "
                   "with a constant operand are left exact "
                   "(--fp-abstraction-constant-operands auto)"
                << std::endl;
  }

  bool declinedForConstantOperand(const ASTNode& n) const
  {
    if (!declineConstantOperands)
      return false;
    for (size_t i = 0; i < n.Degree(); ++i)
      if (n[i].GetSourceSort().kind() == SourceSort::Kind::FloatingPoint &&
          n[i].isConstant())
      {
        constantOperandDeclined.insert(n);
        return true;
      }
    return false;
  }

  bool admitted(const ASTNode& n) const
  {
    return (bm->UserFlags.fp_abstraction_ops & opBit(n.GetKind())) != 0 &&
           admissible(n) && !declinedForConstantOperand(n);
  }

  // Admitted as a link in a chain: its kind is in
  // --fp-abstraction-chain-ops and one of its operands is the result of an
  // application already abstracted -- the children of `n` are the
  // rewritten ones, so such an operand stands here as a surrogate view.
  // Such an application is refined with the chain it is in and shares the
  // chain's rules. Bottom-up, this sees a chain only from its first
  // abstracted link upward: an accumulation over inputs that feeds an
  // abstracted operation at its top is not a chain to this rule, which is
  // why the fma is in the default set rather than here (UserDefinedFlags).
  bool chained(const ASTNode& n) const
  {
    if ((bm->UserFlags.fp_abstraction_chain_ops & opBit(n.GetKind())) == 0 ||
        !admissible(n) || declinedForConstantOperand(n))
      return false;
    for (size_t i = 0; i < n.Degree(); ++i)
      if (bySurrogateView.find(n[i]) != bySurrogateView.end())
        return true;
    return false;
  }

  static bool commutative(Kind k) { return k == FP_MUL || k == FP_ADD; }

  Key keyOf(const ASTNode& n) const
  {
    // A conversion's own sort is a machine integer with no format; key it
    // by its float operand's, beside the child ids (the width constant is
    // a child, so two widths never collide).
    const SourceSort sort = conversionKind(n.GetKind())
                                ? n[2].GetSourceSort()
                                : n.GetSourceSort();
    uint64_t ids[4] = {0, 0, 0, 0};
    for (size_t i = 0; i < n.Degree() && i < 4; ++i)
      ids[i] = n[i].GetNodeNum();
    // fp.mul and fp.add commute in their two float operands (children 1 and
    // 2); so does fp.fma in its product. Nothing else does.
    if (commutative(n.GetKind()) || n.GetKind() == FP_FMA)
      if (ids[1] > ids[2])
        std::swap(ids[1], ids[2]);
    return Key(n.GetKind(), sort.exponentWidth(), sort.significandWidth(),
               ids[0], ids[1], ids[2], ids[3]);
  }

  ASTNode viewOf(const ASTNode& bits, const SourceSort& sort) const
  {
    const unsigned eb = sort.exponentWidth();
    const unsigned sb = sort.significandWidth();
    const ASTNode raw = bm->CreateTerm(FP_TOFP, eb + sb, bm->CreateBVConst(32, eb),
                                       bm->CreateBVConst(32, sb), bits);
    return FloatBlaster::withFormat(bm, raw, eb, sb);
  }

  // The symbol standing for one child in every lemma, minting a proxy and
  // its definition on first sight.
  void proxyFor(const ASTNode& child, ASTNode& proxy, ASTNode& view)
  {
    if (child.isConstant())
    {
      proxy = child;
      view = child;
      return;
    }
    const std::map<ASTNode, Application*>::const_iterator inner =
        bySurrogateView.find(child);
    if (inner != bySurrogateView.end())
    {
      proxy = inner->second->surrogate;
      view = child;
      return;
    }
    const ASTNodeMap::const_iterator known = proxyOf.find(child);
    const SourceSort sort = child.GetSourceSort();
    if (known != proxyOf.end())
    {
      proxy = known->second;
      view = sort.kind() == SourceSort::Kind::FloatingPoint ? viewOf(proxy, sort)
                                                            : proxy;
      return;
    }
    if (sort.kind() == SourceSort::Kind::RoundingMode)
    {
      proxy = bm->CreateDeterministicSourceVariable(SourceSort::roundingMode(),
                                                    "fpar_rm", child);
      view = proxy;
      definitions.push_back(bm->CreateNode(EQ, proxy, child));
    }
    else if (sort.kind() == SourceSort::Kind::BitVector)
    {
      // A conversion's totalised unspecified value: a plain bit-vector
      // child (an array read under the driver); its definition rides the
      // record's defs like any proxy's.
      proxy = bm->CreateDeterministicSourceVariable(
          SourceSort::bitVector(child.GetValueWidth()), "fpar_u", child);
      view = proxy;
      definitions.push_back(bm->CreateNode(EQ, proxy, child));
    }
    else
    {
      assert(sort.kind() == SourceSort::Kind::FloatingPoint);
      proxy = bm->CreateDeterministicSourceVariable(
          SourceSort::bitVector(sort.packedWidth()), "fpar_p", child);
      view = viewOf(proxy, sort);
      // Bit-for-bit where the host demands it (useBitPreciseEqualities);
      // the packed child and the proxy are bit-vectors of one width.
      definitions.push_back(
          owner.bitPrecise_
              ? bm->CreateNode(EQ, proxy, child)
              : bm->CreateNode(FP_SMT_EQ, view, child));
    }
    proxyOf[child] = proxy;
    proxyDefOf[proxy] = definitions.back();
    owner.protected_.insert(proxy);
  }

  ASTNode record(const ASTNode& n, const ASTNode& source)
  {
    ++owner.stats_.candidates;
    const Key key = keyOf(n);
    const std::map<Key, Application*>::const_iterator found = byKey.find(key);
    if (found != byKey.end())
    {
      ++owner.stats_.shared;
      return found->second->surrogateView;
    }

    std::unique_ptr<Application> app(new Application());
    app->kind = n.GetKind();
    // A conversion's own sort is the machine integer; the format its rules
    // and proxies read is the float operand's.
    app->format = conversionKind(app->kind) ? n[2].GetSourceSort()
                                            : n.GetSourceSort();
    app->original = n;
    app->source = source;
    app->surrogate = bm->CreateDeterministicSourceVariable(
        SourceSort::bitVector(n.GetValueWidth()), "fpar_t", n);
    // A float result is replaced by the float view of its surrogate; a
    // bit-vector result by the surrogate itself.
    app->surrogateView = conversionKind(app->kind)
                             ? app->surrogate
                             : viewOf(app->surrogate, app->format);
    owner.protected_.insert(app->surrogate);

    for (size_t i = 0; i < n.Degree(); ++i)
    {
      ASTNode proxy, view;
      proxyFor(n[i], proxy, view);
      app->children.push_back(n[i]);
      app->proxies.push_back(proxy);
      app->proxyViews.push_back(view);
    }
    {
      // The mode sits first for the arithmetic, second for a conversion
      // (after the width constant).
      const size_t rmIdx = conversionKind(app->kind) ? 1 : 0;
      if (hasRoundingMode(app->kind) && n[rmIdx].GetKind() == BVCONST)
        app->roundingMode = (unsigned)n[rmIdx].GetUnsignedConst();
    }

    // The rules, over the proxies and the surrogate; captured on the
    // record as well, with its proxies' definitions, so every encoding
    // unit that mentions the record can carry them.
    {
      const size_t before = definitions.size();
      FpRuleContext context;
      fillRuleContext(*app, context);
      owner.stats_.ruleLemmas += emitFpAbstractionRules(
          context, bm->UserFlags.fp_abstraction_tiers, definitions);
      for (size_t di = before; di < definitions.size(); ++di)
        app->defs.push_back(definitions[di]);
      for (const ASTNode& proxy : app->proxies)
      {
        const ASTNodeMap::const_iterator pd = proxyDefOf.find(proxy);
        if (pd != proxyDefOf.end())
          app->defs.push_back(pd->second);
      }
    }

    Application* raw = app.get();
    owner.applications_.push_back(std::move(app));
    byKey[key] = raw;
    bySurrogateView[raw->surrogateView] = raw;
    bySurrogate[raw->surrogate] = raw;
    ++owner.stats_.abstracted;
    return raw->surrogateView;
  }

  static bool hasRoundingMode(Kind k) { return k != FP_REM; }

  // The record of kind `kind` over (mode, a, b) in this format, if one was
  // made; a and b in either order for the commutative kinds, as keyOf has
  // them.
  Application* find(Kind kind, const SourceSort& format, const ASTNode& mode,
                    const ASTNode& a, const ASTNode& b) const
  {
    uint64_t ids[4] = {mode.GetNodeNum(), a.GetNodeNum(), b.GetNodeNum(), 0};
    if ((commutative(kind) || kind == FP_FMA) && ids[1] > ids[2])
      std::swap(ids[1], ids[2]);
    const Key key(kind, format.exponentWidth(), format.significandWidth(),
                  ids[0], ids[1], ids[2], ids[3]);
    const std::map<Key, Application*>::const_iterator found = byKey.find(key);
    return found == byKey.end() ? NULL : found->second;
  }

  // Facts between records of different operations: a fused multiply-add
  // against the product of its factors and against the sum of a factor
  // with its addend, when those are records too. Revisit after new records
  // arrive: an FMA with no partner yet has emitted no relationship.
  void crossRules()
  {
    for (const std::unique_ptr<Application>& appPtr : owner.applications_)
    {
      Application& app = *appPtr;
      if (app.kind != FP_FMA)
        continue;
      const ASTNode &mode = app.children[0], &x = app.children[1],
                    &y = app.children[2], &z = app.children[3];
      Application* partners[] = {find(FP_MUL, app.format, mode, x, y),
                                 find(FP_ADD, app.format, mode, x, z),
                                 find(FP_ADD, app.format, mode, y, z)};
      FpRuleContext mine;
      fillRuleContext(app, mine);
      for (unsigned role = 0; role < 3; ++role)
      {
        Application* partner = partners[role];
        if (partner == NULL)
          continue;
        const auto key = std::make_tuple(app.surrogate, partner->surrogate, role);
        if (crossRuled.count(key) != 0)
          continue;
        FpRuleContext context;
        fillRuleContext(*partner, context);
        const size_t before = definitions.size();
        owner.stats_.crossRules += emitFpAbstractionCrossRules(
            mine, role == 0 ? &context : NULL, role == 1 ? &context : NULL,
            role == 2 ? &context : NULL, definitions);
        if (definitions.size() == before)
          continue;
        crossRuled.insert(key);
        for (size_t di = before; di < definitions.size(); ++di)
        {
          // Either participant's next encoding must carry the relationship,
          // including when only the newly created partner occurs in it.
          // abstractPiece follows both surrogates to collect their proxy
          // definitions transitively, even if the other piece was popped.
          app.defs.push_back(definitions[di]);
          partner->defs.push_back(definitions[di]);
        }
      }
    }
  }

  void fillRuleContext(const Application& app, FpRuleContext& c) const
  {
    c.bm = bm;
    c.kind = app.kind;
    c.eb = app.format.exponentWidth();
    c.sb = app.format.significandWidth();
    c.rm = app.roundingMode;
    if (conversionKind(app.kind))
    {
      // (width, rm, x, unspecified): the float operand alone is the rules'
      // operand; the target width and the totalised unspecified value
      // travel beside it.
      c.rmTerm = app.proxies[1];
      c.view.push_back(app.proxyViews[2]);
      c.bits.push_back(packedBitsOf(app.proxies[2], app.format));
      c.targetWidth = (unsigned)app.children[0].GetUnsignedConst();
      c.undefBits = app.proxies[3];
    }
    else
    {
      const size_t first = hasRoundingMode(app.kind) ? 1 : 0;
      if (hasRoundingMode(app.kind))
        c.rmTerm = app.proxies[0];
      for (size_t i = first; i < app.proxies.size(); ++i)
      {
        c.view.push_back(app.proxyViews[i]);
        c.bits.push_back(packedBitsOf(app.proxies[i], app.format));
      }
    }
    c.t = app.surrogateView;
    c.tb = app.surrogate;
    // The bands' precision, wider at wide formats: at binary128 a 16-bit
    // band is still a fraction of a percent of the exact multiplier, and
    // it is the difference between a candidate that needs its value and one
    // that does not on the deep satisfiable paths (docs/fp-abstraction.rst).
    c.bandBits = bm->UserFlags.fp_abstraction_significand_bits;
    if (app.format.packedWidth() >= 128 &&
        bm->UserFlags.fp_abstraction_significand_bits_wide > 0)
      c.bandBits = bm->UserFlags.fp_abstraction_significand_bits_wide;
  }

  // The packed bits a lemma reads a float symbol/constant through.
  ASTNode packedBitsOf(const ASTNode& proxy, const SourceSort& sort) const
  {
    if (proxy.GetKind() == SYMBOL)
      return proxy; // a bit-vector symbol already
    assert(proxy.isConstant());
    return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(proxy.GetBVConst()),
                             sort.packedWidth());
  }

  // ---------------------------------------------------------- rewriting
  // Bottom-up, memoised, iterative: the prepared formula may be deeper than
  // the stack.
  ASTNode rewrite(const ASTNode& root)
  {
    std::vector<std::pair<ASTNode, bool>> stack;
    stack.push_back(std::make_pair(root, false));
    while (!stack.empty())
    {
      const ASTNode n = stack.back().first;
      const bool expanded = stack.back().second;
      if (rewritten.find(n) != rewritten.end())
      {
        stack.pop_back();
        continue;
      }
      if (n.Degree() == 0)
      {
        rewritten[n] = n;
        stack.pop_back();
        continue;
      }
      if (!expanded)
      {
        stack.back().second = true;
        for (size_t i = 0; i < n.Degree(); ++i)
          if (rewritten.find(n[i]) == rewritten.end())
            stack.push_back(std::make_pair(n[i], false));
        continue;
      }
      stack.pop_back();
      ASTVec children;
      children.reserve(n.Degree());
      bool changed = false;
      for (size_t i = 0; i < n.Degree(); ++i)
      {
        const ASTNode c = rewritten[n[i]];
        changed = changed || c != n[i];
        children.push_back(c);
      }
      ASTNode out = changed ? rebuild(n, children) : n;
      if (!out.IsNull() && out.Degree() > 0 && exact.find(n) == exact.end() &&
          (pinned.empty() || pinned.find(n) == pinned.end()))
      {
        if (admitted(out))
          out = record(out, n);
        else if (chained(out))
        {
          const uint64_t before = owner.stats_.abstracted;
          out = record(out, n);
          if (owner.stats_.abstracted > before)
            ++owner.stats_.chained;
        }
      }
      rewritten[n] = out;
    }
    return rewritten[root];
  }

  ASTNode rebuild(const ASTNode& n, const ASTVec& children) const
  {
    // Batch rebuilds through the simplifying factory: whatever folds is
    // pure gain there, because the replay evaluates the ORIGINAL formula
    // and never needs the folded instances. A bit-precise host has no
    // replay of that kind; its model layer answers the raw stack's reads
    // from the rows of the instances the encoding actually met, so a
    // select or store instance folded away here is a cell no row will
    // ever pin -- the raw evaluation then completes it arbitrarily and
    // diverges from the encoding (a bogus published model, or a
    // self-check abort on a genuine one). Rebuild through the hashing
    // factory there: instance preservation is the contract.
    NodeFactory* nf =
        owner.bitPrecise_ ? bm->hashingNodeFactory : bm->defaultNodeFactory;
    ASTNode out;
    if (n.GetType() == BOOLEAN_TYPE)
      out = nf->CreateNode(n.GetKind(), children);
    else if (n.GetIndexWidth() > 0)
      out = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                n.GetValueWidth(), children);
    else
      out = nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
    // A float node rebuilt from children that carry no float sort (to_fp's
    // reinterpretation form) needs its format put back.
    if (n.GetType() == FLOATINGPOINT_TYPE &&
        out.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint &&
        !out.isConstant())
      out = FloatBlaster::withFormat(bm, out, n.GetExpWidth(), n.GetSigWidth());
    return out;
  }

  // ---------------------------------------------------------- checking
  ASTNode exactResult(const Application& app,
                      const std::vector<ASTNode>& values) const
  {
    ASTVec constants;
    for (size_t i = 0; i < app.children.size(); ++i)
      constants.push_back(
          bm->LiftSourceValue(values[i], app.children[i].GetSourceSort()));
    const ASTNode operation = bm->hashingNodeFactory->CreateTerm(
        app.kind, app.original.GetValueWidth(), constants);
    const ASTNode packed = literal_fp::tryEvaluateFpConstant(bm, operation);
    if (packed.IsNull())
      return packed;
    if (packed.GetKind() == BVCONST)
      return packed;
    // A float constant: its bits.
    return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(packed.GetBVConst()),
                             app.format.packedWidth());
  }

  // "bits is some NaN of the (eb, sb) format": exponent all ones, fraction
  // nonzero. The class is all that SMT-LIB equality sees of a NaN.
  ASTNode nanClass(const ASTNode& bits, unsigned eb, unsigned sb) const
  {
    const unsigned fw = sb - 1;
    const ASTNode E = bm->CreateTerm(BVEXTRACT, eb, bits,
                                     bm->CreateBVConst(32, eb + sb - 2),
                                     bm->CreateBVConst(32, fw));
    const ASTNode F = bm->CreateTerm(BVEXTRACT, fw, bits,
                                     bm->CreateBVConst(32, fw - 1),
                                     bm->CreateBVConst(32, 0));
    return bm->CreateNode(
        AND,
        bm->CreateNode(EQ, E, bm->CreateBVConst(eb, ((uint64_t)1 << eb) - 1)),
        bm->CreateNode(NOT, bm->CreateNode(EQ, F, bm->CreateZeroConst(fw))));
  }

  ASTNode valueLemma(const Application& app, const std::vector<ASTNode>& values,
                     const ASTNode& exact) const
  {
    ASTVec clause;
    for (size_t i = 0; i < app.proxies.size(); ++i)
    {
      if (app.proxies[i].isConstant())
        continue;
      // A float operand that is a NaN in the candidate is pinned by its
      // class under SMT-LIB equality: the proxy is defined equal to its
      // term under that equality, so its payload is free, and a bit-exact
      // antecedent would exclude one payload per instance while the exact
      // operation (and a totalised conversion, keyed on canonical bits)
      // gives the same result for every payload. A bit-precise host
      // defines its proxies bit-for-bit and keeps the bit-exact antecedent.
      const SourceSort cs = app.children[i].GetSourceSort();
      if (!owner.bitPrecise_ && cs.kind() == SourceSort::Kind::FloatingPoint)
      {
        const unsigned ceb = cs.exponentWidth(), csb = cs.significandWidth();
        if (decodeFpPackedValue(values[i], ceb, csb).cls == FpPackedValue::NaN)
        {
          clause.push_back(
              bm->CreateNode(NOT, nanClass(app.proxies[i], ceb, csb)));
          continue;
        }
      }
      clause.push_back(bm->CreateNode(
          NOT, bm->CreateNode(EQ, app.proxies[i], values[i])));
    }
    // A conversion's exact result is a machine integer: no NaN class to
    // widen over, plain equality is the whole lemma.
    if (conversionKind(app.kind))
    {
      clause.push_back(bm->CreateNode(EQ, app.surrogate, exact));
      return clause.size() == 1 ? clause[0] : bm->CreateNode(OR, clause);
    }
    const unsigned eb = app.format.exponentWidth();
    const unsigned sb = app.format.significandWidth();
    const FpPackedValue ev = decodeFpPackedValue(exact, eb, sb);
    if (ev.cls == FpPackedValue::NaN && !owner.bitPrecise_)
      clause.push_back(nanClass(app.surrogate, eb, sb));
    else
      clause.push_back(bm->CreateNode(EQ, app.surrogate, exact));
    return clause.size() == 1 ? clause[0] : bm->CreateNode(OR, clause);
  }

  // The value lemma widened to a box (--fp-abstraction-box-lemmas): every
  // operand tuple that agrees with the candidate's on the sign, the exponent
  // and the top k fraction bits gives a result that agrees with the exact
  // one on a prefix of its own. The whitelisted operations are monotone in
  // each operand on the accepted fixed-sign domains, so every result lies
  // between corner results. Packed values between two of one sign share
  // their common prefix. Pure bit-vector -- no float is unpacked, so it is
  // cheap to state beside the value lemma. The widest tried box whose
  // result prefix still pins the sign, the exponent and eight fraction bits
  // is stated; when none does, the box of one point is the value lemma.
  ASTNode boxLemma(const Application& app, const std::vector<ASTNode>& values,
                   const ASTNode& exact, bool& widened) const
  {
    widened = false;
    // Remainder is discontinuous when its nearest integer quotient changes;
    // corner results need not bound its interior. Conversions and future
    // kinds also require their own proof before they can use these boxes.
    switch (app.kind)
    {
      case FP_MUL:
      case FP_DIV:
      case FP_SQRT:
      case FP_ADD:
      case FP_SUB:
      case FP_FMA:
      case FP_ROUNDTOINTEGRAL:
        break;
      default:
        return valueLemma(app, values, exact);
    }
    const unsigned eb = app.format.exponentWidth();
    const unsigned sb = app.format.significandWidth();
    const unsigned w = eb + sb, fw = sb - 1;
    const size_t first = hasRoundingMode(app.kind) ? 1 : 0;
    if (decodeFpPackedValue(exact, eb, sb).cls != FpPackedValue::Normal &&
        decodeFpPackedValue(exact, eb, sb).cls != FpPackedValue::Subnormal)
      return valueLemma(app, values, exact);
    for (size_t i = first; i < values.size(); ++i)
    {
      const FpPackedValue::Class cls = decodeFpPackedValue(values[i], eb, sb).cls;
      if (cls != FpPackedValue::Normal && cls != FpPackedValue::Subnormal)
        return valueLemma(app, values, exact);
    }
    const unsigned widths[] = {8, 12, 16, 24, 32, 48, 64, 96};
    const unsigned minPrefix = 1 + eb + 8;
    for (unsigned k : widths)
    {
      if (k >= fw)
        break;
      // The corners: each operand with its low fraction bits cleared or set.
      std::vector<ASTNode> lo(values), hi(values);
      for (size_t i = first; i < values.size(); ++i)
      {
        CBV l = CONSTANTBV::BitVector_Clone(values[i].GetBVConst());
        CBV h = CONSTANTBV::BitVector_Clone(values[i].GetBVConst());
        for (unsigned j = 0; j + k < fw; ++j)
        {
          CONSTANTBV::BitVector_Bit_Off(l, j);
          CONSTANTBV::BitVector_Bit_On(h, j);
        }
        lo[i] = bm->CreateBVConst(l, w);
        hi[i] = bm->CreateBVConst(h, w);
      }
      // Clearing a subnormal's low fraction bits can introduce a zero
      // endpoint even though the candidate itself is nonzero. Division's
      // monotonicity requires the entire divisor interval to exclude zero.
      if (app.kind == FP_DIV &&
          decodeFpPackedValue(lo[2], eb, sb).cls == FpPackedValue::Zero)
        continue;
      const size_t n = values.size() - first;
      ASTNode least, greatest;
      bool ok = true;
      for (unsigned corner = 0; ok && corner < (1u << n); ++corner)
      {
        std::vector<ASTNode> at(values);
        for (size_t i = 0; i < n; ++i)
          at[first + i] = (corner >> i) & 1 ? hi[first + i] : lo[first + i];
        const ASTNode r = exactResult(app, at);
        if (r.IsNull())
        {
          ok = false;
          break;
        }
        const FpPackedValue::Class cls = decodeFpPackedValue(r, eb, sb).cls;
        if (cls != FpPackedValue::Normal && cls != FpPackedValue::Subnormal)
        {
          ok = false;
          break;
        }
        if (least.IsNull())
        {
          least = greatest = r;
          continue;
        }
        // All of one sign, or the prefix would be empty.
        if (CONSTANTBV::BitVector_bit_test(r.GetBVConst(), w - 1) !=
            CONSTANTBV::BitVector_bit_test(least.GetBVConst(), w - 1))
        {
          ok = false;
          break;
        }
        if (CONSTANTBV::BitVector_Lexicompare(r.GetBVConst(), least.GetBVConst()) < 0)
          least = r;
        if (CONSTANTBV::BitVector_Lexicompare(r.GetBVConst(), greatest.GetBVConst()) > 0)
          greatest = r;
      }
      if (!ok)
        continue;
      unsigned m = 0;
      while (m < w && CONSTANTBV::BitVector_bit_test(least.GetBVConst(), w - 1 - m) ==
                          CONSTANTBV::BitVector_bit_test(greatest.GetBVConst(), w - 1 - m))
        ++m;
      if (m < minPrefix)
        continue;
      ASTVec clause;
      const ASTNode hiIx = bm->CreateBVConst(32, w - 1);
      const ASTNode loIx = bm->CreateBVConst(32, fw - k);
      for (size_t i = 0; i < values.size(); ++i)
      {
        if (app.proxies[i].isConstant())
          continue;
        if (i < first)
        {
          clause.push_back(bm->CreateNode(
              NOT, bm->CreateNode(EQ, app.proxies[i], values[i])));
          continue;
        }
        clause.push_back(bm->CreateNode(
            NOT, bm->CreateNode(
                     EQ, bm->CreateTerm(BVEXTRACT, 1 + eb + k, app.proxies[i], hiIx, loIx),
                     bm->CreateTerm(BVEXTRACT, 1 + eb + k, values[i], hiIx, loIx))));
      }
      const ASTNode fromIx = bm->CreateBVConst(32, w - m);
      clause.push_back(bm->CreateNode(
          EQ, bm->CreateTerm(BVEXTRACT, m, app.surrogate, hiIx, fromIx),
          bm->CreateTerm(BVEXTRACT, m, least, hiIx, fromIx)));
      widened = true;
      return clause.size() == 1 ? clause[0] : bm->CreateNode(OR, clause);
    }
    return valueLemma(app, values, exact);
  }

  ASTNode releaseLemma(const Application& app) const
  {
    ASTVec children;
    for (size_t i = 0; i < app.proxyViews.size(); ++i)
      children.push_back(app.proxyViews[i]);
    const ASTNode exact = bm->hashingNodeFactory->CreateTerm(
        app.kind, app.original.GetValueWidth(), children);
    // A conversion's result is a machine integer: no float view to stamp,
    // no payload slack to quotient -- plain equality either way.
    if (conversionKind(app.kind))
      return bm->CreateNode(EQ, app.surrogate, exact);
    const ASTNode stamped = FloatBlaster::withFormat(
        bm, exact, app.format.exponentWidth(), app.format.significandWidth());
    // Bit-for-bit where the host demands it: the circuit's output is one
    // canonical bit pattern, so pinning the surrogate to it exactly is
    // the exact encoding.
    return owner.bitPrecise_
               ? bm->CreateNode(EQ, app.surrogate, stamped)
               : bm->CreateNode(FP_SMT_EQ, app.surrogateView, stamped);
  }

  // One record's candidate values and verdict, for a refinement round.
  struct Checked
  {
    Application* app;
    std::vector<ASTNode> values; // proxy values, mode included
    ASTNode candidate;           // the surrogate's value
    ASTNode exact;               // the operation's, or null
    bool consistent;
  };

  // The candidate's operand values with the mode left out: what the rule
  // context enumerates.
  static std::vector<ASTNode> operandValues(const Checked& c)
  {
    std::vector<ASTNode> out;
    const size_t first = hasRoundingMode(c.app->kind) ? 1 : 0;
    for (size_t i = first; i < c.values.size(); ++i)
      out.push_back(c.values[i]);
    return out;
  }

  // Monotonicity facts between this record and every other checked record
  // of the same operation, format and mode that the candidate violates.
  // Each is a universal fact and is emitted once; the set of them is
  // bounded by the pairs. Returns how many were queued.
  unsigned relationalLemmas(const Checked& self,
                            const std::vector<Checked>& all,
                            AbsRefine_CounterExample& model)
  {
    unsigned emitted = 0;
    FpRuleContext mine;
    fillRuleContext(*self.app, mine);
    const std::vector<ASTNode> myOperands = operandValues(self);
    for (const Checked& other : all)
    {
      if (other.app == self.app || other.app->released ||
          other.app->releasePending)
        continue;
      if (other.app->kind != self.app->kind ||
          !(other.app->format == self.app->format))
        continue;
      FpRuleContext theirs;
      fillRuleContext(*other.app, theirs);
      FpRuleId id;
      const ASTNode lemma = fpAbstractionRelationalLemma(
          mine, myOperands, self.candidate, theirs, operandValues(other),
          other.candidate, &id);
      if (lemma.IsNull() ||
          model.ModelValueOfFormula(lemma) != bm->ASTFalse ||
          !relationalEmitted.insert(lemma).second)
        continue;
      relationalThisCheck.push_back(lemma);
      owner.queueLemma(id, lemma);
      ++owner.stats_.relationalLemmas;
      ++emitted;
    }
    return emitted;
  }

  void refine(const Checked& checked, const std::vector<Checked>& all,
              AbsRefine_CounterExample& model)
  {
    Application& app = *checked.app;
    const UserDefinedFlags& flags = bm->UserFlags;
    if (flags.fp_abstraction_shape && app.shapeLemmas < 2)
    {
      FpRuleContext context;
      fillRuleContext(app, context);
      FpRuleId id;
      const ASTNode lemma = fpAbstractionShapeLemma(
          context, operandValues(checked), checked.candidate, &id);
      // Check the emitted predicate, not only the concrete decoder's
      // prediction: the two must agree even at wide internal bit widths.
      if (!lemma.IsNull() &&
          model.ModelValueOfFormula(lemma) == bm->ASTFalse)
      {
        ++app.shapeLemmas;
        ++owner.stats_.shapeLemmas;
        owner.queueLemma(id, lemma);
        return;
      }
    }
    // Relational facts before or after the value budget
    // (--fp-abstraction-relational-last). Before, they replace releases on
    // the witness hunts whose records share operands -- griggio's sin and
    // sqrt loops take 7 to 70 of them at binary32 and build no circuit --
    // and decide in one round the properties that relate two applications.
    // After, they are kept off a search that a few value lemmas and a
    // release would finish: at binary128 each monotonicity fact is a pair
    // of wide comparators, and eight of them in one round stalled the SAT
    // solver on six LAPACK triangular solves (timeouts against 3-9 s with
    // the facts held back). Neither order wins everywhere, so the width
    // decides: the SMT-LIB order below 128 bits, the late order from there.
    const unsigned lastWidth = flags.fp_abstraction_relational_last_width;
    const bool relationalFirst =
        flags.fp_abstraction_relational &&
        !(lastWidth > 0 && app.format.packedWidth() >= lastWidth);
    if (relationalFirst && relationalLemmas(checked, all, model) > 0)
      return;
    if (app.valueLemmas < flags.fp_abstraction_values)
    {
      const ASTNode lemma = valueLemma(app, checked.values, checked.exact);
      if (model.ModelValueOfFormula(lemma) != bm->ASTFalse)
      {
        // Unreachable while the model layer is consistent: the record was
        // judged inconsistent from the very proxy and surrogate values the
        // lemma pins, so the lemma is false under them. Reaching here means
        // the formula evaluation and the term evaluation disagree. A lemma
        // that would not cut must not spend the value budget; the exact
        // circuit is valid whatever the cause and keeps the round productive.
        release(app);
        return;
      }
      ++app.valueLemmas;
      ++owner.stats_.valueLemmas;
      // The value lemma pins this operand tuple's result; the box lemma
      // (--fp-abstraction-box-lemmas) adds what the tuples around it share.
      // Both, because the box pins a prefix and not the value: on its own it
      // let the same tuple come back with another result inside the prefix.
      owner.queueLemma(FpRuleId::REF_V1, lemma);
      if (flags.fp_abstraction_box_lemmas)
      {
        bool widened = false;
        const ASTNode box = boxLemma(app, checked.values, checked.exact, widened);
        if (widened)
        {
          ++owner.stats_.boxLemmas;
          owner.queueLemma(FpRuleId::REF_B1, box);
        }
      }
      return;
    }
    if (flags.fp_abstraction_relational && !relationalFirst &&
        relationalLemmas(checked, all, model) > 0)
      return;
    release(app);
  }

  // Whether a release of this record goes through a run of the pipeline
  // rather than a splice: the wide-significand operations at or above the
  // restart width, where the ordinary lowering's constant-bit propagation,
  // simplification and bit-vector abstraction have something to work on.
  bool releaseByRestart(const Application& app) const
  {
    const unsigned width = bm->UserFlags.fp_abstraction_restart_width;
    if (width == 0 || app.format.packedWidth() < width ||
        !owner.restartAllowed())
      return false;
    switch (app.kind)
    {
      case FP_MUL:
      case FP_DIV:
      case FP_SQRT:
      case FP_FMA:
      case FP_REM:
        return true;
      default:
        return false;
    }
  }

  void release(Application& app, bool allowRestart = true)
  {
    assert(!app.released && !app.releasePending);
    app.releasePending = true;
    pendingReleases.push_back(&app);
    ++owner.stats_.releases;
    if (allowRestart && releaseByRestart(app))
      owner.releaseRequests_.insert(app.source);
    else
      owner.queueLemma(FpRuleId::REF_E1, releaseLemma(app));
  }
};

FpAbstraction::FpAbstraction(STPMgr* bm, const std::set<ASTNode>& exact,
                             uint64_t restarts, size_t previouslyAbstracted)
    : impl_(new Impl(bm, *this, exact)), bm_(bm),
      previouslyAbstracted_(previouslyAbstracted)
{
  stats_.restarts = restarts;
  restartAllowed_ = restarts < bm->UserFlags.fp_abstraction_restart_limit;
}

FpAbstraction::~FpAbstraction()
{
}

ASTNode FpAbstraction::abstract(const ASTNode& prepared)
{
  if (active())
    FatalError("FpAbstraction::abstract called twice");
  if (bm_->UserFlags.fp_abstraction_decline_pinned)
  {
    impl_->collectPinned(prepared);
    if (!impl_->pinned.empty() && bm_->UserFlags.stats_flag)
      std::cerr << "FpAbstraction: " << impl_->pinned.size()
                << " pinned operation(s) left exact "
                   "(--fp-abstraction-decline-pinned)"
                << std::endl;
  }
  impl_->resolveConstantOperandPolicy(prepared);
  const ASTNode root = impl_->rewrite(prepared);
  if (!impl_->constantOperandDeclined.empty() && bm_->UserFlags.stats_flag)
    std::cerr << "FpAbstraction: " << impl_->constantOperandDeclined.size()
              << " operation(s) with a constant operand left exact "
                 "(--fp-abstraction-constant-operands)"
              << std::endl;
  if (!active())
    return prepared;
  // A restart that released applications and met none of them again --
  // this run abstracted no fewer than the last -- is not repeated.
  if (stats_.restarts > 0 && applications_.size() >= previouslyAbstracted_)
  {
    restartAllowed_ = false;
    if (bm_->UserFlags.stats_flag)
      std::cerr << "FpAbstraction: the restarted run abstracted "
                << applications_.size() << " application(s) against "
                << previouslyAbstracted_
                << " before it; further releases are spliced" << std::endl;
  }
  impl_->crossRules();
  ASTVec conjuncts;
  conjuncts.push_back(root);
  conjuncts.insert(conjuncts.end(), impl_->definitions.begin(),
                   impl_->definitions.end());
  impl_->definitions.clear();
  impl_->rewritten.clear();
  return bm_->CreateNode(AND, conjuncts);
}

ASTNode FpAbstraction::abstractPiece(const ASTNode& prepared,
                                     std::set<ASTNode>* closureSurrogates)
{
  // A piece is not the session, so the automatic policy has nothing to read
  // here and abstracts, as it does for a query that holds such a product.
  impl_->declineConstantOperands =
      bm_->UserFlags.fp_abstraction_constant_operands ==
      UserDefinedFlags::FpConstantOperandMode::OFF;
  const size_t before = applications_.size();
  const ASTNode root = impl_->rewrite(prepared);
  if (applications_.size() != before)
    impl_->crossRules();
  impl_->definitions.clear();
  if (root == prepared && impl_->bySurrogateView.empty())
    return root;
  // The definitions of EVERY record this piece mentions ride the piece,
  // not only the newly minted ones: records are shared by node across
  // pieces, the rewrite memo hands a later piece the surrogate view
  // without revisiting the record, and a definition that rode only the
  // minting unit dies with that unit -- retracted with an exact-stack
  // block, or left without variables by a backend rebuild -- leaving
  // live surrogates with no meaning at all, and a session-dependent
  // wrong model. Walking the rewritten piece for surrogate views and
  // conjoining their records' captured definitions makes every encoding
  // unit self-contained, which is what treating a popped unit's records
  // as dormant always assumed.
  // The collection is TRANSITIVE: a chained inner record's view is
  // swallowed by the outer record's replacement, and the inner is
  // reachable only through the outer's proxy -- the inner's bare
  // surrogate symbol -- or through views nested inside another record's
  // definitions. Missing the closure leaves the inner's child terms out
  // of every piece, which is precisely how a hundred reads vanished from
  // one session's encoding-side model coverage.
  std::set<ASTNode> defsSeen;
  std::set<const Application*> recordsSeen;
  ASTVec conjuncts;
  conjuncts.push_back(root);
  {
    ASTNodeSet walked;
    std::vector<ASTNode> stack(1, root);
    while (!stack.empty())
    {
      const ASTNode n = stack.back();
      stack.pop_back();
      if (!walked.insert(n).second)
        continue;
      const Application* rec = NULL;
      std::map<ASTNode, Application*>::const_iterator it =
          impl_->bySurrogateView.find(n);
      if (it != impl_->bySurrogateView.end())
        rec = it->second;
      else if (n.GetKind() == SYMBOL)
      {
        it = impl_->bySurrogate.find(n);
        if (it != impl_->bySurrogate.end())
          rec = it->second;
      }
      if (rec != NULL && recordsSeen.insert(rec).second)
      {
        for (const ASTNode& d : rec->defs)
          if (defsSeen.insert(d).second)
          {
            conjuncts.push_back(d);
            stack.push_back(d);
          }
        // The record's proxies link to inner records by bare surrogate.
        for (const ASTNode& p : rec->proxies)
          stack.push_back(p);
      }
      for (const ASTNode& child : n.GetChildren())
        stack.push_back(child);
    }
  }
  if (closureSurrogates != nullptr)
    for (const Application* rec : recordsSeen)
      closureSurrogates->insert(rec->surrogate);
  // The rewrite memo is kept across pieces: it is keyed by node, records
  // persist, and a level re-met after a pop lowers to the identical form.
  if (conjuncts.size() == 1)
    return root;
  return bm_->CreateNode(AND, conjuncts);
}

size_t FpAbstraction::releaseAllUnreleased()
{
  size_t queued = 0;
  for (const std::unique_ptr<Application>& app : applications_)
  {
    if (app->released || app->releasePending)
      continue;
    impl_->release(*app);
    ++queued;
  }
  // A release by restart has no meaning where this runs; the driver
  // forbids restarts, so every release above queued a splice.
  assert(releaseRequests_.empty());
  return queued;
}

void FpAbstraction::queueLemma(FpRuleId id, const ASTNode& lemma)
{
  assert(id != FpRuleId::None && id != FpRuleId::Count && !lemma.IsNull());
  pending_.push_back(lemma);
  pendingIds_.push_back(id);
}

void FpAbstraction::syncPermanentFacts(SATSolver& solver, ToSATBase* tosat)
{
  assert(permanentFacts_.size() == permanentIds_.size());
  if (factsAsserted_ >= permanentFacts_.size())
    return;
  if (tosat == NULL)
    FatalError("FP abstraction fact re-assertion began without a bit-blaster");
  const std::chrono::steady_clock::time_point started =
      std::chrono::steady_clock::now();
  for (; factsAsserted_ < permanentFacts_.size(); ++factsAsserted_)
  {
    const ASTNode lowered =
        FloatBlast::lowerOperation(bm_, permanentFacts_[factsAsserted_]);
    impl_->encoder->assertFormula(solver, *tosat, lowered);
  }
  stats_.lemmaSeconds +=
      std::chrono::duration<double>(std::chrono::steady_clock::now() - started)
          .count();
}

void FpAbstraction::beginQuery()
{
  for (const std::unique_ptr<Application>& app : applications_)
  {
    app->valueLemmas = 0;
    app->shapeLemmas = 0;
  }
}

FpAbstraction::Outcome
FpAbstraction::checkCandidate(AbsRefine_CounterExample& model)
{
  if (!active())
    return Outcome::Skipped;
  statsBeforeCheck_ = stats_;
  impl_->relationalThisCheck.clear();
  impl_->budgetsThisCheck.clear();
  impl_->budgetSpentBeforeCheck = impl_->budgetSpent;
  // The budget: past it, release every remaining record spliced in place
  // and let the exact circuits close the solve -- a loss on a witness
  // hunt is then bounded near the budget instead of the timeout. Batch
  // only (the incremental host sets bitPrecise_), and before the record
  // checks: reading a candidate this round is about to discard is waste.
  if (!bitPrecise_ && bm_->UserFlags.fp_abstraction_budget != 0 &&
      !impl_->budgetSpent &&
      std::chrono::steady_clock::now() - impl_->budgetStart >=
          std::chrono::seconds(bm_->UserFlags.fp_abstraction_budget))
  {
    impl_->budgetSpent = true;
    size_t released = 0;
    for (const std::unique_ptr<Application>& appPtr : applications_)
      if (!appPtr->released && !appPtr->releasePending)
      {
        impl_->release(*appPtr, false);
        ++released;
      }
    if (released > 0)
    {
      if (bm_->UserFlags.stats_flag)
        std::cerr << "FpAbstraction: budget of "
                  << bm_->UserFlags.fp_abstraction_budget
                  << " s spent; releasing " << released
                  << " remaining record(s) exactly, spliced in place"
                  << std::endl;
      return Outcome::Conflict;
    }
  }
  // First every record's verdict, then the refinements: a relational lemma
  // needs the candidate values of a record's bucket-mates, consistent or
  // not, so nothing is refined until everything has been read.
  std::vector<Impl::Checked> checked;
  for (const std::unique_ptr<Application>& appPtr : applications_)
  {
    Application& app = *appPtr;
    if (app.released || app.releasePending)
      continue;
    if (checkFilter_ && !checkFilter_(app.surrogate))
    {
      ++stats_.skippedChecks;
      continue;
    }
    if (activeClosureArmed_ &&
        activeClosure_.find(app.surrogate) == activeClosure_.end())
    {
      ++stats_.skippedChecks;
      ++stats_.inactiveSkips;
      continue;
    }
    ++stats_.checks;
    Impl::Checked c;
    c.app = &app;
    for (size_t i = 0; i < app.proxies.size(); ++i)
    {
      ASTNode v = model.ModelValueOfTerm(app.proxies[i]);
      if (v.GetKind() != BVCONST)
      {
        // A float or mode constant proxy answers as itself: its bits.
        if (v.isConstant())
          v = bm_->CreateBVConst(CONSTANTBV::BitVector_Clone(v.GetBVConst()),
                                 v.GetValueWidth());
        else
          FatalError("FPCHK: a proxy has no model value: ", app.proxies[i]);
      }
      c.values.push_back(v);
    }
    if (Impl::hasRoundingMode(app.kind))
    {
      // An active unit carries D_a, which binds the mode proxy to its mode
      // term: a constant, or a symbol the parser pinned to the five legal
      // encodings. A candidate that gives the proxy any other pattern can
      // only be reading a popped unit's unconstrained proxy, so the record
      // is outside the active closure and the acceptance argument does not
      // need its verdict; the evaluator, which has no meaning for such a
      // pattern, is not asked for one.
      const size_t rmIdx = Impl::conversionKind(app.kind) ? 1 : 0;
      const ASTNode& rmValue = c.values[rmIdx];
      if (rmValue.GetValueWidth() == 5 &&
          !symbolic_fp::isRoundingModeEncoding(
              (unsigned)rmValue.GetUnsignedConst()))
      {
        --stats_.checks; // read, not judged
        ++stats_.skippedChecks;
        ++stats_.invalidModeSkips;
        continue;
      }
    }
    c.candidate = model.ModelValueOfTerm(app.surrogate);
    if (c.candidate.GetKind() != BVCONST)
      FatalError("FPCHK: a surrogate has no model value: ", app.surrogate);
    c.exact = impl_->exactResult(app, c.values);
    c.consistent =
        !c.exact.IsNull() &&
        ((bitPrecise_ || Impl::conversionKind(app.kind))
             ? c.exact == c.candidate
             : fpPackedSmtEqual(c.exact, c.candidate,
                                app.format.exponentWidth(),
                                app.format.significandWidth()));
    checked.push_back(c);
  }
  for (const Impl::Checked& c : checked)
  {
    if (c.consistent)
      continue;
    ++stats_.inconsistent;
    impl_->budgetsThisCheck.push_back(
        {c.app, c.app->valueLemmas, c.app->shapeLemmas});
    if (c.exact.IsNull())
    {
      // No literal evaluator for this operation and format: the exact
      // encoding is the only refinement available.
      impl_->release(*c.app);
      continue;
    }
    if (bm_->UserFlags.fp_abstraction_phase_hints)
    {
      // Keep these operands, and take their exact result.
      for (size_t i = 0; i < c.app->proxies.size(); ++i)
        if (!c.app->proxies[i].isConstant())
          impl_->hints.push_back(std::make_pair(c.app->proxies[i], c.values[i]));
      impl_->hints.push_back(std::make_pair(c.app->surrogate, c.exact));
    }
    impl_->refine(c, checked, model);
  }
  if (restartRequested())
    return Outcome::Restart;
  return pending_.empty() ? Outcome::Consistent : Outcome::Conflict;
}

void FpAbstraction::acceptRepairedCandidate()
{
  // The lemmas the check queued are dropped unasserted, so they were not
  // spent; the checks and the disagreements happened.
  stats_.shapeLemmas = statsBeforeCheck_.shapeLemmas;
  stats_.valueLemmas = statsBeforeCheck_.valueLemmas;
  stats_.boxLemmas = statsBeforeCheck_.boxLemmas;
  stats_.relationalLemmas = statsBeforeCheck_.relationalLemmas;
  stats_.releases = statsBeforeCheck_.releases;
  ++stats_.repairs;
  pending_.clear();
  pendingIds_.clear();
  releaseRequests_.clear();
  // Dropping a queued release must leave the record abstract. In the
  // incremental host it survives this query and must be checked again.
  for (Application* app : impl_->pendingReleases)
    app->releasePending = false;
  impl_->pendingReleases.clear();
  for (const Impl::RefinementBudget& saved : impl_->budgetsThisCheck)
  {
    saved.app->valueLemmas = saved.values;
    saved.app->shapeLemmas = saved.shapes;
  }
  impl_->budgetsThisCheck.clear();
  impl_->budgetSpent = impl_->budgetSpentBeforeCheck;
  impl_->hints.clear();
  // The relational facts the queue held were never asserted: forget them,
  // so "emitted" keeps meaning "asserted".
  for (const ASTNode& lemma : impl_->relationalThisCheck)
    impl_->relationalEmitted.erase(lemma);
  impl_->relationalThisCheck.clear();
}

void FpAbstraction::encodePendingLemmas(SATSolver& solver, ToSATBase* tosat)
{
  assert(pending_.size() == pendingIds_.size());
  if (pending_.empty())
    return;
  assert(releaseRequests_.empty()); // A restart replaces this pipeline instead.
  if (tosat == NULL)
    FatalError("FP abstraction lemma encoding began without a bit-blaster");
  // Under the driver a lemma is also a permanent fact of the epoch, so it
  // joins the ledger a SAT-backend rebuild re-splices from; flush any
  // backlog such a rebuild left first, so the asserted prefix stays a
  // prefix. In batch the ledger is empty and this is a no-op.
  syncPermanentFacts(solver, tosat);
  ++stats_.rounds;
  const std::chrono::steady_clock::time_point started =
      std::chrono::steady_clock::now();
  for (size_t i = 0; i < pending_.size(); ++i)
  {
    const ASTNode& lemma = pending_[i];
    // Lower the floating-point predicates and operations the lemma
    // mentions (the exact release is the operation itself) to bits over the
    // proxies and the surrogate, then splice.
    const ASTNode lowered = FloatBlast::lowerOperation(bm_, lemma);
    impl_->encoder->assertFormula(solver, *tosat, lowered);
    permanentFacts_.push_back(lemma);
    permanentIds_.push_back(pendingIds_[i]);
    ++factsAsserted_;
  }
  pending_.clear();
  pendingIds_.clear();
  // All these equalities now belong to the permanent ledger. Only now
  // can future checks safely omit the corresponding applications.
  for (Application* app : impl_->pendingReleases)
  {
    app->releasePending = false;
    app->released = true;
  }
  impl_->pendingReleases.clear();
  impl_->budgetsThisCheck.clear();
  impl_->relationalThisCheck.clear();
  stats_.lemmaSeconds +=
      std::chrono::duration<double>(std::chrono::steady_clock::now() - started)
          .count();
  // The phase hints, for the symbols the solver carries.
  if (!impl_->hints.empty())
  {
    const ToSATBase::ASTNodeToSATVar& live = tosat->SATVar_to_SymbolIndexMap();
    for (const std::pair<ASTNode, ASTNode>& hint : impl_->hints)
    {
      const ToSATBase::ASTNodeToSATVar::const_iterator found =
          live.find(hint.first);
      if (found == live.end() || hint.second.GetKind() != BVCONST)
        continue;
      const std::vector<unsigned>& vars = found->second;
      const unsigned width =
          std::min<unsigned>(vars.size(), hint.second.GetValueWidth());
      for (unsigned i = 0; i < width; ++i)
        if (vars[i] != ~((unsigned)0))
          solver.suggestPhase(vars[i], CONSTANTBV::BitVector_bit_test(
                                           hint.second.GetBVConst(), i) != 0);
    }
    impl_->hints.clear();
  }
}

void FpAbstraction::reportStatistics(std::ostream& out) const
{
  out << "FpAbstraction: " << stats_.abstracted << " abstracted ("
      << stats_.shared << " shared occurrences, " << stats_.candidates
      << " candidates, " << stats_.chained << " by chain), "
      << stats_.ruleLemmas << " rule conjuncts, "
      << stats_.crossRules << " cross-operation rules, "
      << stats_.checks << " checks, " << stats_.skippedChecks << " skipped ("
      << stats_.inactiveSkips << " outside the active closure, "
      << stats_.invalidModeSkips << " with no mode encoding), "
      << stats_.inconsistent
      << " inconsistent, " << stats_.shapeLemmas << " shape lemmas, "
      << stats_.valueLemmas << " value lemmas, " << stats_.relationalLemmas
      << " relational lemmas, " << stats_.releases << " releases, "
      << stats_.rounds << " rounds, " << stats_.restarts << " restarts, "
      << stats_.repairs << " model repairs, " << stats_.boxLemmas
      << " box lemmas, " << stats_.lemmaSeconds << " s encoding lemmas"
      << std::endl;
  // The same records by operation, so a corpus can be read for what it
  // asks of each: how many records of the kind, how many were released
  // to their exact circuit, and how many shape and value lemmas they took.
  if (applications_.empty())
    return;
  struct PerKind
  {
    unsigned records = 0, released = 0, shape = 0, value = 0;
  };
  std::map<Kind, PerKind> byKind;
  for (const std::unique_ptr<Application>& app : applications_)
  {
    PerKind& k = byKind[app->kind];
    ++k.records;
    k.released += app->released ? 1 : 0;
    k.shape += app->shapeLemmas;
    k.value += app->valueLemmas;
  }
  out << "FpAbstraction by operation:";
  for (const std::pair<const Kind, PerKind>& entry : byKind)
  {
    const char* name = "?";
    switch (entry.first)
    {
      case FP_MUL: name = "mul"; break;
      case FP_DIV: name = "div"; break;
      case FP_SQRT: name = "sqrt"; break;
      case FP_ADD: name = "add"; break;
      case FP_SUB: name = "sub"; break;
      case FP_FMA: name = "fma"; break;
      case FP_REM: name = "rem"; break;
      case FP_ROUNDTOINTEGRAL: name = "rti"; break;
      case FP_TO_SBV: name = "to_sbv"; break;
      case FP_TO_UBV: name = "to_ubv"; break;
      default: break;
    }
    out << " " << name << " " << entry.second.records << " records ("
        << entry.second.released << " released, " << entry.second.shape
        << " shape lemmas, " << entry.second.value << " value lemmas)";
  }
  out << std::endl;
}

} // namespace stp

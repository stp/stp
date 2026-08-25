/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

#include "stp/FloatBlaster/FloatBlast.h"

#include "stp/FloatBlaster/FloatBlaster.h"

#include "stp/FloatBlaster/symbolic_fp.h"

#include <cassert>
#include <cstdint>
#include <limits>
#include <unordered_map>

namespace stp
{

class FloatBlast::Impl
{
public:
  explicit Impl(STPMgr* bm_)
      : bm(bm_), node_factory(bm_->defaultNodeFactory)
  {
  }

  ASTNode topLevel(const ASTNode& n)
  {
    if (bm->defaultNodeFactory != node_factory)
      FatalError("FloatBlast reused after the node factory changed");

    // SymFPU's STP backend is thread-local rather than object-local. Another
    // checker may have used this thread since our previous model query.
    symbolic_fp::init(bm);

    traversal_cache.clear();
    const ASTNode out = lower(n);
    traversal_cache.clear();
    return out;
  }

  const FloatBlast::Statistics& statistics() const noexcept { return stats; }

private:
  typedef std::unordered_map<ASTNode, std::unique_ptr<symbolic_fp::uf>,
                             ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
      UnpackedMap;

  // The native arithmetic circuits currently materialise IEEE biases and
  // exponent envelopes in `unsigned`, and their logarithmic-width helpers
  // use `1u << bit`. Keep every such value strictly below unsigned's sign
  // bit and every shift count within the host type. SMT-LIB admits wider
  // formats; those remain supported through the ordinary SymFPU lowering.
  static bool consumeNativeFpEnvelope(std::uintmax_t& remaining,
                                      std::uintmax_t amount)
  {
    if (amount >= remaining)
      return false;
    remaining -= amount;
    return true;
  }

  static bool nativeFpExponentIsSafe(unsigned eb)
  {
    const unsigned digits = std::numeric_limits<unsigned>::digits;
    return eb >= 2 && eb <= digits - 2;
  }

  static std::uintmax_t nativeFpBias(unsigned eb)
  {
    assert(nativeFpExponentIsSafe(eb));
    return (std::uintmax_t{1} << (eb - 1)) - 1;
  }

  static std::uintmax_t nativeFpEnvelopeLimit()
  {
    // 2^(digits - 1), without adding one to unsigned's maximum.
    return static_cast<std::uintmax_t>(std::numeric_limits<unsigned>::max() /
                                       2) +
           1;
  }

  static bool nativeFpArithmeticFormatIsSafe(const SourceSort& sort)
  {
    if (sort.kind() != SourceSort::Kind::FloatingPoint)
      return false;

    const unsigned eb = sort.exponentWidth();
    const unsigned sb = sort.significandWidth();
    if (sb < 2 || !nativeFpExponentIsSafe(eb))
      return false;

    // BBfpExpWidth must represent bias + 2*sb + 4 without reaching a
    // shift by numeric_limits<unsigned>::digits. This also bounds every
    // doubled width and logarithmic shift amount used by BBfpAdd/BBfpMul.
    std::uintmax_t remaining = nativeFpEnvelopeLimit();
    return consumeNativeFpEnvelope(remaining, nativeFpBias(eb)) &&
           consumeNativeFpEnvelope(remaining, sb) &&
           consumeNativeFpEnvelope(remaining, sb) &&
           consumeNativeFpEnvelope(remaining, 4);
  }

  static bool nativeFpToFpFormatsAreSafe(const SourceSort& source,
                                         const SourceSort& target)
  {
    if (source.kind() != SourceSort::Kind::FloatingPoint ||
        target.kind() != SourceSort::Kind::FloatingPoint)
      return false;

    const unsigned eb1 = source.exponentWidth();
    const unsigned sb1 = source.significandWidth();
    const unsigned eb2 = target.exponentWidth();
    const unsigned sb2 = target.significandWidth();
    if (sb1 < 2 || sb2 < 2 || !nativeFpExponentIsSafe(eb1) ||
        !nativeFpExponentIsSafe(eb2))
      return false;

    // BBfpToFp sizes its signed exponent for the complete source/target
    // envelope: bias1 + sb1 + bias2 + 2*sb2 + 4.
    std::uintmax_t remaining = nativeFpEnvelopeLimit();
    return consumeNativeFpEnvelope(remaining, nativeFpBias(eb1)) &&
           consumeNativeFpEnvelope(remaining, sb1) &&
           consumeNativeFpEnvelope(remaining, nativeFpBias(eb2)) &&
           consumeNativeFpEnvelope(remaining, sb2) &&
           consumeNativeFpEnvelope(remaining, sb2) &&
           consumeNativeFpEnvelope(remaining, 4);
  }

  symbolic_fp::floatingPointTypeInfo formatOf(const ASTNode& n) const
  {
    const SourceSort sort = n.GetSourceSort();
    if (sort.kind() != SourceSort::Kind::FloatingPoint)
      FatalError("FloatBlast expected a floating-point source expression: ",
                 n);

    const unsigned int exponent = sort.exponentWidth();
    const unsigned int significand = sort.significandWidth();
    return symbolic_fp::floatingPointTypeInfo(exponent, significand);
  }

  // fp.min, fp.max, fp.to_ubv and fp.to_sbv carry one more child after
  // FpTotalise has run -- the array read supplying their unspecified answer
  // -- and the operations cannot be lowered without it. BVTypeCheck
  // deliberately accepts both arities, so the requirement is not in the
  // node's type; it was an assert here, which under NDEBUG read past the end
  // of the children instead of saying so.
  void requireTotalised(const ASTNode& n, size_t expected) const
  {
    if (n.Degree() != expected)
      FatalError("FloatBlast: this partial floating-point operation has not "
                 "been totalised; FpTotalise has to run before it is "
                 "lowered: ",
                 n);
  }

  void requireSameFormat(const ASTNode& left, const ASTNode& right) const
  {
    if (left.GetSourceSort() != right.GetSourceSort())
      FatalError("FloatBlast received floating-point operands of different "
                 "source sorts");
  }

  // An array expression the array transform rewrites without losing element
  // formats: a declared array, or an if-then-else choosing among such
  // arrays (the transform pushes a read through the mux and abstracts each
  // arm to a format-stamped stand-in). A WRITE anywhere disqualifies it --
  // see the read arm of comparisonLeaf for why. A store chain answers false
  // at its outermost node, so this never walks one; only if-then-else
  // spines recurse.
  bool writesFreeArray(const ASTNode& n)
  {
    if (n.GetKind() == SYMBOL)
      return true;
    if (n.GetKind() == ITE && n.Degree() == 3)
      return writesFreeArray(n[1]) && writesFreeArray(n[2]);
    return false;
  }

  // A predicate operand that is (or resolves to) a packed view the lowering
  // leaves in the formula: a symbol or an interned constant, and structural
  // nodes built out of those. FP constant folding is deferred solver-wide,
  // so a literal usually arrives as to_fp's three-child reinterpret form
  // over constant bits; resolve it through the canonicalising funnel
  // (CreateFPConst), the same lookthrough RemoveUnconstrained's comparison
  // rule uses. Returns null for anything else -- in particular for FP
  // operations, whose values are cached unpacked and belong on the SymFPU
  // path.
  //
  // Everything returned here ends up as a child of a surviving predicate,
  // so it must be what lowering would have left in the formula anyway: each
  // case returns the node unchanged, or a node of the same kind whose
  // children are themselves resolved this way (or lowered, for the parts
  // that are not float-sorted).
  ASTNode comparisonLeaf(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return n;
    if (n.GetKind() == FP_TOFP && n.Degree() == 3 &&
        n[2].GetKind() == BVCONST)
    {
      const SourceSort sort = n.GetSourceSort();
      return bm->CreateFPConst(n[2], sort.exponentWidth(),
                               sort.significandWidth());
    }
    // fp.neg and fp.abs are sign-bit edits on the packed encoding (IEEE-754
    // 5.5.1 quiet operations: no rounding, NaN payload untouched), so either
    // wrapped around a packed view is still a packed view: resolve the
    // operand and keep the wrapper for the bit-blaster, whose FP_NEG/FP_ABS
    // arms negate or clear the top bit of the operand's bits. Rebuilding
    // through the factory matters when the operand resolved to something
    // new: a constant folds (foldFPSign), so the survivor functions'
    // constant rules see the folded form, and a collapsed mux re-enters the
    // involution rules (neg(neg x) = x).
    if (n.GetKind() == FP_NEG || n.GetKind() == FP_ABS)
    {
      const ASTNode inner = comparisonLeaf(n[0]);
      if (inner.IsNull())
        return ASTNode();
      if (inner == n[0])
        return n;
      return node_factory->CreateTerm(n.GetKind(), n.GetValueWidth(), inner);
    }
    // fp.mul and fp.add under --bb.fp-native-arith: the bit-blaster's
    // hand-written packed circuits (BBfpMul, BBfpAdd) take over from
    // SymFPU when both float operands resolve to packed views and the
    // rounding mode is immediate (a constant, or a declared symbol --
    // whose one-hot validity is asserted at declaration), and the format's
    // host-sized intermediate calculations are safe. Wider legal formats
    // fall back to SymFPU. The rebuild goes through the factory, so constant
    // operands fold (a fully constant operation never survives, keeping the
    // lowering-must-change invariant of constant folding and model
    // evaluation) and the identity rules still fire. fp.sub needs no arm:
    // the factory already lowers it to fp.add of the negation.
    if ((n.GetKind() == FP_MUL || n.GetKind() == FP_ADD) &&
        bm->UserFlags.fp_native_arith && n.Degree() == 3 &&
        (n[0].GetKind() == SYMBOL || n[0].GetKind() == BVCONST) &&
        nativeFpArithmeticFormatIsSafe(n.GetSourceSort()))
    {
      const ASTNode left = comparisonLeaf(n[1]);
      if (left.IsNull())
        return ASTNode();
      const ASTNode right = comparisonLeaf(n[2]);
      if (right.IsNull())
        return ASTNode();
      if (left == n[1] && right == n[2])
        return n;
      return node_factory->CreateTerm(n.GetKind(), n.GetValueWidth(), n[0],
                                      left, right);
    }
    // The float-to-float form of to_fp (four children: the two format
    // constants, the rounding mode, the float operand), under the same
    // flag: the bit-blaster re-rounds the packed source directly
    // (BBfpToFp). Unlike the arithmetic arms there is no factory fold for
    // a constant conversion, so a constant operand under a constant mode
    // must NOT survive -- constant folding and model evaluation rely on
    // the SymFPU lowering collapsing exactly that case.
    //
    // Targets with a 2-bit exponent stay on the SymFPU path: SymFPU's
    // convertFloatToFloat mis-rounds into such formats (e.g. converting
    // the (3, 4) value 3/32 to (2, 5) under RNE gives the odd neighbour
    // where IEEE ties-to-even picks 4/32; its own (2, 5) ADDITION is
    // clean, so this is specific to the conversion). The native circuit
    // rounds correctly there, but a circuit that disagrees with the
    // constant evaluator makes model validation reject its own models.
    // Until the evaluator side is fixed, the gate keeps the two aligned.
    if (n.GetKind() == FP_TOFP && bm->UserFlags.fp_native_arith &&
        n.Degree() == 4 &&
        (n[2].GetKind() == SYMBOL || n[2].GetKind() == BVCONST) &&
        n[0].GetUnsignedConst() >= 3 &&
        nativeFpToFpFormatsAreSafe(n[3].GetSourceSort(), n.GetSourceSort()))
    {
      const ASTNode operand = comparisonLeaf(n[3]);
      if (operand.IsNull())
        return ASTNode();
      if (operand.isConstant() && n[2].GetKind() == BVCONST)
        return ASTNode();
      if (operand == n[3])
        return n;
      ASTVec children;
      children.push_back(n[0]);
      children.push_back(n[1]);
      children.push_back(n[2]);
      children.push_back(operand);
      return node_factory->CreateTerm(FP_TOFP, n.GetValueWidth(), children);
    }
    // A select from a float-element array already IS the packed element
    // bits: asPacked's READ arm only rebuilds the array and index if they
    // contain FP work, so it never builds a circuit for the element itself
    // and the predicate can consume those bits directly. The element format
    // lives on the array node and the read derives it (deriveFPFormat), so
    // it survives the array transform's rewriting of this operand -- every
    // stand-in it mints for a read carries the format (ArrayTransformer),
    // which is what the bit-blaster reads back here.
    //
    // That survival argument holds only while the array expression is free
    // of writes (writesFreeArray): the transform turns those reads into
    // format-stamped stand-ins, or muxes over them. A read over a WRITE is
    // instead expanded into a mux over the stored values, and once every
    // leaf of that mux folds to a packed circuit -- the stored values were
    // lowered, and the residual read can fold into one of them -- no node
    // of the result carries the element format for the bit-blaster to read
    // back. So reads over writes take the SymFPU path, which decodes the
    // same carrier.
    if (n.GetKind() == READ)
    {
      if (!writesFreeArray(n[0]))
        return ASTNode();
      // asPacked rebuilds the read through the simplifying factory, so
      // keep only a result that still carries the float sort; anything
      // else sends the predicate to SymFPU.
      const ASTNode packed = asPacked(n);
      if (packed.GetSourceSort().kind() != SourceSort::Kind::FloatingPoint)
        return ASTNode();
      return packed;
    }
    // A float-sorted ITE is a mux over packed bits once its branches are
    // packed views, and the bit-blaster muxes them for free (BBITE) -- while
    // SymFPU's ITE arm unpacks BOTH branches and muxes the unpacked records.
    // The branches recurse through here rather than through asPacked,
    // because asPacked would happily build an encode() circuit for an
    // FP-operation branch, which is exactly the case that belongs on the
    // SymFPU path.
    if (n.GetKind() == ITE && n.Degree() == 3)
    {
      const ASTNode thenLeaf = comparisonLeaf(n[1]);
      if (thenLeaf.IsNull())
        return ASTNode();
      const ASTNode elseLeaf = comparisonLeaf(n[2]);
      if (elseLeaf.IsNull())
        return ASTNode();
      // The condition is Boolean, so lower() is the right treatment: any FP
      // work inside it is lowered (possibly into further surviving native
      // predicates) exactly as it would be anywhere else.
      const ASTNode cond = lower(n[0]);
      if (cond == n[0] && thenLeaf == n[1] && elseLeaf == n[2])
        return n;
      // Through the factory, so a folded condition collapses the mux to one
      // branch here rather than leaving a dead one under the predicate. The
      // constant rules in the two survivor functions run after this and
      // still see the collapsed operand.
      return node_factory->CreateTerm(ITE, n.GetValueWidth(), cond, thenLeaf,
                                      elseLeaf);
    }
    return ASTNode();
  }

  // The six binary comparison predicates over packed-view operands skip
  // SymFPU entirely: the source comparison survives to the bit-blaster,
  // which compares the packed IEEE bits directly (BBcompareFP, BBeqFP).
  // Returns the surviving node -- `n` itself, or the comparison rebuilt
  // over resolved operands, both purely float-sorted so no FP node is ever
  // built over packed carriers -- or null when the comparison has to take
  // the SymFPU path. (nativeClassificationSurvivor is the unary
  // sibling, for the classification predicates.)
  //
  // A comparison of two constants must not survive: constant folding and
  // model evaluation lower the node over its constant children and rely on
  // the result collapsing to TRUE/FALSE through the simplifying factory
  // (ComputeFormulaUsingModel asserts lowering changed the node).
  ASTNode nativeComparisonSurvivor(const ASTNode& n)
  {
    if (!bm->UserFlags.fp_native_cmp)
      return ASTNode();
    const ASTNode left = comparisonLeaf(n[0]);
    if (left.IsNull())
      return ASTNode();
    const ASTNode right = comparisonLeaf(n[1]);
    if (right.IsNull())
      return ASTNode();
    if (left.isConstant() && right.isConstant())
      return ASTNode();
    if (left == n[0] && right == n[1])
      return n;
    // The rebuild goes through the simplifying factory, which may fold the
    // comparison into something the bit-blaster has no native arm for (it
    // already turns fp.geq(x,x) into not(fp.isNaN(x))). Anything but a
    // natively blasted comparison goes back to SymFPU.
    const ASTNode rebuilt = node_factory->CreateNode(n.GetKind(), left, right);
    if (!isNativelyBlasted(rebuilt.GetKind()))
      return ASTNode();
    return rebuilt;
  }

  // Unary sibling of nativeComparisonSurvivor for the classification
  // predicates, which the bit-blaster reads straight off the packed fields
  // (BBclassifyFP). Same three conditions, with the constant rule tightened:
  // for a unary predicate a constant operand means the whole node is
  // constant, and an all-constant node has to lower so that constant
  // folding and model evaluation see it collapse.
  ASTNode nativeClassificationSurvivor(const ASTNode& n)
  {
    if (!bm->UserFlags.fp_native_cmp)
      return ASTNode();
    const ASTNode leaf = comparisonLeaf(n[0]);
    if (leaf.IsNull() || leaf.isConstant())
      return ASTNode();
    if (leaf == n[0])
      return n;
    const ASTNode rebuilt = node_factory->CreateNode(n.GetKind(), leaf);
    if (!isNativelyBlasted(rebuilt.GetKind()))
      return ASTNode();
    return rebuilt;
  }

  static bool isNativelyBlasted(Kind k)
  {
    return k == FP_GT || k == FP_LT || k == FP_GEQ || k == FP_LEQ ||
           k == FP_EQ || k == FP_SMT_EQ || k == FP_ISNORMAL ||
           k == FP_ISSUBNORMAL || k == FP_ISZERO || k == FP_ISINFINITE ||
           k == FP_ISNAN || k == FP_ISNEGATIVE || k == FP_ISPOSITIVE;
  }

  ASTNode rebuild(const ASTNode& n, const ASTVec& children)
  {
    // Nothing rebuilds a UF application: every path that could reach one
    // returns it untouched (see lower). Substituting here would hand the
    // node factory an application whose actual sorts no longer match its
    // declaration, and the factory's job is to refuse that.
    assert(n.GetKind() != UF_APPLY);

    if (n.GetType() == BOOLEAN_TYPE)
      return node_factory->CreateNode(n.GetKind(), children);

    if (n.GetIndexWidth() > 0)
      return node_factory->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                           n.GetValueWidth(), children);

    return node_factory->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
  }

  // Target-language view. Source FP values are packed only if their caller
  // genuinely needs an AST carrier; FP predicates and conversions bypass
  // this function and consume the unpacked view directly.
  ASTNode lower(const ASTNode& n)
  {
    // A UF application is opaque to this pass, whatever its codomain. Its
    // actuals are stated in source sorts and the UF layer both validates and
    // compares them there, so lowering one underneath the application
    // changes what the application denotes -- when it is admitted at all;
    // an application of f to a float that arrives as the bits the float
    // lowered to is exactly what the declaration check refuses.
    //
    // There is nothing to lower in return for that. The application already
    // is the bits of its result: UFContext::apply builds it at the
    // codomain's packed width, and its actuals are resolved at their source
    // sorts by whoever consumes the application -- the UF lowering pass
    // before a solve, the model evaluator's UF_APPLY arm after one.
    if (n.GetKind() == UF_APPLY)
      return n;

    if (n.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint)
      return asPacked(n);

    if (n.Degree() == 0)
      return n;

    const ASTNodeMap::const_iterator persistent = terminal_cache.find(n);
    if (persistent != terminal_cache.end())
      return persistent->second;

    const ASTNodeMap::const_iterator current = traversal_cache.find(n);
    if (current != traversal_cache.end())
      return current->second;

    ASTNode out;
    if (is_FP_kind(n.GetKind()))
    {
      out = lowerFpTerminal(n);
      terminal_cache[n] = out;
    }
    else
    {
      ASTVec children;
      children.reserve(n.Degree());
      bool changed = false;
      for (size_t i = 0; i < n.Degree(); ++i)
      {
        const ASTNode child = lower(n[i]);
        changed = changed || child != n[i];
        children.push_back(child);
      }
      out = changed ? rebuild(n, children) : n;
    }

    traversal_cache[n] = out;
    return out;
  }

  // One branch of a float-valued mux, as packed bits. A branch that names
  // the float sort has a packed view; one that does not is the packed
  // circuit lowering already built for it (deriveSourceSort's ITE rule is
  // what admits the mix, and it checks the widths agree), so it IS its
  // packed bits and lowers as the bitvector it is.
  ASTNode packedBranch(const ASTNode& n)
  {
    if (n.GetSourceSort().kind() == SourceSort::Kind::FloatingPoint)
      return asPacked(n);
    return lower(n);
  }

  // Ordinary packed view. Leaves and structural carrier nodes already are
  // the bits that store the source value, so preserve them (and any NaN
  // payload they happen to contain). A genuine FP operation has no such
  // target representation and is encoded lazily from its cached UF.
  ASTNode asPacked(const ASTNode& n)
  {
    const ASTNodeMap::const_iterator cached = packed_cache.find(n);
    if (cached != packed_cache.end())
      return cached->second;

    (void)formatOf(n); // exact source-sort/format validation at the boundary

    ASTNode out;
    if (n.Degree() == 0)
    {
      out = n;
    }
    else if (n.GetKind() == UF_APPLY)
    {
      // Opaque carrier, like a leaf: the application's own bits are the
      // packed value of its result, and nothing under it is lowered
      // (lower). Deliberately not canonicalised -- the payload of a NaN the
      // solve chose for an application is its payload, exactly as for a
      // float symbol; canonicalPacked is where a caller that needs the
      // quotient asks for it.
      out = n;
    }
    else if (n.GetKind() == READ)
    {
      ASTVec children;
      children.reserve(n.Degree());
      bool changed = false;
      for (size_t i = 0; i < n.Degree(); ++i)
      {
        const ASTNode child = lower(n[i]);
        changed = changed || child != n[i];
        children.push_back(child);
      }
      out = changed ? rebuild(n, children) : n;
    }
    else if (n.GetKind() == ITE)
    {
      assert(n.Degree() == 3);
      // The array transform can leave a float-valued mux holding one branch
      // as its packed circuit -- a plain bitvector of the float's packed
      // width (see deriveSourceSort's ITE rule). Such a branch already is
      // its packed bits: lower it as the bitvector it is rather than
      // asserting a float sort onto it (packedBranch).
      ASTVec children;
      children.reserve(3);
      children.push_back(lower(n[0]));
      children.push_back(packedBranch(n[1]));
      children.push_back(packedBranch(n[2]));
      out = (children[0] == n[0] && children[1] == n[1] &&
             children[2] == n[2])
                ? n
                : rebuild(n, children);
    }
    else if (!is_FP_kind(n.GetKind()))
    {
      // Compatibility for legacy carrier expressions which were explicitly
      // declared/stamped as FP. Rebuild their carrier children first, then
      // leave the operation itself in the target language.
      ASTVec children;
      children.reserve(n.Degree());
      bool changed = false;
      for (size_t i = 0; i < n.Degree(); ++i)
      {
        const ASTNode child = lower(n[i]);
        changed = changed || child != n[i];
        children.push_back(child);
      }
      out = changed ? rebuild(n, children) : n;
    }
    else
    {
      const ASTNodeMap::const_iterator canonical = canonical_packed_cache.find(n);
      if (canonical != canonical_packed_cache.end())
        out = canonical->second;
      else
      {
        out = symbolic_fp::unpacked::encode(formatOf(n), asUnpacked(n));
        ++stats.pack_builds;
        canonical_packed_cache[n] = out;
      }
    }

    packed_cache[n] = out;
    return out;
  }

  // Canonical packed view. This is deliberately distinct from asPacked:
  // SMT FP equality identifies all NaNs, so semantic quotient boundaries
  // (FP_TO_IEEE_BV and totalisation/array indexes) must collapse payloads.
  ASTNode canonicalPacked(const ASTNode& n)
  {
    const ASTNodeMap::const_iterator cached = canonical_packed_cache.find(n);
    if (cached != canonical_packed_cache.end())
      return cached->second;

    const ASTNode out =
        symbolic_fp::unpacked::encode(formatOf(n), asUnpacked(n));
    ++stats.pack_builds;
    canonical_packed_cache[n] = out;

    // A real FP operation's ordinary packed representation is the same
    // SymFPU encoding. Raw leaves/READs/ITEs intentionally remain distinct.
    if (is_FP_kind(n.GetKind()))
      packed_cache[n] = out;
    return out;
  }

  const symbolic_fp::uf& remember(const ASTNode& n,
                                   std::unique_ptr<symbolic_fp::uf> value)
  {
    const std::pair<UnpackedMap::iterator, bool> inserted =
        unpacked_cache.emplace(n, std::move(value));
    assert(inserted.second);
    return *inserted.first->second;
  }

  const symbolic_fp::uf& decodeCarrier(const ASTNode& n,
                                        const ASTNode& carrier)
  {
    ++stats.unpack_builds;
    return remember(n, std::unique_ptr<symbolic_fp::uf>(
                           new symbolic_fp::uf(symbolic_fp::unpacked::decode(
                               formatOf(n), carrier))));
  }

  // Unpacked source view. Every entry is either one actual decode of an
  // opaque carrier or the final (already rounded) result of exactly one
  // source FP operation. References remain stable because values are owned
  // separately from the hash table's buckets.
  const symbolic_fp::uf& asUnpacked(const ASTNode& n)
  {
    const UnpackedMap::const_iterator cached = unpacked_cache.find(n);
    if (cached != unpacked_cache.end())
    {
      ++stats.unpacked_cache_hits;
      return *cached->second;
    }

    const symbolic_fp::floatingPointTypeInfo result_format = formatOf(n);
    const Kind kind = n.GetKind();

    if (n.Degree() == 0)
      return decodeCarrier(n, n);

    if (kind == UF_APPLY)
    {
      // An opaque packed cell whose subterms stay as they are: unlike a
      // READ, an application's children are its declaration identity and
      // its actuals, and neither may be rewritten into the target language
      // (lower).
      packed_cache[n] = n;
      return decodeCarrier(n, n);
    }

    if (kind == READ)
    {
      // Break the asPacked/asUnpacked recursion explicitly: a READ is an
      // opaque packed cell, but its array and index may still need lowering.
      ASTVec children;
      children.reserve(n.Degree());
      bool changed = false;
      for (size_t i = 0; i < n.Degree(); ++i)
      {
        const ASTNode child = lower(n[i]);
        changed = changed || child != n[i];
        children.push_back(child);
      }
      const ASTNode carrier = changed ? rebuild(n, children) : n;
      packed_cache[n] = carrier;
      return decodeCarrier(n, carrier);
    }

    std::unique_ptr<symbolic_fp::uf> result;
    switch (kind)
    {
      case ITE:
        assert(n.Degree() == 3);
        // A mux holding one branch as its packed circuit (deriveSourceSort's
        // ITE rule) cannot unpack branchwise -- the circuit branch carries
        // no float sort. Both branches are packed bits, so the whole mux is
        // one packed carrier: decode that instead.
        if (n[1].GetSourceSort() != n[2].GetSourceSort())
          return decodeCarrier(n, asPacked(n));
        requireSameFormat(n[1], n[2]);
        result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::select(
            lower(n[0]), asUnpacked(n[1]), asUnpacked(n[2]))));
        break;

      case FP_ABS:
        result.reset(new symbolic_fp::uf(
            symbolic_fp::unpacked::abs(result_format, asUnpacked(n[0]))));
        break;
      case FP_NEG:
        result.reset(new symbolic_fp::uf(
            symbolic_fp::unpacked::neg(result_format, asUnpacked(n[0]))));
        break;

      case FP_ADD:
      case FP_SUB:
      case FP_MUL:
      case FP_DIV:
        requireSameFormat(n[1], n[2]);
        if (kind == FP_ADD)
          result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::add(
              result_format, lower(n[0]), asUnpacked(n[1]),
              asUnpacked(n[2]))));
        else if (kind == FP_SUB)
          result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::sub(
              result_format, lower(n[0]), asUnpacked(n[1]),
              asUnpacked(n[2]))));
        else if (kind == FP_MUL)
          result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::mul(
              result_format, lower(n[0]), asUnpacked(n[1]),
              asUnpacked(n[2]))));
        else
          result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::div(
              result_format, lower(n[0]), asUnpacked(n[1]),
              asUnpacked(n[2]))));
        break;

      case FP_FMA:
        requireSameFormat(n[1], n[2]);
        requireSameFormat(n[1], n[3]);
        result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::fma(
            result_format, lower(n[0]), asUnpacked(n[1]), asUnpacked(n[2]),
            asUnpacked(n[3]))));
        break;

      case FP_SQRT:
        result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::sqrt(
            result_format, lower(n[0]), asUnpacked(n[1]))));
        break;

      case FP_REM:
      {
        const SourceSort sort = n.GetSourceSort();
        if (!FloatBlaster::remSupported(sort.exponentWidth(),
                                        sort.significandWidth()))
          FatalError("FloatBlast: fp.rem is not supported at this format: "
                     "its circuit is exponential in the exponent width");
        requireSameFormat(n[0], n[1]);
        result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::rem(
            result_format, asUnpacked(n[0]), asUnpacked(n[1]))));
        break;
      }

      case FP_MIN:
      case FP_MAX:
      {
        requireTotalised(n, 3);
        requireSameFormat(n[0], n[1]);
        const ASTNode choice = node_factory->CreateNode(
            EQ, lower(n[2]), bm->CreateOneConst(1));
        result.reset(new symbolic_fp::uf(
            kind == FP_MIN
                ? symbolic_fp::unpacked::min(result_format, asUnpacked(n[0]),
                                             asUnpacked(n[1]), choice)
                : symbolic_fp::unpacked::max(result_format, asUnpacked(n[0]),
                                             asUnpacked(n[1]), choice)));
        break;
      }

      case FP_ROUNDTOINTEGRAL:
      {
        result.reset(new symbolic_fp::uf(
            symbolic_fp::unpacked::roundToIntegral(
                result_format, lower(n[0]), asUnpacked(n[1]))));
        break;
      }

      case FP_TOFP:
        if (n.Degree() == 3)
        {
          ++stats.unpack_builds;
          result.reset(new symbolic_fp::uf(symbolic_fp::unpacked::decode(
              result_format, lower(n[2]))));
        }
        else
        {
          assert(n.Degree() == 4);
          result.reset(new symbolic_fp::uf(
              symbolic_fp::unpacked::convertFloatToFloat(
                  formatOf(n[3]), result_format, lower(n[2]),
                  asUnpacked(n[3]))));
        }
        break;

      case FP_TOFP_SIGNED:
      case FP_TOFP_UNSIGNED:
        assert(n.Degree() == 4);
        result.reset(new symbolic_fp::uf(
            symbolic_fp::unpacked::convertBVToFloat(
                result_format, lower(n[2]), lower(n[3]),
                kind == FP_TOFP_SIGNED)));
        break;

      default:
      {
        // A legacy non-FP carrier node may still have a declared/stored FP
        // source sort. Decode the rebuilt carrier once rather than guessing
        // an operation from its width.
        if (is_FP_kind(kind))
          FatalError("FloatBlast: unhandled floating-point result kind: ", n);

        ASTVec children;
        children.reserve(n.Degree());
        bool changed = false;
        for (size_t i = 0; i < n.Degree(); ++i)
        {
          const ASTNode child = lower(n[i]);
          changed = changed || child != n[i];
          children.push_back(child);
        }
        const ASTNode carrier = changed ? rebuild(n, children) : n;
        packed_cache[n] = carrier;
        return decodeCarrier(n, carrier);
      }
    }

    assert(result.get() != nullptr);
    if (kind != ITE)
      ++stats.unpacked_operation_builds;
    return remember(n, std::move(result));
  }

  ASTNode lowerFpTerminal(const ASTNode& n)
  {
    const Kind kind = n.GetKind();
    switch (kind)
    {
      case FP_TO_UBV:
      case FP_TO_SBV:
        requireTotalised(n, 4);
        return symbolic_fp::unpacked::toBV(
            formatOf(n[2]), lower(n[1]), asUnpacked(n[2]),
            n[0].GetUnsignedConst(), lower(n[3]), kind == FP_TO_SBV);

      case FP_TO_IEEE_BV:
        assert(n.Degree() == 1);
        return canonicalPacked(n[0]);

      case FP_SMT_EQ:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::smtEqual(
            formatOf(n[0]), asUnpacked(n[0]), asUnpacked(n[1]));
      }
      case FP_EQ:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::ieeeEqual(
            formatOf(n[0]), asUnpacked(n[0]), asUnpacked(n[1]));
      }
      case FP_LT:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::lessThan(
            formatOf(n[0]), asUnpacked(n[0]), asUnpacked(n[1]));
      }
      case FP_LEQ:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::lessThanOrEqual(
            formatOf(n[0]), asUnpacked(n[0]), asUnpacked(n[1]));
      }
      case FP_GT:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::lessThan(
            formatOf(n[0]), asUnpacked(n[1]), asUnpacked(n[0]));
      }
      case FP_GEQ:
      {
        requireSameFormat(n[0], n[1]);
        const ASTNode survivor = nativeComparisonSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::lessThanOrEqual(
            formatOf(n[0]), asUnpacked(n[1]), asUnpacked(n[0]));
      }

      case FP_ISNORMAL:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isNormal(formatOf(n[0]),
                                               asUnpacked(n[0]));
      }
      case FP_ISSUBNORMAL:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isSubnormal(formatOf(n[0]),
                                                  asUnpacked(n[0]));
      }
      case FP_ISZERO:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        if (bm->UserFlags.fp_native_add_iszero &&
            n[0].GetKind() == FP_ADD && n[0].Degree() == 3)
        {
          requireSameFormat(n[0][1], n[0][2]);
          ++stats.add_iszero_builds;
          return symbolic_fp::unpacked::addIsZero(
              formatOf(n[0]), asUnpacked(n[0][1]), asUnpacked(n[0][2]));
        }
        return symbolic_fp::unpacked::isZero(formatOf(n[0]),
                                             asUnpacked(n[0]));
      }
      case FP_ISINFINITE:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isInfinite(formatOf(n[0]),
                                                 asUnpacked(n[0]));
      }
      case FP_ISNAN:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isNaN(formatOf(n[0]),
                                            asUnpacked(n[0]));
      }
      case FP_ISNEGATIVE:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isNegative(formatOf(n[0]),
                                                 asUnpacked(n[0]));
      }
      case FP_ISPOSITIVE:
      {
        const ASTNode survivor = nativeClassificationSurvivor(n);
        if (!survivor.IsNull())
          return survivor;
        return symbolic_fp::unpacked::isPositive(formatOf(n[0]),
                                                 asUnpacked(n[0]));
      }

      default:
        FatalError("FloatBlast: unhandled target-valued floating-point kind: ",
                   n);
    }
  }

  STPMgr* bm;
  NodeFactory* node_factory;
  FloatBlast::Statistics stats;

  // Only the source/target FP boundary survives between calls. Generic BV
  // traversal state is released after every root to avoid retaining whole
  // pre-simplification DAGs for the lifetime of a model.
  ASTNodeMap traversal_cache;
  ASTNodeMap terminal_cache;
  ASTNodeMap packed_cache;
  ASTNodeMap canonical_packed_cache;
  UnpackedMap unpacked_cache;
};

FloatBlast::FloatBlast(STPMgr* bm_) : impl(new Impl(bm_)) {}

FloatBlast::~FloatBlast() = default;

ASTNode FloatBlast::topLevel(const ASTNode& n) { return impl->topLevel(n); }

ASTNode FloatBlast::lowerOperation(STPMgr* bm, const ASTNode& n)
{
  // A context of its own: these callers lower one node, unrelated to the
  // solve's, and must not share or disturb its caches.
  FloatBlast lower(bm);
  return lower.topLevel(n);
}

const FloatBlast::Statistics& FloatBlast::statistics() const noexcept
{
  return impl->statistics();
}

} // namespace stp

/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

#include "stp/Simplifier/ValueSetAnalysis.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Util/CBVOps.h"

namespace stp
{

  const size_t ValueSet::MAX_ELEMENTS;

  ValueSet* ValueSetAnalysis::fresh(const ASTNode& n) const
  {
    return new ValueSet(n.GetValueWidth() > 0 ? n.GetValueWidth() : 1,
                        BOOLEAN_TYPE == n.GetType());
  }

  namespace
  {
    // The conversions between vectors and machine words -- allOnes,
    // mask64, low64 and cbvFromU64 -- are shared: see Util/CBVOps.h.

    // The shift amount, saturated at the width: shifting by the width or
    // more always gives the same answer.
    unsigned shiftAmount(const CBV v, unsigned width)
    {
      uint64_t result = 0;
      for (unsigned i = 0; i < bits_(v); i++)
        if (CONSTANTBV::BitVector_bit_test(v, i))
        {
          if (i >= 63)
            return width;
          result |= (1ull << i);
          if (result >= width)
            return width;
        }
      return (unsigned)result;
    }

    CBV boolCBV(bool b)
    {
      CBV r = CONSTANTBV::BitVector_Create(1, true);
      if (b)
        CONSTANTBV::BitVector_Bit_On(r, 0);
      return r;
    }

    bool isTrue(const CBV v) { return CONSTANTBV::BitVector_bit_test(v, 0); }

    // The analysis is written once, over whichever of the two
    // representations of a value below it's instantiated with. WideRep
    // holds a value as a CONSTANTBV bit-vector of any width, NarrowRep
    // holds one of at most 64 bits natively; which one a node is analysed
    // with is decided on width in dispatchToTransferFunctions, and
    // nothing else here depends on the choice.
    //
    // A wide value is owned by whoever holds it, so it is cloned and
    // destroyed explicitly. A narrow value owns nothing, which makes
    // copy() and destroy() no-ops there.

    struct WideRep
    {
      typedef CBV Value;

      static Value zero(unsigned width) { return mkZero(width); }

      static Value ones(unsigned width) { return allOnes(width); }

      static Value ofU64(unsigned width, uint64_t v)
      {
        return cbvFromU64(width, v);
      }

      // v moved up by "shift" bits. The caller only ever passes values
      // that still fit in the width once shifted.
      static Value ofU64Shifted(unsigned width, uint64_t v, unsigned shift)
      {
        Value result = mkZero(width);
        for (unsigned i = 0; i < 64 && i + shift < width; i++)
          if ((v >> i) & 1)
            CONSTANTBV::BitVector_Bit_On(result, i + shift);
        return result;
      }

      static bool bit(const Value v, unsigned i)
      {
        return CONSTANTBV::BitVector_bit_test(v, i);
      }

      static void setBit(Value& v, unsigned i, bool on)
      {
        if (on)
          CONSTANTBV::BitVector_Bit_On(v, i);
        else
          CONSTANTBV::BitVector_Bit_Off(v, i);
      }

      static Value copy(const Value v)
      {
        return CONSTANTBV::BitVector_Clone(v);
      }

      static void destroy(Value v) { CONSTANTBV::BitVector_Destroy(v); }

      static int compare(const Value a, const Value b)
      {
        return CONSTANTBV::BitVector_Lexicompare(a, b);
      }

      // Booleans are width-1 vectors with bit zero as the truth value.
      static Value ofBool(bool b) { return boolCBV(b); }
      static bool truth(const Value v) { return isTrue(v); }

      static bool predicate(Kind k, const Value a, const Value b, unsigned)
      {
        return NonMemberBVConstPredicateEvaluator(k, a, b);
      }

      static Value term(Kind k, const ASTNode& n, const vector<Value>& args,
                        const vector<unsigned>&, unsigned)
      {
        return NonMemberBVConstEvaluator(k, args, n.GetValueWidth());
      }

      // A set already holds its members in this representation.
      static const vector<Value>* membersOf(const ValueSet* child,
                                            vector<Value>&)
      {
        return &child->values;
      }

      // Takes ownership of v.
      static CBV toCBV(Value v, unsigned) { return v; }
    };

    struct NarrowRep
    {
      typedef uint64_t Value;

      static Value zero(unsigned) { return 0; }

      static Value ones(unsigned width) { return mask64(width); }

      static Value ofU64(unsigned width, uint64_t v)
      {
        return v & mask64(width);
      }

      static Value ofU64Shifted(unsigned width, uint64_t v, unsigned shift)
      {
        // Shifted out of the width entirely, which the caller only does
        // with a zero value.
        if (shift >= 64)
          return 0;
        return (v << shift) & mask64(width);
      }

      static bool bit(Value v, unsigned i) { return ((v >> i) & 1) != 0; }

      static void setBit(Value& v, unsigned i, bool on)
      {
        if (on)
          v |= (1ull << i);
        else
          v &= ~(1ull << i);
      }

      static Value copy(Value v) { return v; }

      static void destroy(Value) {}

      static int compare(Value a, Value b)
      {
        return a < b ? -1 : (a == b ? 0 : 1);
      }

      // Booleans are 0 or 1.
      static Value ofBool(bool b) { return b ? 1 : 0; }
      static bool truth(Value v) { return v != 0; }

      static bool predicate(Kind k, Value a, Value b, unsigned width)
      {
        return NonMemberBVConstPredicateEvaluator64(k, a, b, width);
      }

      static Value term(Kind k, const ASTNode&, const vector<Value>& args,
                        const vector<unsigned>& widths, unsigned outWidth)
      {
        return NonMemberBVConstEvaluator64(k, args, widths, outWidth);
      }

      static const vector<Value>* membersOf(const ValueSet* child,
                                            vector<Value>& owned)
      {
        owned.reserve(child->size());
        for (const CBV m : child->values)
          owned.push_back(low64(m));
        return &owned;
      }

      static CBV toCBV(Value v, unsigned width)
      {
        return cbvFromU64(width, v);
      }
    };

    // What the analysis needs a node's kind evaluated over, straight on
    // the values -- the term and predicate evaluation itself is shared
    // with NonMemberBVConstEvaluator (consteval.cpp); building a
    // hash-consed constant node for every child member and every result
    // here was most of what the analysis used to spend its time on.
    // Returns a value the caller owns.
    template <class Rep>
    typename Rep::Value evalOn(Kind k, const ASTNode& n,
                               const vector<typename Rep::Value>& args,
                               const vector<unsigned>& argWidths,
                               unsigned outWidth)
    {
      switch (k)
      {
        // The boolean connectives.
        case NOT:
          return Rep::ofBool(!Rep::truth(args[0]));

        case OR:
        case NOR:
        {
          bool any = false;
          for (const typename Rep::Value a : args)
            if (Rep::truth(a))
            {
              any = true;
              break;
            }
          return Rep::ofBool(OR == k ? any : !any);
        }

        case AND:
        case NAND:
        {
          bool all = true;
          for (const typename Rep::Value a : args)
            if (!Rep::truth(a))
            {
              all = false;
              break;
            }
          return Rep::ofBool(AND == k ? all : !all);
        }

        case XOR:
        {
          bool parity = false;
          for (const typename Rep::Value a : args)
            if (Rep::truth(a))
              parity = !parity;
          return Rep::ofBool(parity);
        }

        case IFF:
          return Rep::ofBool(Rep::truth(args[0]) == Rep::truth(args[1]));

        case IMPLIES:
          return Rep::ofBool(!Rep::truth(args[0]) || Rep::truth(args[1]));

        // The predicates over two bit-vectors.
        case BOOLEXTRACT:
        case EQ:
        case BVLT:
        case BVLE:
        case BVGT:
        case BVGE:
        case BVSLT:
        case BVSLE:
        case BVSGT:
        case BVSGE:
          return Rep::ofBool(
              Rep::predicate(k, args[0], args[1], argWidths[0]));

        // The bit-vector terms. ITE is handled before evaluation is
        // reached, and the evaluator rejects anything else that doesn't
        // pass constEvaluable.
        default:
          return Rep::term(k, n, args, argWidths, outWidth);
      }
    }

    // Adds v, which it takes ownership of, to a sorted array of distinct
    // values. False, without adding, when the array is full.
    template <class Rep>
    bool insertSorted(typename Rep::Value* values, size_t& size,
                      typename Rep::Value v)
    {
      typename Rep::Value* const end = values + size;
      typename Rep::Value* const it = std::lower_bound(
          values, end, v, [](const typename Rep::Value a,
                             const typename Rep::Value b)
          { return Rep::compare(a, b) < 0; });

      if (it != end && Rep::compare(*it, v) == 0)
      {
        Rep::destroy(v);
        return true;
      }
      if (size >= ValueSet::MAX_ELEMENTS)
      {
        Rep::destroy(v);
        return false;
      }
      std::copy_backward(it, end, end + 1);
      *it = v;
      size++;
      return true;
    }

    // The values evaluated so far, sorted ascending without duplicates.
    // Owns them: whatever is left when it goes out of scope is destroyed.
    template <class Rep>
    struct Results
    {
      typename Rep::Value values[ValueSet::MAX_ELEMENTS];
      size_t count = 0;

      Results() = default;
      Results(const Results&) = delete;
      Results& operator=(const Results&) = delete;

      ~Results()
      {
        for (size_t i = 0; i < count; i++)
          Rep::destroy(values[i]);
      }

      bool insert(typename Rep::Value v)
      {
        return insertSorted<Rep>(values, count, v);
      }
    };

    // The per-child values the analysis makes itself, and so has to
    // destroy: the ones standing in for a child nothing is known about,
    // and, for a representation a set doesn't already hold its members
    // in, the converted copies of them.
    template <class Rep>
    struct OwnedValues
    {
      vector<vector<typename Rep::Value>> values;

      OwnedValues(size_t degree) : values(degree) {}
      OwnedValues(const OwnedValues&) = delete;
      OwnedValues& operator=(const OwnedValues&) = delete;

      ~OwnedValues()
      {
        for (const vector<typename Rep::Value>& v : values)
          for (const typename Rep::Value x : v)
            Rep::destroy(x);
      }
    };

    // Operations that are one-to-one in each argument (or, for equality,
    // reach both answers whatever the other side is): once an operand is
    // unknown the result can be anything, so there is nothing to say.
    bool anythingWhenUnknown(Kind k)
    {
      switch (k)
      {
        case EQ:
        case IFF:
        case XOR:
        case NOT:
        case BVXOR:
        case BVNOT:
        case BVPLUS:
        case BVSUB:
        case BVUMINUS:
          return true;
        default:
          return false;
      }
    }
  }

  bool ValueSetAnalysis::constEvaluable(Kind k)
  {
    // The kinds the switch in NonMemberBVConstEvaluator handles; it
    // exits fatally on anything else. Note BVNAND/BVNOR/BVXNOR are not
    // implemented there.
    switch (k)
    {
      case BOOLEXTRACT:
      case BVNOT:
      case BVSX:
      case BVZX:
      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
      case BVAND:
      case BVOR:
      case BVXOR:
      case BVSUB:
      case BVUMINUS:
      case BVEXTRACT:
      case BVCONCAT:
      case BVMULT:
      case BVPLUS:
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
      case BVDIV:
      case BVMOD:
      case ITE:
      case EQ:
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
      case NOT:
      case OR:
      case NOR:
      case XOR:
      case AND:
      case NAND:
      case IFF:
      case IMPLIES:
        return true;
      default:
        return false;
    }
  }

  // An unknown child stands for every value of its width. Rather than give
  // up, list values that produce exactly the same results -- there are
  // usually few or none of them, and the caller stops as soon as too many
  // results pile up.
  template <class Rep>
  bool ValueSetAnalysis::standIns(const ASTNode& n, size_t index,
                                  const vector<const ValueSet*>& children,
                                  unsigned width,
                                  vector<typename Rep::Value>& out,
                                  Expand& expandWith)
  {
    const Kind k = n.GetKind();

    if (anythingWhenUnknown(k))
      return false;

    switch (k)
    {
      // Multiplication, division and modulus are left out on purpose:
      // they are the expensive ones to evaluate, and an unknown operand
      // rarely pins their result down.
      case BVMULT:
      case BVDIV:
      case BVMOD:
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
        return false;

      case BVAND:
        expandWith = Expand::Submask;
        out.push_back(Rep::ones(width));
        return true;

      case BVOR:
        expandWith = Expand::Supermask;
        out.push_back(Rep::zero(width));
        return true;

      // The comparisons are monotone in each side, so whatever they can
      // answer they already answer at the extremes of the unknown one.
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
        out.push_back(Rep::zero(width));
        out.push_back(Rep::ones(width));
        return true;

      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
      {
        typename Rep::Value signedMax = Rep::ones(width);
        Rep::setBit(signedMax, width - 1, false);
        out.push_back(Rep::ofU64Shifted(width, 1, width - 1)); // signed minimum
        out.push_back(signedMax);                              // signed maximum
        return true;
      }

      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
        return shiftStandIns<Rep>(n, index, children, out);

      default:
        break;
    }

    // Anything else: every value of the width, when there are few enough
    // of them. A wider child would push the result past what a set holds.
    if (width > SMALL_WIDTH)
      return false;
    for (uint64_t v = 0; v < (1ull << width); v++)
      out.push_back(Rep::ofU64(width, v));
    return true;
  }

  template <class Rep>
  bool ValueSetAnalysis::shiftStandIns(const ASTNode& n, size_t index,
                                       const vector<const ValueSet*>& children,
                                       vector<typename Rep::Value>& out)
  {
    const Kind k = n.GetKind();
    const unsigned width = n.GetValueWidth();

    if (index == 1)
    {
      // The amount. Shifting by the width or more always gives the same
      // answer, so the amounts to try stop there.
      if (children[0] == nullptr)
        return false;
      if ((width + 1) * children[0]->size() > PRODUCT_CAP)
        return false;
      for (unsigned s = 0; s <= width; s++)
        out.push_back(Rep::ofU64(width, s));
      return true;
    }

    // The value being shifted. Only the bits that survive the smallest of
    // the amounts can reach the result, so only those are worth varying.
    if (children[1] == nullptr)
      return false;

    unsigned smallest = width;
    for (const CBV s : children[1]->values)
      smallest = std::min(smallest, shiftAmount(s, width));

    // Shifted all the way out, an arithmetic shift still copies the sign
    // bit, so that bit always has to be varied.
    if (BVSRSHIFT == k && smallest == width)
      smallest = width - 1;

    const unsigned survivors = width - smallest;
    if (survivors > SMALL_WIDTH)
      return false;

    // A left shift moves the surviving bits down to the bottom, any other
    // shift leaves them where the smallest amount puts them.
    const unsigned shift = BVLEFTSHIFT == k ? 0 : smallest;
    for (uint64_t v = 0; v < (1ull << survivors); v++)
      out.push_back(Rep::ofU64Shifted(width, v, shift));
    return true;
  }

  // In place on the sorted array of values evaluated so far. False when
  // the expansion wouldn't fit.
  template <class Rep>
  bool ValueSetAnalysis::expand(typename Rep::Value* values, size_t& size,
                                unsigned width, Expand how)
  {
    typename Rep::Value members[ValueSet::MAX_ELEMENTS];
    const size_t count = size;
    std::copy(values, values + count, members);
    size = 0; // the values are owned by "members" until the end.

    bool fitted = true;
    for (size_t i = 0; i < count && fitted; i++)
    {
      // The bits the unknown operand is free to change.
      vector<unsigned> free;
      for (unsigned b = 0; b < width; b++)
      {
        const bool one = Rep::bit(members[i], b);
        if (Expand::Submask == how ? one : !one)
          free.push_back(b);
      }

      // Two to the power of that many members: past three bits it can't
      // fit in a set anyway.
      if (free.size() > 31 || (1ull << free.size()) > ValueSet::MAX_ELEMENTS)
      {
        fitted = false;
        break;
      }

      // Every subset of the free bits, cleared from the member or set in
      // it.
      for (uint64_t v = 0; v < (1ull << free.size()) && fitted; v++)
      {
        typename Rep::Value variant = Rep::copy(members[i]);
        for (unsigned b = 0; b < free.size(); b++)
        {
          const bool set_bit = ((v >> b) & 1) != 0;
          if (Expand::Submask == how)
          {
            if (!set_bit)
              Rep::setBit(variant, free[b], false);
          }
          else if (set_bit)
            Rep::setBit(variant, free[b], true);
        }

        fitted = insertSorted<Rep>(values, size, variant);
      }
    }

    for (size_t i = 0; i < count; i++)
      Rep::destroy(members[i]);
    return fitted;
  }

  // Most operations are handled by evaluating the node over the cartesian
  // product of the values its children can take.
  template <class Rep>
  ValueSet* ValueSetAnalysis::product(const ASTNode& n,
                                      const vector<const ValueSet*>& children)
  {
    typedef typename Rep::Value Value;

    const Kind k = n.GetKind();
    const size_t degree = children.size();
    const unsigned outWidth = n.GetValueWidth() > 0 ? n.GetValueWidth() : 1;

    vector<unsigned> widths(degree);
    for (size_t i = 0; i < degree; i++)
      widths[i] = std::max(1u, n[i].GetValueWidth());

    // What each child ranges over: its set's values, or values standing
    // in for a child nothing is known about.
    OwnedValues<Rep> owned(degree);
    vector<const vector<Value>*> members(degree);
    Expand expandWith = Expand::None;
    for (size_t i = 0; i < degree; i++)
    {
      if (children[i] != nullptr)
        members[i] = Rep::membersOf(children[i], owned.values[i]);
      else if (standIns<Rep>(n, i, children, widths[i], owned.values[i],
                             expandWith))
        members[i] = &owned.values[i];
      else
      {
        widened++;
        return nullptr;
      }
    }

    size_t combinations = 1;
    for (size_t i = 0; i < degree; i++)
    {
      combinations *= members[i]->size();
      if (combinations > PRODUCT_CAP)
      {
        widened++;
        return nullptr;
      }
    }

    // Holding every value of the width, a set says exactly what a null
    // pointer says, and the remaining combinations can't grow it -- which
    // is where an evaluation of a comparison usually ends up.
    const size_t complete = outWidth < 4 ? ((size_t)1 << outWidth) : (size_t)-1;

    // Evaluate the node over each combination of the children's values,
    // into a sorted array.
    Results<Rep> results;
    vector<Value> combination(degree);
    vector<size_t> odometer(degree, 0);
    for (size_t count = 0; count < combinations; count++)
    {
      for (size_t i = 0; i < degree; i++)
        combination[i] = (*members[i])[odometer[i]];

      if (!results.insert(evalOn<Rep>(k, n, combination, widths, outWidth)) ||
          results.count >= complete)
      {
        widened++;
        return nullptr;
      }

      for (size_t i = 0; i < odometer.size(); i++)
      {
        if (++odometer[i] < members[i]->size())
          break;
        odometer[i] = 0;
      }
    }

    if (Expand::None != expandWith &&
        !expand<Rep>(results.values, results.count, outWidth, expandWith))
    {
      widened++;
      return nullptr;
    }

    if (results.count >= complete)
    {
      widened++;
      return nullptr;
    }

    // Only now build the bit-vectors, one per member that survived. The
    // array is sorted ascending, which is the set's order.
    ValueSet* result = fresh(n);
    result->values.reserve(results.count);
    for (size_t i = 0; i < results.count; i++)
    {
      CBV member = Rep::toCBV(results.values[i], outWidth);
      assert(bits_(member) == outWidth);
      result->values.push_back(member);
    }
    results.count = 0; // the set owns them now.

    propagated++;
    return result;
  }

  ValueSet* ValueSetAnalysis::dispatchToTransferFunctions(
      const ASTNode& n, const vector<const ValueSet*>& children)
  {
    const Kind k = n.GetKind();

    if (BVCONST == k)
    {
      ValueSet* result = fresh(n);
      result->insert(CONSTANTBV::BitVector_Clone(n.GetBVConst()));
      propagated++;
      return result;
    }

    if (TRUE == k || FALSE == k)
    {
      ValueSet* result = fresh(n);
      CBV v = CONSTANTBV::BitVector_Create(1, true);
      if (TRUE == k)
        CONSTANTBV::BitVector_Bit_On(v, 0);
      result->insert(v);
      propagated++;
      return result;
    }

    if (ITE == k)
    {
      // The condition selects a branch when it's known; otherwise the
      // node can take any value from either branch.
      const ValueSet* condition = children[0];
      if (condition != nullptr && condition->isConstant())
      {
        const ValueSet* branch =
            CONSTANTBV::BitVector_bit_test(condition->smallest(), 0)
                ? children[1]
                : children[2];
        if (branch == nullptr)
          return nullptr;

        ValueSet* result = fresh(n);
        for (const CBV m : branch->values)
        {
          bool fitted = result->insert(CONSTANTBV::BitVector_Clone(m));
          assert(fitted);
          (void)fitted;
        }
        propagated++;
        return result;
      }

      if (children[1] == nullptr || children[2] == nullptr)
        return nullptr;

      ValueSet* result = fresh(n);
      for (int branch = 1; branch <= 2; branch++)
        for (const CBV m : children[branch]->values)
          if (!result->insert(CONSTANTBV::BitVector_Clone(m)))
          {
            delete result;
            widened++;
            return nullptr;
          }
      propagated++;
      return result;
    }

    if (!constEvaluable(k) || n.Degree() == 0)
      return nullptr;

    // Nodes whose children and result all fit in 64 bits -- nearly all of
    // them -- are evaluated natively instead of on the bit-vectors.
    bool fits = n.GetValueWidth() <= 64;
    for (size_t i = 0; fits && i < n.Degree(); i++)
      fits = n[i].GetValueWidth() <= 64;

    return fits ? product<NarrowRep>(n, children)
                : product<WideRep>(n, children);
  }

  void ValueSetAnalysis::stats()
  {
    std::cerr << "{ValueSetAnalysis} Propagated: " << propagated << std::endl;
    std::cerr << "{ValueSetAnalysis} Widened: " << widened << std::endl;
  }
}

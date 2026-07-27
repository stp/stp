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
    CBV valueOf(unsigned width, uint64_t value)
    {
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < width && i < 64; i++)
        if ((value >> i) & 1)
          CONSTANTBV::BitVector_Bit_On(result, i);
      return result;
    }

    CBV allOnes(unsigned width)
    {
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Fill(result);
      return result;
    }

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

    // What the analysis needs a node's kind evaluated over, straight on
    // the bit-vectors -- the term and predicate evaluation itself is
    // shared with NonMemberBVConstEvaluator (consteval.cpp); building a
    // hash-consed constant node for every child member and every result
    // here was most of what the analysis used to spend its time on.
    // Booleans are width-1 vectors with bit zero as the truth value.
    // Returns a fresh CBV the caller owns.
    CBV evalOnCBVs(Kind k, const ASTNode& n, const vector<CBV>& args)
    {
      switch (k)
      {
        // The boolean connectives, over width-1 vectors.
        case NOT:
          return boolCBV(!isTrue(args[0]));

        case OR:
        case NOR:
        {
          bool any = false;
          for (const CBV a : args)
            if (isTrue(a))
            {
              any = true;
              break;
            }
          return boolCBV(OR == k ? any : !any);
        }

        case AND:
        case NAND:
        {
          bool all = true;
          for (const CBV a : args)
            if (!isTrue(a))
            {
              all = false;
              break;
            }
          return boolCBV(AND == k ? all : !all);
        }

        case XOR:
        {
          bool parity = false;
          for (const CBV a : args)
            if (isTrue(a))
              parity = !parity;
          return boolCBV(parity);
        }

        case IFF:
          return boolCBV(isTrue(args[0]) == isTrue(args[1]));

        case IMPLIES:
          return boolCBV(!isTrue(args[0]) || isTrue(args[1]));

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
          return boolCBV(
              NonMemberBVConstPredicateEvaluator(k, args[0], args[1]));

        // The bit-vector terms. ITE is handled before evaluation is
        // reached, and the evaluator rejects anything else that doesn't
        // pass constEvaluable.
        default:
          return NonMemberBVConstEvaluator(k, args, n.GetValueWidth());
      }
    }

    uint64_t mask64(unsigned width)
    {
      return width >= 64 ? ~0ull : (1ull << width) - 1;
    }

    // The value of a bit-vector of at most 64 bits. The chunk functions
    // move at most an unsigned long per call, which is 32 bits on some
    // platforms, so go in two halves.
    uint64_t cbvToU64(const CBV v)
    {
      const unsigned width = bits_(v);
      assert(width <= 64);
      uint64_t result =
          CONSTANTBV::BitVector_Chunk_Read(v, std::min(width, 32u), 0);
      if (width > 32)
        result |= (uint64_t)CONSTANTBV::BitVector_Chunk_Read(v, width - 32, 32)
                  << 32;
      return result;
    }

    CBV u64ToCBV(uint64_t v, unsigned width)
    {
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Chunk_Store(result, std::min(width, 32u), 0,
                                        (unsigned long)(v & 0xffffffffull));
      if (width > 32)
        CONSTANTBV::BitVector_Chunk_Store(result, width - 32, 32,
                                          (unsigned long)(v >> 32));
      return result;
    }

    size_t popcount64(uint64_t v)
    {
      size_t count = 0;
      while (v != 0)
      {
        v &= v - 1;
        count++;
      }
      return count;
    }

    // evalOnCBVs again, on values that fit in 64 bits. Booleans are 0 or 1.
    uint64_t evalOnU64s(Kind k, const vector<uint64_t>& args,
                        const vector<unsigned>& argWidths, unsigned outWidth)
    {
      switch (k)
      {
        // The boolean connectives, over 0 and 1.
        case NOT:
          return args[0] ^ 1;

        case OR:
        case NOR:
        {
          uint64_t any = 0;
          for (const uint64_t a : args)
            any |= a;
          return OR == k ? any : any ^ 1;
        }

        case AND:
        case NAND:
        {
          uint64_t all = 1;
          for (const uint64_t a : args)
            all &= a;
          return AND == k ? all : all ^ 1;
        }

        case XOR:
        {
          uint64_t parity = 0;
          for (const uint64_t a : args)
            parity ^= a;
          return parity;
        }

        case IFF:
          return (args[0] == args[1]) ? 1 : 0;

        case IMPLIES:
          return (args[0] == 0 || args[1] == 1) ? 1 : 0;

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
          return NonMemberBVConstPredicateEvaluator64(k, args[0], args[1],
                                                      argWidths[0])
                     ? 1
                     : 0;

        // The bit-vector terms. ITE is handled before evaluation is
        // reached, and the evaluator rejects anything else that doesn't
        // pass constEvaluable.
        default:
          return NonMemberBVConstEvaluator64(k, args, argWidths, outWidth);
      }
    }

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
  bool ValueSetAnalysis::standIns(const ASTNode& n, size_t index,
                                  const vector<const ValueSet*>& children,
                                  vector<CBV>& out, Expand& expandWith)
  {
    const Kind k = n.GetKind();
    const unsigned width = std::max(1u, n[index].GetValueWidth());

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
        out.push_back(allOnes(width));
        return true;

      case BVOR:
        expandWith = Expand::Supermask;
        out.push_back(CONSTANTBV::BitVector_Create(width, true));
        return true;

      // The comparisons are monotone in each side, so whatever they can
      // answer they already answer at the extremes of the unknown one.
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
        out.push_back(CONSTANTBV::BitVector_Create(width, true));
        out.push_back(allOnes(width));
        return true;

      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
      {
        CBV signedMin = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Bit_On(signedMin, width - 1);
        CBV signedMax = allOnes(width);
        CONSTANTBV::BitVector_Bit_Off(signedMax, width - 1);
        out.push_back(signedMin);
        out.push_back(signedMax);
        return true;
      }

      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
        return shiftStandIns(n, index, children, out);

      default:
        break;
    }

    // Anything else: every value of the width, when there are few enough
    // of them. A wider child would push the result past what a set holds.
    if (width > SMALL_WIDTH)
      return false;
    for (uint64_t v = 0; v < (1ull << width); v++)
      out.push_back(valueOf(width, v));
    return true;
  }

  bool ValueSetAnalysis::shiftStandIns(const ASTNode& n, size_t index,
                                       const vector<const ValueSet*>& children,
                                       vector<CBV>& out)
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
        out.push_back(valueOf(width, s));
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

    for (uint64_t v = 0; v < (1ull << survivors); v++)
    {
      CBV value = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < survivors; i++)
        if ((v >> i) & 1)
          CONSTANTBV::BitVector_Bit_On(value,
                                       BVLEFTSHIFT == k ? i : i + smallest);
      out.push_back(value);
    }
    return true;
  }

  // Takes ownership of "set".
  ValueSet* ValueSetAnalysis::expand(ValueSet* set, Expand how)
  {
    const unsigned width = set->getWidth();
    ValueSet* result = new ValueSet(width, set->isBoolean());

    for (const CBV member : set->values)
    {
      // The bits the unknown operand is free to change.
      vector<unsigned> free;
      for (unsigned i = 0; i < width; i++)
      {
        const bool one = CONSTANTBV::BitVector_bit_test(member, i);
        if (Expand::Submask == how ? one : !one)
          free.push_back(i);
      }

      // Two to the power of that many members: past three bits it can't
      // fit in a set anyway.
      if (free.size() > 31 || (1ull << free.size()) > ValueSet::MAX_ELEMENTS)
      {
        delete result;
        delete set;
        return nullptr;
      }

      for (uint64_t v = 0; v < (1ull << free.size()); v++)
      {
        CBV variant = CONSTANTBV::BitVector_Clone(member);
        for (unsigned b = 0; b < free.size(); b++)
        {
          const bool set_bit = ((v >> b) & 1) != 0;
          if (Expand::Submask == how)
          {
            if (!set_bit)
              CONSTANTBV::BitVector_Bit_Off(variant, free[b]);
          }
          else if (set_bit)
            CONSTANTBV::BitVector_Bit_On(variant, free[b]);
        }

        if (!result->insert(variant))
        {
          delete result;
          delete set;
          return nullptr;
        }
      }
    }

    delete set;
    return result;
  }

  // standIns, on values that fit in 64 bits.
  bool ValueSetAnalysis::standIns64(const ASTNode& n, size_t index,
                                    const vector<const ValueSet*>& children,
                                    unsigned width, vector<uint64_t>& out,
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
        out.push_back(mask64(width));
        return true;

      case BVOR:
        expandWith = Expand::Supermask;
        out.push_back(0);
        return true;

      // The comparisons are monotone in each side, so whatever they can
      // answer they already answer at the extremes of the unknown one.
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
        out.push_back(0);
        out.push_back(mask64(width));
        return true;

      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
        out.push_back(1ull << (width - 1)); // signed minimum
        out.push_back(mask64(width) >> 1);  // signed maximum
        return true;

      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
        return shiftStandIns64(n, index, children, out);

      default:
        break;
    }

    // Anything else: every value of the width, when there are few enough
    // of them. A wider child would push the result past what a set holds.
    if (width > SMALL_WIDTH)
      return false;
    for (uint64_t v = 0; v < (1ull << width); v++)
      out.push_back(v);
    return true;
  }

  bool ValueSetAnalysis::shiftStandIns64(
      const ASTNode& n, size_t index, const vector<const ValueSet*>& children,
      vector<uint64_t>& out)
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
        out.push_back(s);
      return true;
    }

    // The value being shifted. Only the bits that survive the smallest of
    // the amounts can reach the result, so only those are worth varying.
    if (children[1] == nullptr)
      return false;

    unsigned smallest = width;
    for (const CBV s : children[1]->values)
      smallest = (unsigned)std::min<uint64_t>(smallest, cbvToU64(s));

    // Shifted all the way out, an arithmetic shift still copies the sign
    // bit, so that bit always has to be varied.
    if (BVSRSHIFT == k && smallest == width)
      smallest = width - 1;

    const unsigned survivors = width - smallest;
    if (survivors > SMALL_WIDTH)
      return false;

    for (uint64_t v = 0; v < (1ull << survivors); v++)
      out.push_back(BVLEFTSHIFT == k ? v : v << smallest);
    return true;
  }

  // expand(), in place on a sorted array of at most MAX_ELEMENTS values.
  // False when the expansion wouldn't fit.
  bool ValueSetAnalysis::expand64(uint64_t* values, size_t& size,
                                  unsigned width, Expand how)
  {
    uint64_t members[ValueSet::MAX_ELEMENTS];
    const size_t count = size;
    std::copy(values, values + count, members);
    size = 0;

    for (size_t i = 0; i < count; i++)
    {
      // The bits the unknown operand is free to change.
      const uint64_t free = Expand::Submask == how
                                ? members[i]
                                : (~members[i] & mask64(width));

      // Two to the power of that many members: past three bits it can't
      // fit in a set anyway.
      if (popcount64(free) > 31 ||
          (1ull << popcount64(free)) > ValueSet::MAX_ELEMENTS)
        return false;

      // Every subset of the free bits, cleared from the member or set in
      // it.
      uint64_t subset = free;
      while (true)
      {
        const uint64_t variant =
            Expand::Submask == how ? subset : members[i] | subset;

        uint64_t* end = values + size;
        uint64_t* it = std::lower_bound(values, end, variant);
        if (it == end || *it != variant)
        {
          if (size >= ValueSet::MAX_ELEMENTS)
            return false;
          std::copy_backward(it, end, end + 1);
          *it = variant;
          size++;
        }

        if (subset == 0)
          break;
        subset = (subset - 1) & free;
      }
    }
    return true;
  }

  ValueSet* ValueSetAnalysis::dispatch64(const ASTNode& n,
                                         const vector<const ValueSet*>& children)
  {
    const Kind k = n.GetKind();
    const size_t degree = children.size();
    const unsigned outWidth = n.GetValueWidth() > 0 ? n.GetValueWidth() : 1;

    vector<unsigned> widths(degree);
    for (size_t i = 0; i < degree; i++)
      widths[i] = std::max(1u, n[i].GetValueWidth());

    // What each child ranges over: its set's values, or values standing
    // in for a child nothing is known about.
    vector<vector<uint64_t>> members(degree);
    Expand expandWith = Expand::None;
    for (size_t i = 0; i < degree; i++)
    {
      if (children[i] != nullptr)
      {
        members[i].reserve(children[i]->size());
        for (const CBV m : children[i]->values)
          members[i].push_back(cbvToU64(m));
      }
      else if (!standIns64(n, i, children, widths[i], members[i], expandWith))
      {
        widened++;
        return nullptr;
      }
    }

    size_t combinations = 1;
    for (size_t i = 0; i < degree; i++)
    {
      combinations *= members[i].size();
      if (combinations > PRODUCT_CAP)
      {
        widened++;
        return nullptr;
      }
    }

    // Holding every value of the width, a set says exactly what a null
    // pointer says, and the remaining combinations can't grow it -- which
    // is where an evaluation of a comparison usually ends up.
    const size_t complete =
        outWidth < 4 ? ((size_t)1 << outWidth) : (size_t)-1;

    // Evaluate the node over each combination of the children's values,
    // into a sorted array.
    uint64_t results[ValueSet::MAX_ELEMENTS];
    size_t size = 0;

    vector<uint64_t> combination(degree);
    vector<size_t> odometer(degree, 0);
    for (size_t count = 0; count < combinations; count++)
    {
      for (size_t i = 0; i < degree; i++)
        combination[i] = members[i][odometer[i]];

      const uint64_t r = evalOnU64s(k, combination, widths, outWidth);

      uint64_t* end = results + size;
      uint64_t* it = std::lower_bound(results, end, r);
      if (it == end || *it != r)
      {
        if (size >= ValueSet::MAX_ELEMENTS || size + 1 >= complete)
        {
          widened++;
          return nullptr;
        }
        std::copy_backward(it, end, end + 1);
        *it = r;
        size++;
      }

      for (size_t i = 0; i < odometer.size(); i++)
      {
        if (++odometer[i] < members[i].size())
          break;
        odometer[i] = 0;
      }
    }

    if (Expand::None != expandWith &&
        !expand64(results, size, outWidth, expandWith))
    {
      widened++;
      return nullptr;
    }

    if (size >= complete)
    {
      widened++;
      return nullptr;
    }

    // Only now build the bit-vectors, one per member that survived. The
    // array is sorted ascending, which is the set's order.
    ValueSet* result = fresh(n);
    result->values.reserve(size);
    for (size_t i = 0; i < size; i++)
      result->values.push_back(u64ToCBV(results[i], outWidth));

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
    {
      bool fits = n.GetValueWidth() <= 64;
      for (size_t i = 0; fits && i < n.Degree(); i++)
        fits = n[i].GetValueWidth() <= 64;
      if (fits)
        return dispatch64(n, children);
    }

    // Values standing in for the children nothing is known about.
    struct Owned
    {
      vector<vector<CBV>> values;
      ~Owned()
      {
        for (const vector<CBV>& v : values)
          for (const CBV c : v)
            CONSTANTBV::BitVector_Destroy(c);
      }
    } standIn;
    standIn.values.resize(children.size());

    Expand expandWith = Expand::None;
    for (size_t i = 0; i < children.size(); i++)
      if (children[i] == nullptr &&
          !standIns(n, i, children, standIn.values[i], expandWith))
      {
        widened++;
        return nullptr;
      }

    // What each child ranges over.
    vector<const vector<CBV>*> members(children.size());
    size_t combinations = 1;
    for (size_t i = 0; i < children.size(); i++)
    {
      members[i] = (children[i] != nullptr) ? &children[i]->values
                                            : &standIn.values[i];
      combinations *= members[i]->size();
      if (combinations > PRODUCT_CAP)
      {
        widened++;
        return nullptr;
      }
    }

    // Evaluate the node over each combination of the children's values.
    ValueSet* result = fresh(n);
    vector<CBV> combination(children.size());
    vector<size_t> odometer(children.size(), 0);
    for (size_t count = 0; count < combinations; count++)
    {
      for (size_t i = 0; i < children.size(); i++)
        combination[i] = (*members[i])[odometer[i]];

      if (!result->insert(evalOnCBVs(k, n, combination)))
      {
        delete result;
        widened++;
        return nullptr;
      }

      // Holding every value of the width already, the set says exactly
      // what a null pointer says, and the remaining combinations can't
      // change that -- which is where an evaluation of a comparison
      // usually ends up.
      if (result->isComplete())
      {
        delete result;
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

    if (Expand::None != expandWith)
      result = expand(result, expandWith);

    // A set holding every value of its width says exactly what a null
    // pointer says.
    if (result == nullptr || result->isComplete())
    {
      delete result;
      widened++;
      return nullptr;
    }

    propagated++;
    return result;
  }

  void ValueSetAnalysis::stats()
  {
    std::cerr << "{ValueSetAnalysis} Propagated: " << propagated << std::endl;
    std::cerr << "{ValueSetAnalysis} Widened: " << widened << std::endl;
  }
}

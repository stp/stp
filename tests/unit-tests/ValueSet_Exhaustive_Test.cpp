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

/*
 * The value set transfer functions, exhaustively at small widths.
 *
 * Every combination of input sets is tried -- every subset of the values a
 * child could take, and "nothing is known" as well -- and compared against
 * the values the operation can actually produce. The analysis is allowed to
 * widen completely and say nothing; what it may not do is return a set that
 * is missing a value the operation can produce, or one that is looser than
 * it needs to be.
 *
 * Everything but multiplication, division and modulus is also required to
 * be exact whenever the answer would fit in a set: those are the operations
 * that are cheap enough to be worth reasoning about with an unknown operand
 * (x & 0 is zero however little is known about x).
 */

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/ValueSet.h"
#include "stp/Simplifier/ValueSetAnalysis.h"
#include <algorithm>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using stp::ASTNode;
using stp::ASTVec;
using stp::Kind;
using stp::ValueSet;
using stp::ValueSetAnalysis;

namespace
{

void boot()
{
  static bool booted = false;
  if (!booted)
  {
    CONSTANTBV::BitVector_Boot();
    booted = true;
  }
}

stp::CBV makeCBV(unsigned width, unsigned value)
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

unsigned fromCBV(const stp::CBV v, unsigned width)
{
  unsigned result = 0;
  for (unsigned i = 0; i < width; i++)
    if (CONSTANTBV::BitVector_bit_test(v, i))
      result |= 1u << i;
  return result;
}

std::vector<unsigned> members(const ValueSet* set)
{
  std::vector<unsigned> result;
  if (set != nullptr)
    for (const stp::CBV m : set->values)
      result.push_back(fromCBV(m, set->getWidth()));
  return result;
}

// One child of the node under test.
struct Child
{
  unsigned width;      // 1 for booleans
  bool isBoolean;
  bool isConstant;     // an extract's bounds, an extend's width
  unsigned value;      // when isConstant
};

Child value(unsigned width) { return {width, false, false, 0}; }
Child boolean() { return {1, true, false, 0}; }
Child constant(unsigned v) { return {32, false, true, v}; }

struct OpUnderTest
{
  Kind kind;
  std::string name;
  std::vector<Child> children;
  unsigned resultWidth; // 1 for booleans
  bool resultIsBoolean;
  // Multiplication, division and modulus aren't required to say anything
  // when an operand is unknown.
  bool mustBeExact;
};

// The operations, shaped for the given width.
std::vector<OpUnderTest> operationsAt(unsigned w)
{
  std::vector<OpUnderTest> ops;
  const std::vector<Kind> binary = {
      stp::BVAND,   stp::BVOR,   stp::BVXOR,        stp::BVPLUS,
      stp::BVSUB,   stp::BVMULT, stp::BVDIV,        stp::BVMOD,
      stp::SBVDIV,  stp::SBVREM, stp::SBVMOD,       stp::BVLEFTSHIFT,
      stp::BVRIGHTSHIFT, stp::BVSRSHIFT};
  const std::vector<std::string> binaryNames = {
      "bvand",  "bvor",  "bvxor",  "bvadd", "bvsub", "bvmul", "bvudiv",
      "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr"};

  for (size_t i = 0; i < binary.size(); i++)
  {
    const Kind k = binary[i];
    const bool exact =
        !(k == stp::BVMULT || k == stp::BVDIV || k == stp::BVMOD ||
          k == stp::SBVDIV || k == stp::SBVREM || k == stp::SBVMOD);
    ops.push_back({k, binaryNames[i], {value(w), value(w)}, w, false, exact});
  }

  const std::vector<Kind> predicates = {stp::EQ,    stp::BVLT,  stp::BVLE,
                                        stp::BVGT,  stp::BVGE,  stp::BVSLT,
                                        stp::BVSLE, stp::BVSGT, stp::BVSGE};
  const std::vector<std::string> predicateNames = {
      "eq", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt",
      "bvsge"};
  for (size_t i = 0; i < predicates.size(); i++)
    ops.push_back({predicates[i], predicateNames[i], {value(w), value(w)}, 1,
                   true, true});

  ops.push_back({stp::BVNOT, "bvnot", {value(w)}, w, false, true});
  ops.push_back({stp::BVUMINUS, "bvneg", {value(w)}, w, false, true});
  ops.push_back(
      {stp::ITE, "ite", {boolean(), value(w), value(w)}, w, false, true});
  ops.push_back(
      {stp::BVCONCAT, "concat", {value(w), value(w)}, 2 * w, false, true});
  // The top bit of the child.
  ops.push_back({stp::BVEXTRACT,
                 "extract",
                 {value(w), constant(w - 1), constant(w - 1)},
                 1,
                 false,
                 true});
  ops.push_back({stp::BVZX,
                 "zero_extend",
                 {value(w), constant(2 * w)},
                 2 * w,
                 false,
                 true});
  ops.push_back({stp::BVSX,
                 "sign_extend",
                 {value(w), constant(2 * w)},
                 2 * w,
                 false,
                 true});

  // The boolean operations don't have a width.
  if (w == 1)
  {
    ops.push_back({stp::AND, "and", {boolean(), boolean()}, 1, true, true});
    ops.push_back({stp::OR, "or", {boolean(), boolean()}, 1, true, true});
    ops.push_back({stp::XOR, "xor", {boolean(), boolean()}, 1, true, true});
    ops.push_back({stp::IFF, "iff", {boolean(), boolean()}, 1, true, true});
    ops.push_back(
        {stp::IMPLIES, "implies", {boolean(), boolean()}, 1, true, true});
    ops.push_back({stp::NOT, "not", {boolean()}, 1, true, true});
  }

  return ops;
}

struct Context
{
  stp::STPMgr mgr;
  NodeFactory* factory() { return mgr.hashingNodeFactory; }

  ASTNode build(const OpUnderTest& op)
  {
    ASTVec children;
    for (size_t i = 0; i < op.children.size(); i++)
    {
      const Child& c = op.children[i];
      if (c.isConstant)
      {
        children.push_back(mgr.CreateBVConst(c.width, c.value));
        continue;
      }
      const std::string name =
          "s_" + op.name + "_" + std::to_string(op.resultWidth) + "_" +
          std::to_string(i);
      children.push_back(
          mgr.CreateSymbol(name.c_str(), 0, c.isBoolean ? 0 : c.width));
    }

    ASTNode n = op.resultIsBoolean
                    ? factory()->CreateNode(op.kind, children)
                    : factory()->CreateTerm(op.kind, op.resultWidth, children);
    BVTypeCheck(n);
    return n;
  }

  // The operation applied to one concrete assignment.
  unsigned evaluate(const OpUnderTest& op, const std::vector<unsigned>& values)
  {
    ASTVec children;
    for (size_t i = 0; i < op.children.size(); i++)
    {
      const Child& c = op.children[i];
      const unsigned v = c.isConstant ? c.value : values[i];
      if (c.isBoolean)
        children.push_back(v ? mgr.ASTTrue : mgr.ASTFalse);
      else
        children.push_back(mgr.CreateBVConst(c.width, v));
    }

    const ASTNode result = stp::NonMemberBVConstEvaluator(
        &mgr, op.kind, children, op.resultIsBoolean ? 0 : op.resultWidth);
    if (op.resultIsBoolean)
      return result == mgr.ASTTrue ? 1 : 0;
    return fromCBV(result.GetBVConst(), op.resultWidth);
  }
};

// A child either ranges over a subset of the values of its width, or over
// all of them because nothing is known about it. The options are the
// non-empty subsets whose size is within "maxSetSize", and then one more
// standing for "unknown", which is the last one.
std::vector<unsigned> masksFor(const Child& c, unsigned maxSetSize)
{
  std::vector<unsigned> masks;
  if (c.isConstant)
  {
    masks.push_back(1u << c.value);
    return masks;
  }

  const unsigned values = 1u << c.width;
  for (unsigned mask = 1; mask < (1u << values); mask++)
  {
    unsigned size = 0;
    for (unsigned v = 0; v < values; v++)
      size += (mask >> v) & 1;
    if (size <= maxSetSize)
      masks.push_back(mask);
  }
  masks.push_back((1u << values) - 1); // unknown: every value, no set
  return masks;
}

std::string describe(const OpUnderTest& op, const std::vector<unsigned>& masks,
                     const std::vector<bool>& unknown)
{
  std::string result = op.name + "(";
  for (size_t i = 0; i < masks.size(); i++)
  {
    if (i > 0)
      result += ", ";
    if (unknown[i])
    {
      result += "?";
      continue;
    }
    result += "{";
    bool first = true;
    for (unsigned v = 0; v < 32; v++)
      if ((masks[i] >> v) & 1)
      {
        if (!first)
          result += ",";
        result += std::to_string(v);
        first = false;
      }
    result += "}";
  }
  return result + ")";
}

void checkExhaustively(unsigned width, unsigned maxSetSize)
{
  boot();
  Context c;
  ValueSetAnalysis analysis(c.mgr);

  for (const OpUnderTest& op : operationsAt(width))
  {
    const ASTNode n = c.build(op);
    const size_t degree = op.children.size();

    // What the operation produces for every concrete assignment, indexed by
    // the children's values packed together. Built once: the evaluator is
    // far slower than the sweep it feeds.
    std::vector<unsigned> shift(degree, 0);
    unsigned packedBits = 0;
    for (size_t i = 0; i < degree; i++)
    {
      shift[i] = packedBits;
      if (!op.children[i].isConstant)
        packedBits += op.children[i].width;
    }

    std::vector<unsigned> table(1u << packedBits, 0);
    for (unsigned packed = 0; packed < table.size(); packed++)
    {
      std::vector<unsigned> values(degree, 0);
      for (size_t i = 0; i < degree; i++)
        if (!op.children[i].isConstant)
          values[i] =
              (packed >> shift[i]) & ((1u << op.children[i].width) - 1);
      table[packed] = c.evaluate(op, values);
    }

    std::vector<std::vector<unsigned>> options(degree);
    std::vector<size_t> option(degree, 0);
    for (size_t i = 0; i < degree; i++)
      options[i] = masksFor(op.children[i], maxSetSize);

    bool done = false;
    while (!done)
    {
      std::vector<unsigned> masks(degree, 0);
      std::vector<bool> unknown(degree, false);
      for (size_t i = 0; i < degree; i++)
      {
        masks[i] = options[i][option[i]];
        unknown[i] = !op.children[i].isConstant &&
                     option[i] + 1 == options[i].size();
      }

      // The sets handed to the analysis. Unknown children are null, which
      // is how a symbol's value set is stored.
      std::vector<ValueSet*> owned(degree, nullptr);
      std::vector<const ValueSet*> children(degree, nullptr);
      for (size_t i = 0; i < degree; i++)
      {
        if (unknown[i])
          continue;
        const Child& child = op.children[i];
        owned[i] = new ValueSet(child.width, child.isBoolean);
        if (child.isConstant)
        {
          EXPECT_TRUE(owned[i]->insert(makeCBV(child.width, child.value)));
        }
        else
        {
          for (unsigned v = 0; v < (1u << child.width); v++)
            if ((masks[i] >> v) & 1)
            {
              EXPECT_TRUE(owned[i]->insert(makeCBV(child.width, v)));
            }
        }
        children[i] = owned[i];
      }

      // Every value the operation can produce from those inputs. An
      // unknown child ranges over its whole width.
      std::vector<unsigned> ideal;
      for (unsigned packed = 0; packed < table.size(); packed++)
      {
        bool admitted = true;
        for (size_t i = 0; i < degree && admitted; i++)
        {
          if (op.children[i].isConstant || unknown[i])
            continue;
          const unsigned v =
              (packed >> shift[i]) & ((1u << op.children[i].width) - 1);
          admitted = ((masks[i] >> v) & 1) != 0;
        }
        if (admitted &&
            std::find(ideal.begin(), ideal.end(), table[packed]) == ideal.end())
          ideal.push_back(table[packed]);
      }
      std::sort(ideal.begin(), ideal.end());

      ValueSet* result = analysis.dispatchToTransferFunctions(n, children);
      const std::string context = describe(op, masks, unknown) + " at width " +
                                  std::to_string(width);

      // Either the analysis widened completely, or it is exactly right.
      if (result != nullptr)
      {
        EXPECT_EQ(members(result), ideal) << context;
      }

      // The cheap operations have to be exact whenever the answer is
      // something a set can hold and is worth holding.
      const bool representable = ideal.size() <= ValueSet::MAX_ELEMENTS &&
                                 ideal.size() < (1u << op.resultWidth);
      if (op.mustBeExact && representable)
      {
        EXPECT_NE(result, nullptr) << context;
        if (result != nullptr)
        {
          EXPECT_EQ(members(result), ideal) << context;
        }
      }

      delete result;
      for (ValueSet* set : owned)
        delete set;

      done = true;
      for (size_t i = 0; i < degree; i++)
      {
        if (++option[i] < options[i].size())
        {
          done = false;
          break;
        }
        option[i] = 0;
      }
    }
  }
}

} // namespace

// Every subset of every child, at the widths where running them all is
// quick. (Width three with every subset passes too, but takes over a
// minute, which is longer than the rest of the suite put together.)
TEST(ValueSet_Exhaustive_Test, all_sets_width_one)
{
  checkExhaustively(1, 2);
}

TEST(ValueSet_Exhaustive_Test, all_sets_width_two)
{
  checkExhaustively(2, 4);
}

TEST(ValueSet_Exhaustive_Test, sets_of_three_width_three)
{
  checkExhaustively(3, 3);
}

// Wider, where enumerating every subset is out of reach: single values and
// the unknown child, which is where the reasoning about unknown operands
// lives. Width four is also where a bitwise operation's answer first stops
// fitting in a set -- x & 15 with x unknown has sixteen answers -- so the
// giving-up path is covered here too.
TEST(ValueSet_Exhaustive_Test, single_values_width_four)
{
  checkExhaustively(4, 1);
}

TEST(ValueSet_Exhaustive_Test, single_values_width_five)
{
  checkExhaustively(5, 1);
}

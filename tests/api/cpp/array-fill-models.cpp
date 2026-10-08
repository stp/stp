/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
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

// array-fill-models.cpp -- a sat answer's model satisfies every assertion
// whatever model-array-fill says.
//
// A candidate's read rows can give two reads equal indexes and different
// values: m[15] = 15 and m[m[15]] = 9. The model collapses them onto one
// cell, and the check that accepts the candidate evaluates the assertions
// under that collapsed model, so a cell the solve never read can decide the
// answer -- here m[9], through (select m (select m #xF)). That is a model
// only for the value the check gave such a cell, so the model the API
// publishes has to fill it with that value too: with all-ones, under
// model-array-fill = ones, after a check that completed it with zero, the
// published model falsified an assertion the check had just found true.
// Nested reads on the incremental driver collapse rows often enough to show
// it on a few dozen stacks; the batch pipeline rarely.

#include "api_common.hpp"

#include <cstdint>
#include <string>
#include <vector>

using namespace stp;

namespace
{

enum class Layout
{
  IncrementalBase,   // the incremental driver, assertions at level 0
  IncrementalPushed, // the incremental driver, one push deep
  Batch              // incremental = off
};

const char* layout_name(Layout l)
{
  switch (l)
  {
    case Layout::IncrementalBase: return "incremental, level 0";
    case Layout::IncrementalPushed: return "incremental, one push";
    case Layout::Batch: return "batch";
  }
  return "?";
}

// Asserts `assertions` over a, b, c, d : (_ BitVec 4) and
// m : (Array (_ BitVec 4) (_ BitVec 4)), checks, and on sat returns the
// assertions the model falsifies. `read_fill`, when set, is written between
// the check and the first model read.
std::vector<std::string> falsified(Layout layout, const std::string& fill,
                                   const std::vector<std::string>& assertions,
                                   const std::string& read_fill = "")
{
  TermManager tm;
  Options o;
  o.set("incremental", layout == Layout::Batch ? "off" : "on");
  o.set("model-array-fill", fill);
  Solver s(tm, o);
  s.parse_smt2("(declare-const a (_ BitVec 4))(declare-const b (_ BitVec 4))"
               "(declare-const c (_ BitVec 4))(declare-const d (_ BitVec 4))"
               "(declare-const m (Array (_ BitVec 4) (_ BitVec 4)))");
  if (layout == Layout::IncrementalPushed)
    s.push();
  std::vector<Term> terms;
  for (const std::string& f : assertions)
  {
    terms.push_back(s.parse_term(f));
    s.assert_formula(terms.back());
  }
  std::vector<std::string> out;
  if (!s.check_sat().is_sat())
    return out;
  if (!read_fill.empty())
    s.options().set("model-array-fill", read_fill);
  const Model model = s.model();
  for (std::size_t i = 0; i < terms.size(); ++i)
    if (!model.bool_value(terms[i]))
      out.push_back(assertions[i]);
  return out;
}

// The stack that first showed it, and its mirror image for the other fill:
// one push deep, each candidate the check accepted read m[m[15]] from a cell
// no row recorded. The first falsified its assertion when the check completed
// with all-ones and the model filled with zero, the second the other way
// round.
TEST(ArrayFillModels, nested_read_at_one_push)
{
  const std::vector<std::string> zero_falls = {
      "(bvult (select m b) (select m (select m (_ bv15 4))))", "(= d b)",
      "(= b c)"};
  const std::vector<std::string> ones_falls = {
      "(bvugt (select m b) (select m (select m (_ bv15 4))))", "(= d b)",
      "(= b c)"};
  for (const char* fill : {"zero", "ones"})
    for (const auto* stack : {&zero_falls, &ones_falls})
      for (Layout l :
           {Layout::IncrementalBase, Layout::IncrementalPushed, Layout::Batch})
      {
        SCOPED_TRACE(std::string(fill) + ", " + layout_name(l) + ", " +
                     stack->front());
        EXPECT_EQ(falsified(l, fill, *stack), std::vector<std::string>());
      }
}

// A seeded sweep of nested-read stacks over every layout and both fills, and
// with the fill changed between the check and the first model read: the model
// a check accepted is the one it publishes, so a fill written afterwards is
// for the next check's model.
class Stacks
{
  std::uint32_t state;

  unsigned below(unsigned n)
  {
    state ^= state << 13;
    state ^= state >> 17;
    state ^= state << 5;
    return state % n;
  }
  std::string var()
  {
    static const char* const names[] = {"a", "b", "c", "d"};
    return names[below(4)];
  }
  std::string term(int depth)
  {
    switch (below(depth > 0 ? 4 : 2))
    {
      case 0: return var();
      case 1: return "(_ bv" + std::to_string(below(16)) + " 4)";
      case 2: return "(select m " + term(depth - 1) + ")";
      default: return "(bvadd " + term(depth - 1) + " " + term(depth - 1) + ")";
    }
  }
  std::string atom()
  {
    static const char* const ops[] = {"bvult", "bvugt", "=", "distinct",
                                      "bvule"};
    const std::string op = ops[below(5)];
    const std::string left =
        below(2) ? "(select m (select m " + term(1) + "))" : term(2);
    return "(" + op + " " + left + " " + term(2) + ")";
  }

public:
  explicit Stacks(std::uint32_t seed) : state(seed) {}

  std::vector<std::string> next()
  {
    std::vector<std::string> out;
    for (unsigned n = 1 + below(3); n > 0; --n)
      out.push_back(atom());
    for (unsigned n = below(3); n > 0; --n)
      out.push_back("(= " + var() + " " + var() + ")");
    return out;
  }
};

TEST(ArrayFillModels, nested_read_sweep)
{
  Stacks stacks(0x5eed1234u);
  for (int i = 0; i < 60; ++i)
  {
    const std::vector<std::string> stack = stacks.next();
    for (const char* fill : {"zero", "ones"})
      for (const char* read_fill : {"", "zero", "ones"})
        for (Layout l :
             {Layout::IncrementalBase, Layout::IncrementalPushed, Layout::Batch})
        {
          std::string trace = std::string("fill ") + fill;
          if (*read_fill != '\0')
            trace += std::string(" then ") + read_fill;
          trace += std::string(", ") + layout_name(l) + ":";
          for (const std::string& f : stack)
            trace += " " + f;
          SCOPED_TRACE(trace);
          EXPECT_EQ(falsified(l, fill, stack, read_fill),
                    std::vector<std::string>());
        }
  }
}

} // namespace

/********************************************************************
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

/*
 * Tests for n-ary (arity > 2) BVMULT nodes.
 *
 * The type checker accepts BVMULT with any arity >= 2 and the hashing node
 * factory builds such nodes, so they reach every pass -- from the parser
 * now that the simplifying factory keeps them wide, and always from
 * library code that installs no simplifying factory. These tests pin the
 * paths that used to assume exactly two operands: the bit-blaster, the
 * like-term collector, the negation pull-up and the word-level solver's
 * monomial matching.
 */

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/BVSolver.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "extlib-constbv/constantbv.h"
#include <gtest/gtest.h>
#include <sstream>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf; // hashing factory: builds inputs without simplifying.
  unsigned counter = 0;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    hf = mgr.hashingNodeFactory;
  }

  ASTNode bv(unsigned width)
  {
    return mgr.CreateSymbol(("bv" + std::to_string(counter++)).c_str(), 0,
                            width);
  }

  ASTNode konst(unsigned value, unsigned width)
  {
    return mgr.CreateBVConst(width, value);
  }

  void collectSymbols(const ASTNode& n, ASTNodeSet& out)
  {
    if (n.GetKind() == SYMBOL)
    {
      out.insert(n);
      return;
    }
    for (const auto& c : n)
      collectSymbols(c, out);
  }

  // Evaluate a fully-assigned node down to a constant.
  ASTNode eval(const ASTNode& n, ASTNodeMap assignment /*by value*/)
  {
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }

  void checkEquivalent(const ASTNode& before, const ASTNode& after)
  {
    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());

    uint64_t combos = 1;
    for (const auto& s : syms)
      combos *= 1u << s.GetValueWidth();
    ASSERT_LE(combos, 1u << 16)
        << "too many assignments (" << combos << ") -- lower the width";

    for (uint64_t c = 0; c < combos; c++)
    {
      ASTNodeMap assignment;
      uint64_t rest = c;
      for (size_t i = 0; i < syms.size(); i++)
      {
        const unsigned size = 1u << syms[i].GetValueWidth();
        assignment.insert(
            {syms[i], konst(rest % size, syms[i].GetValueWidth())});
        rest /= size;
      }
      ASTNodeMap a2 = assignment; // eval() consumes the map.
      ASSERT_EQ(eval(before, assignment), eval(after, a2))
          << "meaning changed at assignment " << c << "\nbefore:" << before
          << "\nafter:" << after;
    }
  }
};

// The full pipeline over a wide product: everything the simplifier leaves
// of it must still bit-blast. 2 * 2 * 2 == 8 has a model...
TEST(NaryBvmult, three_operand_product_solves_sat)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w), y = c.bv(w), z = c.bv(w);
  ASTNode product = c.hf->CreateTerm(BVMULT, w, x, y, z);
  ASTNode eq = c.hf->CreateNode(EQ, product, c.konst(8, w));

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);
  IncrementalSolver inc(&c.mgr, &ce, &simp, &at);

  EXPECT_EQ(SOLVER_SATISFIABLE, inc.checkSat(ASTVec{eq}));
}

// ...while odd * odd * odd is odd, so it is never 8.
TEST(NaryBvmult, three_odd_operands_never_even)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w), y = c.bv(w), z = c.bv(w);
  ASTNode product = c.hf->CreateTerm(BVMULT, w, x, y, z);
  ASTNode eq = c.hf->CreateNode(EQ, product, c.konst(8, w));

  const ASTNode zero32 = c.mgr.CreateBVConst(32, 0);
  auto oddness = [&](const ASTNode& t) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVEXTRACT, 1, t, zero32, zero32), c.konst(1, 1));
  };

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);
  IncrementalSolver inc(&c.mgr, &ce, &simp, &at);

  EXPECT_EQ(SOLVER_UNSATISFIABLE,
            inc.checkSat(ASTVec{eq, oddness(x), oddness(y), oddness(z)}));
}

// The negation pull-up rebuilds a product it strips a BVUMINUS out of;
// with three operands it must keep all of them.
TEST(NaryBvmult, negation_pullup_keeps_every_operand)
{
  Context c;
  const unsigned w = 3;
  ASTNode x = c.bv(w), y = c.bv(w), z = c.bv(w);
  ASTNode nx = c.hf->CreateTerm(BVUMINUS, w, x);
  ASTNode product = c.hf->CreateTerm(BVMULT, w, nx, y, z);
  ASTNode neg = c.hf->CreateTerm(BVUMINUS, w, product);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);

  ASTNode simplified = simp.SimplifyTerm(neg);
  c.checkEquivalent(neg, simplified);
}

// Like-term collection reads a wide monomial as coefficient times the
// product of the rest: 3*x*y + 2*x*y combines to 5*x*y.
TEST(NaryBvmult, like_terms_combine_across_wide_monomials)
{
  Context c;
  const unsigned w = 3;
  ASTNode x = c.bv(w), y = c.bv(w);
  ASTNode m1 = c.hf->CreateTerm(BVMULT, w, c.konst(3, w), x, y);
  ASTNode m2 = c.hf->CreateTerm(BVMULT, w, c.konst(2, w), x, y);
  ASTNode sum = c.hf->CreateTerm(BVPLUS, w, m1, m2);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);

  ASTNode simplified = simp.SimplifyTerm(sum);
  c.checkEquivalent(sum, simplified);

  // The two monomials must have combined into a single one.
  EXPECT_NE(BVPLUS, simplified.GetKind()) << simplified;
}

// The word-level solver's monomial patterns describe two-operand
// multiplies; a wide one must not be taken apart as if the first two
// operands were the whole product.
TEST(NaryBvmult, solver_leaves_wide_monomials_whole)
{
  Context c;
  const unsigned w = 3;
  ASTNode x = c.bv(w), y = c.bv(w);
  ASTNode product = c.hf->CreateTerm(BVMULT, w, c.konst(3, w), x, y);
  ASTNode lhs = c.hf->CreateTerm(BVPLUS, w, product, c.konst(7, w));
  ASTNode eq = c.hf->CreateNode(EQ, lhs, c.konst(0, w));

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  BVSolver solver(&c.mgr, &simp);

  ASTNode solved = solver.TopLevelBVSolve(eq, false);
  ASTNode back = simp.applySubstitutionMap(solved);
  c.checkEquivalent(eq, back);
}

// The CVC grammar is legacy and only accepts two-operand BVMULT, so the
// CVC printer must emit a wide product as a chain of binary applications
// it can read back.
TEST(NaryBvmult, cvc_printer_chunks_into_binary)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w), y = c.bv(w), z = c.bv(w);
  ASTNode product = c.hf->CreateTerm(BVMULT, w, x, y, z);

  std::ostringstream os;
  printer::PL_Print(os, product, &c.mgr);
  const std::string text = os.str();

  size_t count = 0;
  for (size_t pos = text.find("BVMULT("); pos != std::string::npos;
       pos = text.find("BVMULT(", pos + 1))
    count++;
  EXPECT_EQ(2u, count) << text;
}

} // namespace

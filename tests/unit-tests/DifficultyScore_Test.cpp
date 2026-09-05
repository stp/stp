/********************************************************************
 * The difficulty score against the AIG it is estimating.
 *
 * DifficultyScore predicts how many AIG AND-nodes the bit-blaster will build,
 * and STP reverts a simplification when that prediction says the formula got
 * harder. The prediction's coefficients were fitted to measurements; these
 * tests bit-blast the same operations and check the fit still holds, so that
 * a change to the bit-blaster which invalidates it fails here rather than
 * silently degrading the revert decision.
 *
 * tools/difficulty_bench does the same measurement across every operation and
 * width; this covers the load-bearing cases and the structural properties
 * (constant operands are cheaper, n-ary scales with degree-1) that the
 * coefficients alone do not capture.
 ********************************************************************/

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/DifficultyScore.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

class DifficultyFixture
{
public:
  STPMgr mgr;
  SubstitutionMap substitutions;
  Simplifier simp;
  unsigned counter = 0;

  DifficultyFixture() : substitutions(&mgr), simp(&mgr, &substitutions) {}

  ASTNode fresh(unsigned width)
  {
    return mgr.CreateSymbol(("s" + std::to_string(counter++)).c_str(), 0,
                            width);
  }

  ASTNode freshBool() { return fresh(0); }

  // Bit-blasts n on its own and returns the AIG AND-node count. The children
  // are fresh symbols, which cost nothing to blast, so this is the marginal
  // cost of n itself.
  int aigNodes(const ASTNode& n)
  {
    BBNodeManagerAIG nm;
    BitBlasterAIG bb(&nm, &simp, mgr.defaultNodeFactory, &mgr.UserFlags);
    if (n.GetType() == BOOLEAN_TYPE)
      bb.BBForm(n);
    else
    {
      BBNodeSetAIG support;
      bb.BBTerm(n, support);
    }
    return nm.totalNumberOfNodes();
  }

  int64_t score(const ASTNode& n)
  {
    DifficultyScore d;
    return d.score(n, &mgr);
  }

  // A constant whose set bits are exactly `bits`.
  ASTNode constant(unsigned width, const std::vector<unsigned>& bits)
  {
    CBV cbv = CONSTANTBV::BitVector_Create(width, true);
    for (unsigned b : bits)
      if (b < width)
        CONSTANTBV::BitVector_Bit_On(cbv, b);
    return mgr.CreateBVConst(cbv, width);
  }
};

// The estimate deliberately assumes no sharing, so it is an upper bound and a
// little high is right; a factor of two either way is the tolerance the
// revert decision needs.
void expectClose(DifficultyFixture& f, const ASTNode& n, const char* what)
{
  const int aig = f.aigNodes(n);
  const int64_t predicted = f.score(n);
  EXPECT_LE(predicted, 2 * static_cast<int64_t>(aig) + 8)
      << what << ": predicted " << predicted << ", built " << aig;
  EXPECT_GE(2 * predicted + 8, static_cast<int64_t>(aig))
      << what << ": predicted " << predicted << ", built " << aig;
}

TEST(DifficultyScore, bitvector_operations_are_within_a_factor_of_two)
{
  DifficultyFixture f;

  for (unsigned w : {8u, 16u, 32u, 64u})
  {
    for (const Kind k : {BVAND, BVOR, BVXOR, BVNAND, BVNOR, BVXNOR, BVPLUS,
                         BVMULT})
      expectClose(f, f.mgr.CreateTerm(k, w, f.fresh(w), f.fresh(w)), "n-ary");

    for (const Kind k : {BVSUB, BVDIV, BVMOD, SBVDIV, SBVREM, SBVMOD,
                         BVLEFTSHIFT, BVRIGHTSHIFT, BVSRSHIFT})
      expectClose(f, f.mgr.CreateTerm(k, w, f.fresh(w), f.fresh(w)), "binary");

    for (const Kind k : {EQ, BVLT, BVLE, BVGT, BVGE, BVSLT, BVSLE, BVSGT,
                         BVSGE, BVUADDO, BVSADDO, BVUMULO, BVSMULO, BVUSUBO,
                         BVSSUBO})
      expectClose(f, f.mgr.CreateNode(k, f.fresh(w), f.fresh(w)), "predicate");

    expectClose(f, f.mgr.CreateTerm(BVUMINUS, w, f.fresh(w)), "bvneg");
    expectClose(f, f.mgr.CreateTerm(ITE, w, f.freshBool(), f.fresh(w),
                                    f.fresh(w)),
                "ite");
  }
}

TEST(DifficultyScore, operations_with_a_constant_operand_are_within_a_factor_of_two)
{
  DifficultyFixture f;

  for (unsigned w : {8u, 16u, 32u, 64u})
  {
    const ASTNode small = f.constant(w, {0, 2, 5});
    const ASTNode large = f.constant(w, {w - 2, w - 8, 3});

    expectClose(f, f.mgr.CreateTerm(BVAND, w, small, f.fresh(w)), "bvand-c");
    expectClose(f, f.mgr.CreateTerm(BVXOR, w, small, f.fresh(w)), "bvxor-c");
    expectClose(f, f.mgr.CreateTerm(BVPLUS, w, small, f.fresh(w)), "bvadd-c");
    expectClose(f, f.mgr.CreateTerm(BVSUB, w, f.fresh(w), small), "bvsub-c");
    expectClose(f, f.mgr.CreateTerm(BVMULT, w, small, f.fresh(w)), "bvmul-c");
    expectClose(f, f.mgr.CreateTerm(BVMULT, w, large, f.fresh(w)), "bvmul-C");
    expectClose(f, f.mgr.CreateTerm(BVDIV, w, f.fresh(w), small), "bvudiv-c");
    expectClose(f, f.mgr.CreateTerm(BVDIV, w, small, f.fresh(w)), "c-bvudiv");
    expectClose(f, f.mgr.CreateTerm(BVDIV, w, large, f.fresh(w)), "C-bvudiv");
    expectClose(f, f.mgr.CreateTerm(BVLEFTSHIFT, w, f.fresh(w), small),
                "bvshl-c");
    expectClose(f, f.mgr.CreateNode(EQ, f.fresh(w), small), "=-c");
    expectClose(f, f.mgr.CreateNode(BVGT, f.fresh(w), small), "bvugt-c");
    expectClose(f, f.mgr.CreateTerm(ITE, w, f.freshBool(), small, f.fresh(w)),
                "ite-c");
  }
}

// Selecting and permuting bits builds no AIG node at all, and the score has
// to agree exactly: these are what a simplification that rewrites an
// operation into extracts and concats trades against.
TEST(DifficultyScore, wiring_is_free)
{
  DifficultyFixture f;
  const unsigned w = 32;

  const ASTNode x = f.fresh(w);
  const ASTNode cases[] = {
      f.mgr.CreateTerm(BVNOT, w, x),
      f.mgr.CreateTerm(BVCONCAT, 2 * w, x, f.fresh(w)),
      f.mgr.CreateTerm(BVEXTRACT, w / 2, x, f.mgr.CreateBVConst(32, w / 2 - 1),
                       f.mgr.CreateBVConst(32, 0)),
      f.mgr.CreateTerm(BVSX, 2 * w, x, f.mgr.CreateBVConst(32, 2 * w)),
      f.mgr.CreateTerm(BVZX, 2 * w, x, f.mgr.CreateBVConst(32, 2 * w)),
      f.mgr.CreateNode(NOT, f.freshBool()),
      f.mgr.CreateTerm(BVLEFTSHIFT, w, x, f.mgr.CreateBVConst(w, 3)),
      f.mgr.CreateTerm(BVAND, w, x, f.constant(w, {0, 1, 2})),
  };

  for (const ASTNode& n : cases)
  {
    EXPECT_EQ(0, f.aigNodes(n)) << n;
    EXPECT_EQ(0, f.score(n)) << n;
  }
}

// An n-ary operation is blasted as degree-1 binary ones, and the score has to
// scale the same way -- costing it `degree` times over is what made the old
// scorer prefer splitting an add into a chain.
TEST(DifficultyScore, n_ary_scales_with_one_fewer_than_the_degree)
{
  DifficultyFixture f;
  const unsigned w = 32;

  for (const Kind k : {BVPLUS, BVAND, BVXOR})
  {
    const int64_t binary =
        f.score(f.mgr.CreateTerm(k, w, f.fresh(w), f.fresh(w)));
    for (unsigned degree = 3; degree <= 8; degree++)
    {
      ASTVec kids;
      for (unsigned i = 0; i < degree; i++)
        kids.push_back(f.fresh(w));
      EXPECT_EQ(binary * static_cast<int64_t>(degree - 1),
                f.score(f.mgr.CreateTerm(k, w, kids)))
          << _kind_names[k] << " at degree " << degree;
    }
  }
}

// Everything an operation is applied to being constant means the bit-blaster
// evaluates it rather than building it.
TEST(DifficultyScore, constant_folding_costs_nothing)
{
  DifficultyFixture f;
  const unsigned w = 32;
  const ASTNode a = f.constant(w, {0, 3, 9});
  const ASTNode b = f.constant(w, {1, 4, 30});

  for (const Kind k : {BVPLUS, BVMULT, BVDIV, BVAND})
    EXPECT_EQ(0, f.score(f.mgr.CreateTerm(k, w, a, b))) << _kind_names[k];
  EXPECT_EQ(0, f.score(f.mgr.CreateNode(BVGT, a, b)));
}

// The score of a whole formula is the sum over its distinct nodes: a shared
// subterm is charged once, not once per use. That is what makes the estimate
// track the hash-consed AIG at all.
TEST(DifficultyScore, sharing_is_counted_once)
{
  DifficultyFixture f;
  const unsigned w = 32;

  const ASTNode product =
      f.mgr.CreateTerm(BVMULT, w, f.fresh(w), f.fresh(w));
  const ASTNode once = f.mgr.CreateNode(EQ, product, f.fresh(w));
  const ASTNode twice =
      f.mgr.CreateNode(AND, once, f.mgr.CreateNode(EQ, product, f.fresh(w)));

  const int64_t multiply = f.score(product);
  ASSERT_GT(multiply, 0);
  // The second use adds an equality and a conjunction, not another multiply.
  EXPECT_LT(f.score(twice) - f.score(once), multiply / 2);
}

} // namespace

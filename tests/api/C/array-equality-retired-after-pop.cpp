/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Everything the array-equality consistency checker works on is solve-local:
// the abstraction records, the frozen array graph, and the scalar names its
// refinement lemmas are encoded over. That state deliberately outlives the
// solve that built it, because the model surfaces read the certified array
// contents after the query has returned, so retiring it is the next round's
// job and nobody else's -- a C API vc_pop keeps the model of the query inside
// the bracket and so clears nothing.
//
// The incremental driver retired it on the route it takes for an ordinary
// stack. The exact-stack route, which owns the whole active stack whenever a
// conjunct has an array equality or applies an uninterpreted function, began
// a round of its own only in the first of those two cases. So a query that
// merely applied a function inherited whatever the last equality left behind,
// and STP ran the previous round's checker over this round's assignment.
//
// What that cost depends on whether the names survived into the new round's
// solver, and both endings are below, one per test. The array equality is
// popped before the second query in each: that is what makes the second round
// an ordinary one as far as arrays are concerned, and it is the point the
// stale graph should have been dropped at.

namespace
{

// vc_query: 1 = VALID (the assertions are unsatisfiable), 0 = INVALID (they
// are satisfiable). The queries below are all `false`, so 0 means sat.
const int SAT = 0;

// Two arrays of the same sort, plus the flags. 'i' engages the incremental
// driver from the first query rather than from the first push, which is what
// puts both queries below on the persistent exact-stack route; it is what a
// C API client that solves incrementally sets.
struct Session
{
  VC vc;
  Expr left, right;

  Session() : vc(vc_createValidityChecker())
  {
    vc_setFlag(vc, 'x'); // whole-array equality by lemmas on demand
    vc_setFlag(vc, 'u'); // uninterpreted functions
    vc_setFlag(vc, 'i'); // incremental from the first query

    Type array = vc_arrayType(vc, vc_bvType(vc, 8), vc_bvType(vc, 8));
    left = vc_varExpr(vc, "a", array);
    right = vc_varExpr(vc, "b", array);
  }

  ~Session() { vc_Destroy(vc); }

  int query() { return vc_query(vc, vc_falseExpr(vc)); }
};

} // namespace

// The equality is the only thing on the stack when it is queried, and the
// function application arrives after the pop. Its argument is a rounding
// mode, so the round that decides it is not the round that encoded the
// witness index and the read abstractions, and the stale graph asks the new
// assignment for scalar names that are not in it at all.
TEST(array_equality_retired_after_pop, application_asserted_after_the_pop)
{
  Session s;

  vc_push(s.vc);
  vc_assertFormula(s.vc, vc_eqExpr(s.vc, s.left, s.right));
  EXPECT_EQ(SAT, s.query());
  vc_pop(s.vc);

  Type domain[1] = {vc_fpRoundingModeType(s.vc)};
  UFDeclHandle f = vc_declareUninterpretedFunction(s.vc, "f", domain, 1,
                                                   vc_bvType(s.vc, 8));
  Expr actuals[1] = {vc_fpRoundingMode(s.vc, VC_RM_RTP)};
  Expr application = vc_applyUninterpretedFunction(s.vc, f, actuals, 1);
  Expr x = vc_varExpr(s.vc, "x", vc_bvType(s.vc, 8));
  vc_assertFormula(s.vc, vc_bvLeExpr(s.vc, application, x));

  EXPECT_EQ(SAT, s.query());
}

// The function application is already at the base level when the equality is
// pushed over it, so the second round re-solves a stack the first round did
// encode and the stale names do have values -- the ones this round's solver
// chose for a formula the graph says nothing about. The checker reads them as
// two arrays disagreeing at the witness index and demands a refinement lemma
// which a round with no active equality has no lane to encode.
TEST(array_equality_retired_after_pop, application_asserted_before_the_push)
{
  Session s;

  Type domain[1] = {vc_bvType(s.vc, 8)};
  UFDeclHandle f = vc_declareUninterpretedFunction(s.vc, "f", domain, 1,
                                                   vc_bvType(s.vc, 8));
  Expr actuals[1] = {vc_bvConstExprFromInt(s.vc, 8, 3)};
  Expr application = vc_applyUninterpretedFunction(s.vc, f, actuals, 1);
  vc_assertFormula(s.vc, vc_sbvLeExpr(s.vc, vc_bvConstExprFromInt(s.vc, 8, 1),
                                      application));

  vc_push(s.vc);
  vc_assertFormula(s.vc, vc_eqExpr(s.vc, s.left, s.right));
  EXPECT_EQ(SAT, s.query());
  vc_pop(s.vc);

  EXPECT_EQ(SAT, s.query());
}

/* Forgetting vc_DeleteExpr is a leak c_interface.h documents, and a
 * bit-vector constant survives it: those are owned by the manager's tables
 * and go when the manager does.  A Real constant is refcount-owned and
 * interns itself in LraAstState::real_constants, so the same mistake used to
 * leave that set holding raw pointers nothing would free -- and, while
 * assertions reached lib/Lra, tripped assert(real_constants.empty()) in
 * ~LraAstState and took the host process down with SIGABRT.
 *
 * This program makes exactly that mistake on both paths and must exit 0 on
 * each.  It is a crash test, not a leak test: what it pins is that a caller
 * who leaks cannot be killed by it. */
#include <stp/c_interface.h>
#include <stdio.h>

static int realSession(void)
{
  VC vc = vc_createValidityChecker();
  Type r = vc_realType(vc);
  Expr x = vc_varExpr(vc, "x", r);
  Expr c = vc_realConstExprFromStr(vc, "7/2");
  Expr le = vc_realLeExpr(vc, x, c);
  vc_assertFormula(vc, le);
  int const answer =
      vc_query(vc, vc_realLeExpr(vc, x, vc_realConstExprFromStr(vc, "100.0")));
  /* Deliberately no vc_DeleteExpr on any of the above. */
  vc_Destroy(vc);
  return answer;
}

static int bvSession(void)
{
  VC vc = vc_createValidityChecker();
  Type b = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", b);
  Expr c = vc_bvConstExprFromInt(vc, 8, 7);
  vc_assertFormula(vc, vc_bvLeExpr(vc, x, c));
  int const answer =
      vc_query(vc, vc_bvLeExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 200)));
  vc_Destroy(vc);
  return answer;
}

int main(void)
{
  int const real_answer = realSession();
  int const bv_answer = bvSession();
  if (real_answer < 0 || bv_answer < 0)
  {
    printf("unexpected query verdict: real=%d bv=%d\n", real_answer, bv_answer);
    return 1;
  }
  /* Repeat, so a stale intern table from the first session would be caught. */
  if (realSession() < 0)
  {
    printf("second Real session failed\n");
    return 1;
  }
  printf("undeleted Expr survives vc_Destroy on both paths\n");
  return 0;
}

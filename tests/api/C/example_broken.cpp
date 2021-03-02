// https://gist.github.com/delcypher/13fdf881fdde69eca95d

/* This small program is a trivial example showing
 * how to use a few bits of the STP C-API
 *
 */
#include <gtest/gtest.h>
#include <stdio.h>
#include <stp/c_interface.h>

void handleQuery(VC handle, Expr queryExpr);

TEST(examplebroken, one)
{
  int width = 8;
  VC handle = vc_createValidityChecker();

  // Create variable "x"
  Expr x = vc_varExpr(handle, "x", vc_bvType(handle, width));

  // Create bitvector x + x
  Expr xPlusx = vc_bvPlusExpr(handle, width, x, x);

  // Create bitvector constant 2
  Expr two = vc_bvConstExprFromInt(handle, width, 2);

  // Create bitvector 2*x
  Expr xTimes2 = vc_bvMultExpr(handle, width, two, x);

  // Create bool expression x + x = 2*x
  Expr equality = vc_eqExpr(handle, xPlusx, xTimes2);

  vc_assertFormula(handle, vc_trueExpr(handle));

  // We are asking STP: ∀ x. true → ( x + x = 2*x )
  // This should be VALID.
  printf("######First Query\n");
  handleQuery(handle, equality);

  // We are asking STP: ∀ x. true → ( x + x = 2 )
  // This should be INVALID.
  printf("######Second Query\n");
  // Create bool expression x + x = 2
  Expr badEquality = vc_eqExpr(handle, xPlusx, two);
  handleQuery(handle, badEquality);

  // Clean up
  vc_Destroy(handle);
}

void handleQuery(VC handle, Expr queryExpr)
{
  // Print the assertions
  printf("Assertions:\n");
  vc_printAsserts(handle, 0);

  int result = vc_query(handle, queryExpr);
  printf("Query:\n");
  vc_printQuery(handle);
  switch (result)
  {
    case 0:
      printf("Query is INVALID\n");

      // print counter example
      printf("Counter example:\n");
      vc_printCounterExample(handle);
      break;

    case 1:
      printf("Query is VALID\n");
      break;
    case 2:
      printf("Could not answer query\n");
      break;
    case 3:
      printf("Timeout.\n");
      break;
    default:
      printf("Unhandled error\n");
  }
  printf("\n\n");
}

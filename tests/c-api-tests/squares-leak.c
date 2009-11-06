/* g++ -I$(HOME)/stp/c_interface squares-leak.c -L$(HOME)/stp/lib -lstp -o squares-leak */
/* then, */
/* valgrind --leak-check=full --show-reachable=yes ./squares-leak */

#include <stdio.h>
#include "c_interface.h"

int main(int argc, char **argv) {
  unsigned int i;

  /* Do some simple arithmetic by creating an expression involving
     constants and then simplifying it. Since we create and destroy
     a fresh VC each time, we shouldn't leak any memory. */
  for (i = 1; i <= 100; i++) {
    VC vc = vc_createValidityChecker();
    Expr arg = vc_bvConstExprFromLL(vc, 64, (unsigned long long)i);
    Expr product = vc_bvMultExpr(vc, 64, arg, arg);
    Expr simp = vc_simplify(vc, product);
    unsigned long long j = getBVUnsignedLongLong(simp);
    vc_DeleteExpr(arg);
    vc_DeleteExpr(product);
    vc_DeleteExpr(simp);
    if (i % 10000 == 0)
      printf("%u**2 = %llu\n", i, j);
    vc_Destroy(vc);
  }
}

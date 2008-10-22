// gcc -c rt_trim.c -I/home/ddunbar/include && g++ -o badlog rt_trim.o -L/home/ddunbar/lib -lstp

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/resource.h>

#include <stp/c_interface.h>

static double getUserTime(void) {
        struct rusage us;
        getrusage(RUSAGE_SELF, &us);
        return us.ru_utime.tv_sec + us.ru_utime.tv_usec/1000000.;
}

static unsigned timed_query(VC vc, Expr q, int line) {
        static unsigned queryCounter = 0;
        double start = getUserTime();
        unsigned res = 0;
        double delta = 0.;

          res = vc_query(vc,q);
          delta = getUserTime()-start;
          printf("Q%d: %.2fs (%d)\n", queryCounter, delta, line);

        queryCounter++;
        return res;
}

#define vc_query(vc,q) timed_query(vc,q,__LINE__)

void *theVC;
void *gArr274;
void *gArr274End;

static void makeArrays() {
  gArr274End = gArr274 = vc_varExpr1(theVC, "arr274", 32, 8);

  int i;
  for (i=0; i < (1<<12); i++) {
    unsigned char value;
    if (i<4) {
      // value presumably only significant in relation to constant in Q1
      value = (146497536 >> (i*8)) & 0xFF; 
    } else {
      value = 0;
    }
    gArr274End = vc_writeExpr(theVC, gArr274End, 
                              vc_bvConstExprFromInt(theVC, 32, i),
                              vc_bvConstExprFromInt(theVC, 8, value));
  }
}


static void Q0(int runQuery) {
  vc_push(theVC);
  // the width here matters a lot... things go much faster if this is just
  // a concat of 0 with an 8-bit var
  void *symIndex = vc_varExpr1(theVC, "idxQ0", 0, 32);
  void *read0 = vc_readExpr(theVC, gArr274End, symIndex);
  void *tmp382 = vc_eqExpr(theVC, read0, vc_bvConstExprFromInt(theVC, 8, 0));
  if (runQuery) vc_query(theVC, tmp382);
  vc_pop(theVC);
}

static void Q1() {
  vc_push(theVC);

  void *symIndex = vc_varExpr1(theVC, "idxQ1", 0, 32);
  void *index = vc_writeExpr(theVC, gArr274End, 
                             symIndex, 
                             vc_bvConstExprFromInt(theVC, 8, 0));

  void *read0 = vc_readExpr(theVC, index, vc_bvConstExprFromInt(theVC, 32, 0));
  void *read1 = vc_readExpr(theVC, index, vc_bvConstExprFromInt(theVC, 32, 1));
  void *read2 = vc_readExpr(theVC, index, vc_bvConstExprFromInt(theVC, 32, 2));
  void *read3 = vc_readExpr(theVC, index, vc_bvConstExprFromInt(theVC, 32, 3));

  void *tmp238 = vc_bvConcatExpr(theVC, read3, 
                                 vc_bvConcatExpr(theVC, read2,
                                                 vc_bvConcatExpr(theVC, read1, read0)));
  void *tmp227 = vc_bvConstExprFromInt(theVC, 32, -146496888);
  void *tmp239 = vc_bvPlusExpr(theVC, 32, tmp238, tmp227);
  void *tmp240 = vc_bvConstExprFromInt(theVC, 32, 4096);
  void *tmp241 = vc_bvLtExpr(theVC, tmp239, tmp240);
  vc_query(theVC, tmp241);

  vc_pop(theVC);
}

int main(int argc, char **argv) {
  int runQuery = argc>1;

  printf("-- %s query test --\n", runQuery?"Two":"One");

  theVC = vc_createValidityChecker();
  makeArrays();
  Q0(runQuery);
  Q1();
  return 1;
}

# Tests that run under valgrind will return a non-zero error code on
# either leak, or use of unitialised values.
TOP = ../..
include $(TOP)/scripts/Makefile.common
CXXFLAGS= -DEXT_HASH_MAP $(CFLAGS) -I../../src/c_interface
LDFLAGS=-L../../lib
LIBS=$(LDFLAGS) -lstp 

VALGRINDPATH=`which valgrind`
ifeq   "$(VALGRINDPATH)" ""
	VALGRIND=
else
	VALGRIND=$(VALGRINDPATH) --leak-check=full --error-exitcode=10
endif


all: 0 1 2 3 4 5 6 7 8 9 10 11 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28
	rm -rf *.out

0:	
	g++ $(CXXFLAGS) array-cvcl-02.c -o a0.out $(LIBS)
	./a0.out

1:	
	g++  $(CXXFLAGS) b4-c.c -lstp -o a1.out $(LIBS)
	./a1.out
2:
	g++  $(CXXFLAGS) b4-c2.c -lstp -o a2.out $(LIBS)
	./a2.out
3:
	g++  $(CXXFLAGS) getbvunsignedlonglong-check.c -o a3.out $(LIBS)
	$(VALGRIND) ./a3.out
4:
	g++  $(CXXFLAGS) multiple-queries.c -o a4.out $(LIBS)
	./a4.out
5:
	g++  $(CXXFLAGS) parsefile-using-cinterface.c -o a5.out $(LIBS)
	./a5.out
6:
	g++  $(CXXFLAGS) print.c -o a6.out $(LIBS)
	./a6.out
7:
	g++  $(CXXFLAGS) push-pop-1.c  -o a7.out $(LIBS)
	./a7.out
8:
	g++  $(CXXFLAGS)  sbvdiv.c  -o a8.out $(LIBS)
	./a8.out
9:
	g++  $(CXXFLAGS)  simplify.c -o a9.out $(LIBS) 
	./a9.out
10:
	g++  $(CXXFLAGS)  simplify1.c -o a10.out $(LIBS)
	./a10.out
11:
	g++  $(CXXFLAGS)  squares-leak.c  -o a11.out $(LIBS)
	$(VALGRIND) ./a11.out
12:
	g++  $(CXXFLAGS)  stp-counterex.c  -o a12.out $(LIBS)
	./a12.out
13:
	g++  $(CXXFLAGS)  stp-div-001.c   -o a13.out $(LIBS)
	./a13.out
14:
	g++  $(CXXFLAGS)  stpcheck.c -o a14.out $(LIBS) 
	./a14.out
15:
	g++  $(CXXFLAGS)  x.c  -o a15.out $(LIBS)
	$(VALGRIND) ./a15.out
16:
	g++ $(CXXFLAGS)  y.c -lstp -o a16.out $(LIBS)
	./a16.out
17:
	g++  $(CXXFLAGS)  push-pop.c -o a17.out $(LIBS)
	$(VALGRIND) ./a17.out
18:
	g++  $(CXXFLAGS)  cvc-to-c.cpp  -o a18.out $(LIBS)
	#./a18.out ./t.cvc

19:
	g++  -g $(CXXFLAGS)  biosat-rna.cpp  -o a19.out $(LIBS)
	./a19.out AUUGGUAUGUAAGCUACUUCUUCCAAGACCA 800

20:
	g++  -g $(CXXFLAGS)  leak.c  -o a20.out $(LIBS)
	$(VALGRIND) ./a20.out

21:	
	g++ $(CXXFLAGS) interface-check.c -o a21.out $(LIBS)
	./a21.out
22:
	g++ $(CXXFLAGS) parsestring-using-cinterface.c -o a22.out $(LIBS)
	./a22.out

# Test 23 is the same as test 0, except linked in a different order.
# This is meant to catch problems in which libstp.a contains a
# main() function or has extra dependencies.
23:
	g++ $(CXXFLAGS) -o a23.out \
         ../../lib/libstp.a array-cvcl-02.c ../../lib/libstp.a
	./a23.out

24:
	g++ $(CXXFLAGS) -o a24.out \
         ../../lib/libstp.a if-check.c ../../lib/libstp.a
	./a24.out

25:
	g++ $(CXXFLAGS) -o a25.out \
         ../../lib/libstp.a stp-bool.c ../../lib/libstp.a
	./a25.out

26:
	g++ $(CXXFLAGS) -o a26.out \
         ../../lib/libstp.a stp-test3.c ../../lib/libstp.a
	./a26.out

27:
	g++ $(CXXFLAGS) -o a27.out \
         ../../lib/libstp.a stp-array-model.c ../../lib/libstp.a
	./a27.out

28:
	g++ $(CXXFLAGS) push-no-pop.c -o a28.out $(LIBS)
	$(VALGRIND) ./a28.out

clean:
	rm -rf *~ *.out *.dSYM

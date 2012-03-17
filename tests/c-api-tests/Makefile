# Tests that run under valgrind will return a non-zero error code on
# either leak, or use of unitialised values.
TOP = ../..
include $(TOP)/scripts/Makefile.common
CXXFLAGS= -DEXT_HASH_MAP $(CFLAGS) -I../../src/c_interface
LDFLAGS=-L../../lib
LIBS=$(LDFLAGS) -lstp -lstdc++

VALGRINDPATH=`which valgrind`
ifeq   "$(VALGRINDPATH)" ""
	VALGRIND=
else
	VALGRIND=$(VALGRINDPATH) --leak-check=full --error-exitcode=10
endif


all: 0 1 2 3 4 5 6 7 8 9 10 11 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29
	rm -rf *.out

0:	
	$(CC)  $(CXXFLAGS) array-cvcl-02.c -o a0.out $(LIBS)
	./a0.out

1:	
	$(CC)  $(CXXFLAGS) b4-c.c -lstp -o a1.out $(LIBS)
	./a1.out
2:
	$(CXX)  $(CXXFLAGS) b4-c2.c -lstp -o a2.out $(LIBS)
	./a2.out
3:
	$(CXX)  $(CXXFLAGS) getbvunsignedlonglong-check.c -o a3.out $(LIBS)
	$(VALGRIND) ./a3.out
4:
	$(CXX)  $(CXXFLAGS) multiple-queries.c -o a4.out $(LIBS)
	./a4.out
5:
	$(CXX)  $(CXXFLAGS) parsefile-using-cinterface.c -o a5.out $(LIBS)
	./a5.out
6:
	$(CXX)  $(CXXFLAGS) print.c -o a6.out $(LIBS)
	./a6.out
7:
	$(CXX)  $(CXXFLAGS) push-pop-1.c  -o a7.out $(LIBS)
	./a7.out
8:
	$(CXX)  $(CXXFLAGS)  sbvdiv.c  -o a8.out $(LIBS)
	./a8.out
9:
	$(CXX)  $(CXXFLAGS)  simplify.c -o a9.out $(LIBS) 
	./a9.out
10:
	$(CXX)  $(CXXFLAGS)  simplify1.c -o a10.out $(LIBS)
	./a10.out
11:
	$(CXX)  $(CXXFLAGS)  squares-leak.c  -o a11.out $(LIBS)
	$(VALGRIND) ./a11.out
12:
	$(CXX)  $(CXXFLAGS)  stp-counterex.c  -o a12.out $(LIBS)
	./a12.out
13:
	$(CXX)  $(CXXFLAGS)  stp-div-001.c   -o a13.out $(LIBS)
	./a13.out
14:
	$(CXX)  $(CXXFLAGS)  stpcheck.c -o a14.out $(LIBS) 
	./a14.out
15:
	$(CXX)  $(CXXFLAGS)  x.c  -o a15.out $(LIBS)
	$(VALGRIND) ./a15.out
16:
	$(CXX) $(CXXFLAGS)  y.c -lstp -o a16.out $(LIBS)
	./a16.out
17:
	$(CXX)  $(CXXFLAGS)  push-pop.c -o a17.out $(LIBS)
	$(VALGRIND) ./a17.out
18:
	$(CXX)  $(CXXFLAGS)  cvc-to-c.cpp  -o a18.out $(LIBS)
	#./a18.out ./t.cvc

19:
	$(CXX)  -g $(CXXFLAGS)  biosat-rna.cpp  -o a19.out $(LIBS)
	./a19.out AUUGGUAUGUAAGCUACUUCUUCCAAGACCA 800

20:
	$(CXX)  -g $(CXXFLAGS)  leak.c  -o a20.out $(LIBS)
	$(VALGRIND) ./a20.out

21:	
	$(CXX) $(CXXFLAGS) interface-check.c -o a21.out $(LIBS)
	./a21.out
22:
	$(CXX) $(CXXFLAGS) parsestring-using-cinterface.c -o a22.out $(LIBS)
	./a22.out

# Test 23 is the same as test 0, except linked in a different order.
# This is meant to catch problems in which libstp.a contains a
# main() function or has extra dependencies.
23:
	$(CXX) $(CXXFLAGS) -o a23.out \
         ../../lib/libstp.a array-cvcl-02.c $(LIBS)
	./a23.out

24:
	$(CXX) $(CXXFLAGS) -o a24.out \
         ../../lib/libstp.a if-check.c $(LIBS)
	./a24.out

25:
	$(CXX) $(CXXFLAGS) -o a25.out \
         ../../lib/libstp.a stp-bool.c $(LIBS)
	./a25.out

26:
	$(CC) $(CXXFLAGS) -o a26.out \
         ../../lib/libstp.a stp-test3.c $(LIBS)
	./a26.out

27:
	$(CC) $(CXXFLAGS) -o a27.out \
         ../../lib/libstp.a stp-array-model.c $(LIBS)
	./a27.out

28:
	$(CC) $(CXXFLAGS) push-no-pop.c -o a28.out $(LIBS)
	$(VALGRIND) ./a28.out

29:
	$(CXX) $(CXXFLAGS) timeout.c -o a29.out $(LIBS)
	./a29.out

clean:
	rm -rf *~ *.out *.dSYM

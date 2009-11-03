# Some of these tests look for leaks, so place a limit on virtual memory.
# Big enough leaks will thus cause a segfault.

include ../../scripts/Makefile.common
CXXFLAGS=-DEXT_HASH_MAP $(CFLAGS) -I../../src/c_interface -L../../lib

all: 0 1 2 3 4 5 6 7 8 9 10 11 11 12 13 14 15 16 17 18 19
	rm -rf *.out

0:	
	g++ $(CXXFLAGS) array-cvcl-02.c -o a0.out -lstp
	./a0.out

1:	
	g++  $(CXXFLAGS) b4-c.c -lstp -o a1.out
	./a1.out
2:
	g++  $(CXXFLAGS) b4-c2.c -lstp -o a2.out
	./a2.out
3:
	g++  $(CXXFLAGS) getbvunsignedlonglong-check.c -lstp -o a3.out
	./a3.out
4:
	g++  $(CXXFLAGS) multiple-queries.c  -lstp -o a4.out
	./a4.out
5:
	g++  $(CXXFLAGS) parsefile-using-cinterface.c -lstp -o a5.out
	./a5.out
6:
	g++  $(CXXFLAGS) print.c -lstp -o a6.out
	./a6.out
7:
	g++  $(CXXFLAGS) push-pop-1.c -lstp -o a7.out
	./a7.out
8:
	g++  $(CXXFLAGS)  sbvmod.c -lstp -o a8.out
	./a8.out
9:
	g++  $(CXXFLAGS)  simplify.c -o a9.out -lstp
	./a9.out
10:
	g++  $(CXXFLAGS)  simplify1.c -lstp -o a10.out
	./a10.out
11:
	g++  $(CXXFLAGS)  squares-leak.c -lstp -o a11.out
	#ulimit -v 30000 && ./a11.out
12:
	g++  $(CXXFLAGS)  stp-counterex.c -lstp -o a12.out
	./a12.out
13:
	g++  $(CXXFLAGS)  stp-div-001.c  -lstp -o a13.out
	./a13.out
14:
	g++  $(CXXFLAGS)  stpcheck.c -o a14.out -lstp
	./a14.out
15:
	g++  $(CXXFLAGS)  x.c  -lstp -o a15.out
	./a15.out
16:
	g++ $(CXXFLAGS)  y.c -lstp -o a16.out
	./a16.out
17:
	g++  $(CXXFLAGS)  push-pop.c -lstp -o a17.out
	./a17.out
18:
	g++  $(CXXFLAGS)  cvc-to-c.cpp  -lstp -o a18.out
	#./a18.out ./t.cvc

19:
	g++  -g $(CXXFLAGS)  biosat-rna.cpp  -lstp -o biosat.out
	./biosat.out AUUGGUAUGUAAGCUACUUCUUCCAAGACCA 800

20:
	g++  -g $(CXXFLAGS)  leak.c  -lstp -o a20.out
	#ulimit -v 13000 && ./a20.out


clean:
	rm -rf *~ *.out


all: 0 1 2 3 4 5 6 7 8 9 10 11 11 12 13 14 15 16 17 18
	rm -rf *.out

0:	
	g++ -DEXT_HASH_MAP array-cvcl-02.c -I../../src/c_interface -L../../lib -lstp -o a0.out
	./a0.out

1:	
	g++ -DEXT_HASH_MAP b4-c.c -I../../src/c_interface -L../../lib -lstp -o a1.out
	./a1.out
2:
	g++ -DEXT_HASH_MAP b4-c2.c -I../../src/c_interface -L../../lib -lstp -o a2.out
	./a2.out
3:
	g++ -DEXT_HASH_MAP getbvunsignedlonglong-check.c -I../../src/c_interface -L../../lib -lstp -o a3.out
	./a3.out
4:
	g++ -DEXT_HASH_MAP multiple-queries.c -I../../src/c_interface -L../../lib -lstp -o a4.out
	./a4.out
5:
	g++ -DEXT_HASH_MAP parsefile-using-cinterface.c -I../../src/c_interface -L../../lib -lstp -o a5.out
	./a5.out
6:
	g++ -DEXT_HASH_MAP print.c -I../../src/c_interface -L../../lib -lstp -o a6.out
	./a6.out
7:
	g++ -DEXT_HASH_MAP push-pop-1.c -I../../src/c_interface -L../../lib -lstp -o a7.out
	./a7.out
8:
	g++ -DEXT_HASH_MAP sbvmod.c -I../../src/c_interface -L../../lib -lstp -o a8.out
	./a8.out
9:
	g++ -DEXT_HASH_MAP simplify.c -I../../src/c_interface -L../../lib -lstp -o a9.out
	./a9.out
10:
	g++ -DEXT_HASH_MAP simplify1.c -I../../src/c_interface -L../../lib -lstp -o a10.out
	./a10.out
11:
	g++ -DEXT_HASH_MAP squares-leak.c -I../../src/c_interface -L../../lib -lstp -o a11.out
	./a11.out
12:
	g++ -DEXT_HASH_MAP stp-counterex.c -I../../src/c_interface -L../../lib -lstp -o a12.out
	./a12.out
13:
	g++ -DEXT_HASH_MAP stp-div-001.c -I../../src/c_interface -L../../lib -lstp -o a13.out
	./a13.out
14:
	g++ -DEXT_HASH_MAP stpcheck.c -I../../src/c_interface -L../../lib -lstp -o a14.out
	./a14.out
15:
	g++ -DEXT_HASH_MAP x.c -I../../src/c_interface -L../../lib -lstp -o a15.out
	./a15.out
16:
	g++ -DEXT_HASH_MAP y.c -I../../src/c_interface -L../../lib -lstp -o a16.out
	./a16.out
17:
	g++ -DEXT_HASH_MAP push-pop.c -I../../src/c_interface -L../../lib -lstp -o a17.out
	./a17.out
18:
	g++ -DEXT_HASH_MAP cvc-to-c.cpp -I../../src/c_interface -L../../lib -lstp -o a18.out
	./a18.out ./t.cvc


clean:
	rm -rf *~ *.out
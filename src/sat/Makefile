TOP = ../..
include $(TOP)/scripts/Makefile.common

SRCS=$(wildcard  *.cpp)
OBJS=$(SRCS:.cpp=.o)
SRCS+=utils/System.cc
OBJS+=utils/System.o
LIB=libminisat.a
COPTIMIZE="-O3 -m32"

.PHONY:core
core: $(OBJS)
	#Command line variables override those set in the makefile.
	$(MAKE) -C core libr COPTIMIZE="$(CFLAGS_M32) -O3"
	$(MAKE) -C simp libr COPTIMIZE="$(CFLAGS_M32) -O3"
	$(MAKE) -C cryptominisat2 lib all
	
	rm -f $(LIB)
	ar cq $(LIB) ./core/*.or ./simp/*.or *.o utils/*.o *.o
	ranlib $(LIB)

.PHONY: clean
clean:
	rm -rf *.o core/*.o *~ $(LIB)
	$(MAKE) -C core    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C cryptominisat2 clean

CryptoMinisat.o: CryptoMinisat.cpp
	$(CC) $(CFLAGS) -Icryptominisat2/mtl -Imtl CryptoMinisat.cpp -c -I$(TOP)/src

include ../../scripts/Makefile.common

SRCS = Globals.cpp main.cpp
OBJS = $(SRCS:.cpp=.o)
LIBS = -L../AST -last -L../sat -lminisat -L../simplifier -lsimplifier -L../bitvec -lconsteval -L../constantbv -lconstantbv -L../parser -lparser
CFLAGS += -I../sat/mtl -I../sat/core  -I../sat/simp -I../sat/unsound

parser: Globals.o main.o
	$(CXX) $(CFLAGS) $(LDFLAGS) Globals.o main.o $(LIBS) -o stp
	@mv stp ../../bin/stp

clean:	
	rm -rf *.o *~ *.a .#*

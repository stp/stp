include ../Makefile.common

SRCS = lexPL.cpp parsePL.cpp let-funcs.cpp main.cpp
OBJS = $(SRCS:.cpp=.o)
LIBS = -L../AST -last -L../sat/core -L../sat/simp -lminisat -L../simplifier -lsimplifier -L../bitvec -lconsteval -L../constantbv -lconstantbv
CFLAGS += -I../sat/mtl -I../sat/core -I../sat/simp

all: parsePL.cpp lexPL.cpp let-funcs.cpp parser parsePL.o lexPL.o let-funcs.o 

parser:		lexPL.o parsePL.o let-funcs.o main.o parsePL_defs.h
		$(CXX) $(CFLAGS) $(LDFLAGS) lexPL.o parsePL.o main.o let-funcs.o $(LIBS) -o parser
		@mv parser ../bin/stp

lexPL.cpp:	PL.lex parsePL_defs.h ../AST/AST.h
		$(LEX) PL.lex
		@mv lex.yy.c lexPL.cpp

parsePL.cpp:	PL.y
		$(YACC) PL.y
		@cp y.tab.c parsePL.cpp
		@cp y.tab.h parsePL_defs.h

clean:	
		rm -rf *.o parsePL_defs.h *~ lexPL.cpp parsePL.cpp *.output parser y.tab.* lex.yy.c .#*

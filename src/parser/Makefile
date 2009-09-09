include ../../scripts/Makefile.common

LEX=flex
YACC=bison -d -y --debug -v

SRCS = lexCVC.cpp parseCVC.cpp parseSMT.cpp lexSMT.cpp let-funcs.cpp
OBJS = $(SRCS:.cpp=.o)
LIBS = -L../AST -last -L../sat -lminisat -L../simplifier -lsimplifier -L../bitvec -lconsteval -L../constantbv -lconstantbv
CFLAGS += -I../sat/mtl -I../sat/core  -I../sat/simp -I../sat/unsound

#all: parseSMT.cpp lexSMT.cpp parseCVC.cpp lexCVC.cpp let-funcs.cpp parser parseCVC.o lexCVC.o let-funcs.o 

libparser.a: $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

lexCVC.cpp:	CVC.lex parseCVC_defs.h ../AST/AST.h
		$(LEX)  -o lexCVC.cpp --prefix cvc CVC.lex

parseCVC_defs.h parseCVC.cpp:	CVC.y
		$(YACC) -p cvc CVC.y
		@cp y.tab.c parseCVC.cpp
		@cp y.tab.h parseCVC_defs.h

lexSMT.cpp:	parseSMT_defs.h smtlib.lex ../AST/AST.h
		$(LEX) -o lexSMT.cpp --prefix smt smtlib.lex 

parseSMT_defs.h parseSMT.cpp:smtlib.y
		$(YACC) -p smt smtlib.y
		@cp y.tab.c parseSMT.cpp
		@cp y.tab.h parseSMT_defs.h

clean:	
		rm -rf *.o parseCVC_defs.h parseSMT_defs.h *~ lexSMT.cpp parseSMT.cpp lexCVC.cpp parseCVC.cpp *.output parser y.tab.* lex.yy.c .#*
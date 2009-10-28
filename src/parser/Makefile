include ../../scripts/Makefile.common

LEX=flex
YACC=bison -d -y --debug -v

SRCS = lexCVC.cpp parseCVC.cpp parseSMT.cpp lexSMT.cpp let-funcs.cpp
OBJS = $(SRCS:.cpp=.o)
LIBS = -L../AST -last -L../sat -lminisat -L../simplifier -lsimplifier -L../bitvec -lconsteval -L../constantbv -lconstantbv
CFLAGS += -I../sat/mtl -I../sat/core  -I../sat/simp -I../sat/unsound

libparser.a: $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

lexCVC.cpp:	CVC.lex parseCVC_defs.h ../AST/AST.h
		$(LEX)  -olexCVC.cpp -Pcvc CVC.lex

#For rules with multiple targets. Make runs the rule once for each target. 
#These rules are "pattern rules" which only run once (rather than twice).
parseCV%_defs.h parseCV%.cpp:	CVC.y
		$(YACC) -o cvc.tab.c -p cvc CVC.y
		@cp  cvc.tab.c parseCVC.cpp
		@cp  cvc.tab.h parseCVC_defs.h

lexSMT.cpp:	parseSMT_defs.h smtlib.lex ../AST/AST.h
		$(LEX) -o lexSMT.cpp --prefix smt smtlib.lex 

parseSM%_defs.h parseSM%.cpp:smtlib.y
		$(YACC) -o smt.tab.c -p smt smtlib.y
		@cp  smt.tab.c parseSMT.cpp
		@cp  smt.tab.h parseSMT_defs.h


clean:	
	rm -rf *.o parseCVC_defs.h parseSMT_defs.h *~ lexSMT.cpp parseSMT.cpp lexCVC.cpp parseCVC.cpp *.output parser smt.tab.* cvc.tab.* lex.yy.c .#*
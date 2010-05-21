TOP = ../..
include $(TOP)/scripts/Makefile.common

#`From the flex manual>: -Cfe' is often a good compromise between speed and size for production scanners.
LEX=flex -Cfe
YACC=bison -d -y --debug -v

SRCS = lexCVC.cpp parseCVC.cpp parseSMT.cpp lexSMT.cpp LetMgr.cpp parse2SMT.cpp lex2SMT.cpp
OBJS = $(SRCS:.cpp=.o)
LIBS = -L../AST -last -L../sat -lminisat -L../simplifier -lsimplifier -L../bitvec -lconsteval -L../constantbv -lconstantbv
CFLAGS += -I$(MTL) -I$(SOLVER_INCLUDE)

libparser.a: $(OBJS)
	rm -f $@
	$(AR) rc $@ $^
	$(RANLIB) $@

lexCVC.cpp:	CVC.lex parseCVC_defs.h ../AST/AST.h
		$(LEX)  -olexCVC.cpp -Pcvc CVC.lex

#For rules with multiple targets. Make runs the rule once for each
#target.  These rules are "pattern rules" which only run once (rather
#than twice).

parseCV%_defs.h parseCV%.cpp:	CVC.y
		$(YACC) -o cvc.tab.c -p cvc CVC.y
		@cp  cvc.tab.c parseCVC.cpp
		@cp  cvc.tab.h parseCVC_defs.h

lexSMT.cpp:	parseSMT_defs.h smtlib.lex ../AST/AST.h
		$(LEX) -olexSMT.cpp -Psmt smtlib.lex 

parseSM%_defs.h parseSM%.cpp:smtlib.y
		$(YACC) -o smt.tab.c -p smt smtlib.y
		@cp  smt.tab.c parseSMT.cpp
		@cp  smt.tab.h parseSMT_defs.h

lex2SMT.cpp: parseSMT2_defs.h smtlib2.lex ../AST/AST.h
		$(LEX) -olex2SMT.cpp -Psmt2 smtlib2.lex 

parse2SM%_defs.h parse2SM%.cpp:smtlib2.y
		$(YACC) -o smt2.tab.c -p smt2 smtlib2.y
		@cp  smt2.tab.c parse2SMT.cpp
		@cp  smt2.tab.h parse2SMT_defs.h



clean:	
	rm -rf *.o parseCVC_defs.h parseSMT_defs.h *~ lexSMT.cpp parseSMT.cpp lexCVC.cpp parseCVC.cpp *.output parser smt.tab.* smt2.tab.* cvc.tab.* lex.yy.c libparser.a parse2SMT.cpp parse2SMT_defs.h lex2SMT.cpp .#*

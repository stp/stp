TOP = ../..
include $(TOP)/scripts/Makefile.common

#`From the flex manual>: -Cfe' is often a good compromise between speed and size for production scanners.
LEX=flex -Cfe
YACC=bison --debug -v

SRCS = $(foreach foo,cvc smt smt2,lex$(foo).cpp parse$(foo).cpp) LetMgr.cpp
OBJS = $(SRCS:.cpp=.o)


libparser.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

lex%.cpp: %.lex parse%.hpp ../AST/AST.h
	$(LEX) -o$@ -P$* $<

parse%.cpp parse%.hpp: %.y
	$(YACC) -o parse$*.cpp -d -p $* $<


clean:
	$(RM) *.o *~ *.a .#* depend lex*.cpp parse*.cpp parse*.hpp *.output

ifeq (,$(filter clean configclean distclean,$(MAKECMDGOALS)))
depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
endif

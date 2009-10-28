include ../../scripts/Makefile.common

SRCS=$(wildcard  *.cpp)
OBJS = $(SRCS:.cpp=.o)
OBJS+= ASTKind.o
CFLAGS += -I../sat/mtl -I../sat/core

#Make the ast library for use by other modules
libast.a:$(OBJS) depend
	-rm -rf $@
	$(AR) rc $@ $(OBJS)
	$(RANLIB) $@

# ASTKind.h and ASTKind.cpp are automatically generated
ASTKind.h ASTKind.cpp:	ASTKind.kinds genkinds.pl
	./genkinds.pl

.PHONY: clean
clean:
	rm -rf *.o *~ *.a  ASTKind.cpp ASTKind.h depend .#*

#If this depended on ASTKind.h & ASTKind.cpp, then ./genkinds.pl
#would be called each "clean".
depend: $(SRCS) ASTKind.kinds genkinds.pl
	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include ./depend


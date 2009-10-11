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
	rm -rf *.o *~ bbtest asttest cnftest *.a  ASTKind.cpp ASTKind.h depend .#*

depend: $(SRCS) ASTKind.h ASTKind.cpp
	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include ./depend


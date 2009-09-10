include ../../scripts/Makefile.common

SRCS=$(wildcard  *.cpp printer/*.cpp)
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
	rm -rf *.o *~ bbtest asttest cnftest *.a  ASTKind.cpp .#*
	rm -rf printer/*.o printer/*~

depend: $(SRCS)
	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include ./depend


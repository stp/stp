include ../../scripts/Makefile.common

SRCS=$(wildcard  *.cpp printer/*.cpp)
SRCS+= ASTKind.cpp
OBJS = $(SRCS:.cpp=.o)
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
	rm -rf *.o *~ bbtest asttest cnftest *.a  ASTKind.h ASTKind.cpp .#*
	rm -rf printer/*.o

depend: $(SRCS)
	$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

-include depend

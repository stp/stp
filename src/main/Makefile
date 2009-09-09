include ../../scripts/Makefile.common

SRCS=$(wildcard  *.cpp)
OBJS = $(SRCS:.cpp=.o)
LIBS = 	-L../to-sat -ltosat -L../AST -last -L../abstraction-refinement -labstractionrefinement \
	-L../sat -lminisat  \
	-L../simplifier -lsimplifier \
        -L../bitvec -lconsteval \
	-L../constantbv -lconstantbv \
	-L../parser -lparser

#This rebuilds each time, because the target "parser" is not created
#Until the dependencies on each of the libraries is included, that's safest.
parser: $(OBJS) depend
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(OBJS) $(LIBS) -o stp
	@mv stp ../../bin/stp

.PHONY: clean
clean:	
	rm -rf *.o *~ *.a .#* depend

depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

-include depend

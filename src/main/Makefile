include ../../scripts/Makefile.common

SRCS=main.cpp versionString.cpp Globals.cpp
OBJS = $(SRCS:.cpp=.o)

LIBS = 	-L../to-sat -ltosat \
	-L../AST -last \
	-L../abstraction-refinement -labstractionrefinement \
	-L../sat -lminisat  \
	-L../simplifier -lsimplifier \
        -L../bitvec -lconsteval \
	-L../constantbv -lconstantbv \
	-L../parser -lparser

# This rebuilds each time, because the target "parser" is not created
# Until the dependencies on each of the libraries is included, that's safest.
parser:  $(OBJS) depend
	$(CXX) $(CXXFLAGS) $(LDFLAGS) $(OBJS) $(LIBS) -o stp
	@mv stp ../../bin/stp

#.PHONY: clean
clean:	
	rm -rf *.o *~ *.a .#* depend versionString.cpp

# Use svnversion to output the global revision number. 
# This will be updated every time make is called. 
# Because main.cpp depends on this, 
# it will in turn be rebuilt every time.
versionString.cpp: ALWAYS_RUN
	@echo "#include <string>"  > versionString.cpp
	@echo "namespace BEEV{extern const std::string version=\"" $(shell svnversion ..) "\";}" >> versionString.cpp

ALWAYS_RUN:


depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@



#-include depend
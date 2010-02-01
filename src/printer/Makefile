include ../../scripts/Makefile.common

SRCS=$(wildcard  *.cpp)
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I$(MTL) -I$(SOLVER_INCLUDE)

#Make the ast library for use by other modules
libprinter.a:$(OBJS) depend
	-rm -rf $@
	$(AR) rc $@ $(OBJS)
	$(RANLIB) $@

.PHONY: clean
clean:
	rm -rf *.o *~ *.a depend

depend: $(SRCS)
	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include ./depend


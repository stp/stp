include ../../scripts/Makefile.common

SRCS = $(wildcard *.cpp)
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I$(MTL) -I$(MTRAND) -I$(SOLVER_INCLUDE)

libabstractionrefinement.a: 	$(OBJS) depend
				$(AR) rc $@ $(OBJS)
				$(RANLIB) $@

clean:	
				rm -rf *.o *~ *.a .#* depend

depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

#-include depend				
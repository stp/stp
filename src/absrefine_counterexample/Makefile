include ../../scripts/Makefile.common

SRCS = $(wildcard *.cpp)
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/simp -I../sat/core

libabstractionrefinement.a: 	$(OBJS) depend
				$(AR) rc $@ $(OBJS)
				$(RANLIB) $@

clean:	
				rm -rf *.o *~ *.a .#* depend

depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

#-include depend				
TOP = ../..
include $(TOP)/scripts/Makefile.common

SRCS = $(wildcard *.cpp)
SRCS += $(wildcard AIG/*.cpp)
OBJS = $(SRCS:.cpp=.o)

CFLAGS += -I$(MTL) -I$(SOLVER_INCLUDE)

libtosat.a: 	$(OBJS) depend
		$(AR) rc $@ $(OBJS)
		$(RANLIB) $@

.PHONY: clean
clean:	
		rm -rf *.o *~ *.a .#* depend AIG/*.o

depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

-include depend		

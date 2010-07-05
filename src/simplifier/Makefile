TOP = ../..
include $(TOP)/scripts/Makefile.common

SRCS = $(wildcard *.cpp)
SRCS += $(wildcard constantBitP/*.cpp)
OBJS = $(SRCS:.cpp=.o)

CFLAGS += -I$(MTL) -I$(SOLVER_INCLUDE)

libsimplifier.a:$(OBJS) depend
		$(AR) rc $@ $(OBJS)
		$(RANLIB) $@

.PHONY: clean
clean:	
	rm -rf *.o *~ *.a .#* depend constantBitP/*.o

depend: $(SRCS)
	@$(CXX) -MM $(CXXFLAGS) $(SRCS) > $@

-include depend

include ../../scripts/Makefile.common

SRCS = $(wildcard aig/*/*.c)
#SRCS += $(wildcard aig/cnf/*.c)
#SRCS += $(wildcard aig/kit/*.c)
#SRCS += $(wildcard aig/dar/*.c)

OBJS = $(SRCS:.c=.o)
CFLAGS += -I.

libabc.a: 	$(OBJS) 
		$(AR) rc $@ $(OBJS)
		$(RANLIB) $@

.PHONY: clean
clean:	
		rm -rf *.o *~ *.a .#* depend $(OBJS)

depend: $(SRCS)
	@$(CXX) -MM -MG $(CXXFLAGS) $(SRCS) > $@

-include depend		

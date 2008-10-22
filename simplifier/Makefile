include ../Makefile.common

SRCS = simplifier.cpp bvsolver.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/simp -I../sat/core

libsimplifier.a: $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

clean:	
	rm -rf *.o *~ *.a .#*

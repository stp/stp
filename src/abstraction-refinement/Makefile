include ../../scripts/Makefile.common

SRCS = AbstractionRefinement.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/simp -I../sat/core

libabstractionrefinement.a: 	$(OBJS)
				$(AR) rc $@ $^
				$(RANLIB) $@

clean:	
				rm -rf *.o *~ *.a .#*

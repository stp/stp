include ../Makefile.common

SRCS = consteval.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/core -I../sat/simp

libconsteval.a: $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

clean:	
	rm -rf *.o *~ *.a .#*

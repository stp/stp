include ../../Makefile.common

SRCS = c_interface.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/core

libcinterface.a: $(OBJS)
	$(AR) rc $@ $^
	$(RANLIB) $@

clean:	
	rm -rf *.o *~ *.a .#*

c_interface.o: c_interface.h

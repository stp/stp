include ../../scripts/Makefile.common

SRCS = BitBlast.cpp SimpBool.cpp ToCNF.cpp ToSAT.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/simp -I../sat/core

libtosat.a: 	$(OBJS)
		$(AR) rc $@ $^
		$(RANLIB) $@

clean:	
		rm -rf *.o *~ *.a .#*

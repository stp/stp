TOP = ../../..
include $(TOP)/scripts/Makefile.common

MTL       = ../mtl
SOURCES   = Solver.C dlmalloc.c
OBJECTS   = Solver.o dlmalloc.o
CFLAGS    += -I$(MTL) -DEXT_HASH_MAP -ffloat-store $(CFLAGS_M32) -c

all: $(OBJECTS)

clean:
	rm -f $(OBJECTS) $(LIB)

.C.o:
	$(CC) $(CFLAGS) $< -o $@

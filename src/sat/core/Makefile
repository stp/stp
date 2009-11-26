include   ../../../scripts/Makefile.common

MTL       = ../mtl
SOURCES   = Solver.C
OBJECTS   = $(SOURCES:.C=.o)
LIB       = libminisat.a
CFLAGS    += -I$(MTL) -DEXT_HASH_MAP -ffloat-store $(CFLAGS_M32) -c
EXEC      = minisat
LFLAGS    = -lz

all: $(LIB) #$(EXEC)
lib: $(LIB)

$(LIB): $(OBJECTS)
	rm -f $@
	ar cq $@ $(OBJECTS)
	cp $(LIB) ../
	cp $(OBJECTS) ../

clean:
	rm -f $(OBJECTS) $(LIB)

.C.o:
	$(CC) $(CFLAGS) $< -o $@

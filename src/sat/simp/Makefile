TOP = ../../..
include $(TOP)/scripts/Makefile.common

MTL       = ../mtl
SOURCES   = SimpSolver.C ../core/Solver.C 
OBJECTS   = $(SOURCES:.C=.o)
OBJECTS    += ../core/dlmalloc.o
LIB       = libminisat.a
CFLAGS    += -I$(MTL) -DEXT_HASH_MAP -ffloat-store $(CFLAGS_M32) -c -DMSPACES
EXEC      = minisat
LFLAGS    = -lz

all: $(LIB) #$(EXEC)
lib: $(LIB)

$(LIB): $(OBJECTS)
	rm -f $@
	ar cq $@ $(OBJECTS)
	ranlib $@
	cp $(LIB) ../
	cp $(OBJECTS) ../

clean:
	rm -f $(OBJECTS) $(LIB)

.C.o:
	$(CC) $(CFLAGS) $< -o $@

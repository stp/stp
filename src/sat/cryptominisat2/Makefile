include   ../../../scripts/Makefile.common

MTL       = mtl
MTRAND    = MTRand
SOURCES   = Conglomerate.cpp  FindUndef.cpp  Gaussian.cpp  Logger.cpp  MatrixFinder.cpp  PackedRow.cpp  Solver.cpp  VarReplacer.cpp  XorFinder.cpp
OBJECTS   = $(SOURCES:.cpp=.o)
LIB       = libminisat.a
CFLAGS    += -I$(MTL) -I$(MTRAND) -DEXT_HASH_MAP -ffloat-store $(CFLAGS_M32) -c
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

.cpp.o:
	$(CC) $(CFLAGS) $< -o $@

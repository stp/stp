TOP = ../../..
include $(TOP)/scripts/Makefile.common

MTL       = mtl
MTRAND    = MTRand
SOURCES   = Logger.cpp Solver.cpp Gaussian.cpp PackedRow.cpp XorFinder.cpp Conglomerate.cpp MatrixFinder.cpp VarReplacer.cpp FindUndef.cpp ClauseCleaner.cpp RestartTypeChooser.cpp Clause.cpp FailedVarSearcher.cpp PartFinder.cpp Subsumer.cpp PartHandler.cpp XorSubsumer.cpp
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
	ranlib $@
	cp $(LIB) ../
	cp $(OBJECTS) ../

clean:
	rm -f $(OBJECTS) $(LIB)

.cpp.o:
	$(CC) $(CFLAGS) $< -o $@

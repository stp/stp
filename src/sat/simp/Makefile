MTL       = ../mtl
CORE      = ../core
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
EXEC      = minisat
CFLAGS    = -I$(MTL) -I$(CORE) -DEXT_HASH_MAP -Wall -ffloat-store
LFLAGS    = -lz

CSRCS     = $(wildcard *.C)
COBJS     = $(addsuffix .o, $(basename $(CSRCS))) $(CORE)/Solver.o

include ../mtl/template.mk
all:
	ranlib libminisat.a
	cp *.or ../
	cp libminisat.a ../

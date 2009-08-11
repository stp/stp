MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
EXEC      = minisat
CFLAGS    = -I$(MTL) -Wall -DEXT_HASH_MAP -ffloat-store
LFLAGS    = -lz


include ../mtl/template.mk
all:
	cp libminisat.a ../
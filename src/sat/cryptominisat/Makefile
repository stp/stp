include   ../../../scripts/Makefile.common
MTL       = mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
EXEC      = minisat
CFLAGS    += -I$(MTL) -Wall -DEXT_HASH_MAP -ffloat-store $(CFLAGS_M32)
LFLAGS    = -lz

include mtl/template.mk
all: libminisat.a
	ranlib libminisat.a
	cp *.o ../
	cp libminisat.a ../

MTL       = ../mtl
CHDRS     = $(wildcard *.h) $(wildcard $(MTL)/*.h)
EXEC      = minisat
CFLAGS    = -I$(MTL) -Wall -DEXT_HASH_MAP -ffloat-store -m32
LFLAGS    = -lz


include ../mtl/template.mk
all:
	ranlib libminisat.a
	cp *.or ../
	cp libminisat.a ../

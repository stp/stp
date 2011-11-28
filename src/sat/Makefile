TOP = ../..
include $(TOP)/scripts/Makefile.common

SRCS = $(wildcard *.cpp)
OBJS = $(SRCS:.cpp=.o)
LIB = libminisat.a

# exported variables override those set in recursive makefiles.
export COPTIMIZE=$(CFLAGS_M32) $(CFLAGS_FPIC) -O3 


.PHONY:core
core: $(LIB)

# $(LIB) depends on */lib_release.a and will be rebuilt only if they have been updated
$(LIB): core/lib_release.a core_prop/lib_release.a simp/lib_release.a utils/lib_release.a cryptominisat2/libminisat.a $(OBJS)
	$(RM) $@
	$(call arcat,$@,$(filter %.a,$^))
	$(AR) qcs $@ $(filter %.o,$^)

core_prop/lib_release.a: FORCE
	$(MAKE) -C core_prop libr
core/lib_release.a: FORCE
	$(MAKE) -C core libr
simp/lib_release.a: FORCE
	$(MAKE) -C simp libr
utils/lib_release.a: FORCE
	$(MAKE) -C utils libr
cryptominisat2/libminisat.a: FORCE
	$(MAKE) -C cryptominisat2 lib all
FORCE:

.PHONY: clean
clean:
	$(RM) *.o *~ *.a .#*
	$(MAKE) -C core    clean
	$(MAKE) -C core_prop    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C utils   clean
	$(MAKE) -C cryptominisat2 clean

CryptoMinisat.o: CFLAGS += -Icryptominisat2/mtl -Imtl -I$(TOP)/src

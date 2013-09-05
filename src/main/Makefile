TOP = ../..
include $(TOP)/scripts/Makefile.common

SRCS = main.cpp versionString.cpp Globals.cpp
OBJS = $(SRCS:.cpp=.o)


# Build as a library; final linking to an executable will be done by the
# topmost Makefile.
libmain.a: $(filter-out main.o,$(OBJS)) | main.o
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) *.o *~ *.a .#* depend versionString.stamp versionString.cpp

# Use svnversion to output the global revision number.
versionString.stamp: FORCE
	@GITVERSION=`./getGitVersion.sh`; \
	if [ x`cat $@ 0> /dev/null` != x$$GITVERSION ]; then \
		echo $$GITVERSION > $@; \
	fi

# FIXME: there's some sort of memory error that causes "make regressstp"
# to fail if version isn't at least 3 characters long.
versionString.cpp: versionString.stamp
	@echo "#include <string>"  > $@
	@echo "namespace BEEV{extern const std::string version = \" `cat $^` \";}" >> $@

FORCE:

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend

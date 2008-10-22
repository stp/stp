 # STP (Simple Theorem Prover) top level makefile
 #
 # To make in debug mode, type 'make "CLFAGS=-ggdb"
 # To make in optimized mode, type 'make "CFLAGS=-O2" 

include Makefile.common config.info

BIN_DIR=$(PREFIX)/bin
LIB_DIR=$(PREFIX)/lib
INCLUDE_DIR=$(PREFIX)/include/stp

BINARIES=bin/stp
LIBRARIES=lib/libstp.a
HEADERS=c_interface/*.h

# NB: the TAGS target is a hack to get around this recursive make nonsense
# we want all the source and header files generated before we make tags
.PHONY: all
all:
	$(MAKE) -C AST
	$(MAKE) -C sat
	$(MAKE) -C simplifier
	$(MAKE) -C bitvec
	$(MAKE) -C c_interface
	$(MAKE) -C constantbv
	$(MAKE) -C parser -f Makefile.smt
	$(AR) rc libstp.a  AST/*.o sat/*.o simplifier/*.o bitvec/*.o constantbv/*.o c_interface/*.o
	ranlib libstp.a
	@mkdir -p lib
	@mv libstp.a lib/
	$(MAKE) TAGS
	@echo ""
	@echo "Compilation successful."
	@echo "Type 'make install' to install STP."

.PHONY: install
install: all
	@cp -f $(BINARIES) $(BIN_DIR)
	@cp -f $(LIBRARIES) $(LIB_DIR)
	@cp -f $(HEADERS) $(INCLUDE_DIR)
	@echo "STP installed successfully."

.PHONY: clean
clean:
	rm -rf *~
	rm -rf *.a
	rm -rf lib/*.a
	rm -rf test/*~
	rm -rf bin/*~
	rm -rf *.log
	rm -rf bin/stp
	rm -rf Makefile
	rm -rf config.info
	rm -f TAGS
	$(MAKE) clean -C AST
	$(MAKE) clean -C sat
	$(MAKE) clean -C simplifier
	$(MAKE) clean -C bitvec
	$(MAKE) clean -C parser
	$(MAKE) clean -C c_interface
	$(MAKE) clean -C constantbv

# this is make way too difficult because of the recursive Make junk, it 
# should be removed
TAGS: FORCE
	find . -name "*.[h]" -or -name "*.cpp" -or -name "*.C" | grep -v SCCS | etags -

FORCE:

# The higher the level, the more tests are run (3 = all)
REGRESS_TESTS0 = egt 
REGRESS_LEVEL=4
REGRESS_TESTS=$(REGRESS_TESTS0)
REGRESS_LOG = `date +%Y-%m-%d`"-regress.log"
PROGNAME=bin/stp
ALL_OPTIONS= -l $(REGRESS_LEVEL) $(PROGNAME) $(REGRESS_TESTS)

.PHONY: regressall
regressall:
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	@echo "Starting tests at" `date` | tee -a $(REGRESS_LOG)
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	bin/run_tests.smt $(ALL_OPTIONS) 2>&1 | tee -a $(REGRESS_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	@echo "Output is saved in $(REGRESS_LOG)" | tee -a $(REGRESS_LOG)
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)



 # STP (Simple Theorem Prover) top level makefile
 #
 # To make in debug mode, type 'make "OPTIMIZE=-g"
 # To make in optimized mode, type 'make "OPTIMIZE=-O3" 


include scripts/Makefile.common scripts/config.info

BIN_DIR=$(PREFIX)/bin
LIB_DIR=$(PREFIX)/lib
INCLUDE_DIR=$(PREFIX)/include/stp

SRC=src
BINARIES=bin/stp
LIBRARIES=lib/libstp.a
HEADERS=$(SRC)/c_interface/*.h

.PHONY: all
all:
	$(MAKE) -C $(SRC)/AST
	$(MAKE) -C $(SRC)/STPManager
	$(MAKE) -C $(SRC)/printer
	$(MAKE) -C $(SRC)/abstraction-refinement
	$(MAKE) -C $(SRC)/to-sat
	$(MAKE) -C $(SRC)/sat core
#	$(MAKE) -C $(SRC)/sat simp
#	$(MAKE) -C $(SRC)/sat unsound
	$(MAKE) -C $(SRC)/simplifier
	$(MAKE) -C $(SRC)/const-evaluator
	$(MAKE) -C $(SRC)/c_interface
	$(MAKE) -C $(SRC)/extlib-constbv
	$(MAKE) -C $(SRC)/parser
	$(MAKE) -C $(SRC)/main
	$(AR) rc libstp.a  $(SRC)/AST/*.o  $(SRC)/STPManager/*.o  $(SRC)/printer/*.o $(SRC)/abstraction-refinement/*.o $(SRC)/to-sat/*.o \
			   $(SRC)/sat/*.or $(SRC)/simplifier/*.o  $(SRC)/const-evaluator/*.o $(SRC)/extlib-constbv/*.o $(SRC)/c_interface/*.o \
			   $(SRC)/parser/let-funcs.o $(SRC)/parser/parseCVC.o $(SRC)/parser/lexCVC.o $(SRC)/main/*.o
	$(RANLIB) libstp.a
	@mkdir -p lib
	@mv libstp.a lib/
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
	rm -rf *~ scripts/*~
	rm -rf *.a
	rm -rf lib/*.a
	rm -rf test/*~
	rm -rf bin/*~
	rm -rf bin/stp
	rm -rf *.log
	rm -f TAGS
	$(MAKE) clean -C $(SRC)/AST
	$(MAKE) clean -C $(SRC)/STPManager	
	$(MAKE) clean -C $(SRC)/printer
	$(MAKE) clean -C $(SRC)/abstraction-refinement
	$(MAKE) clean -C $(SRC)/to-sat
	$(MAKE) clean -C $(SRC)/sat
	$(MAKE) clean -C $(SRC)/simplifier
	$(MAKE) clean -C $(SRC)/const-evaluator
	$(MAKE) clean -C $(SRC)/c_interface
	$(MAKE) clean -C $(SRC)/extlib-constbv
	$(MAKE) clean -C $(SRC)/parser
	$(MAKE) clean -C $(SRC)/main
	$(MAKE) clean -C tests/c-api-tests

.PHONY: regressall
regressall:
	$(MAKE) regresscapi && $(MAKE) regresscvc && $(MAKE) regresssmt && $(MAKE) regressstp && $(MAKE) regressbigarray

# The higher the level, the more tests are run (3 = all)
REGRESS_LEVEL=4
REGRESS_TESTS=$(REGRESS_TESTS0)
REGRESS_LOG = `date +%Y-%m-%d`"-regress-cvc.log"
PROGNAME=bin/stp
ALL_OPTIONS= -l $(REGRESS_LEVEL) $(PROGNAME) $(REGRESS_TESTS)

.PHONY: regresscvc
regresscvc:
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	@echo "Starting tests at" `date` | tee -a $(REGRESS_LOG)
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	scripts/run_cvc_tests.pl $(ALL_OPTIONS) 2>&1 | tee -a $(REGRESS_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)
	@echo "Output is saved in $(REGRESS_LOG)" | tee -a $(REGRESS_LOG)
	@echo "*********************************************************" \
          | tee -a $(REGRESS_LOG)

# The higher the level, the more tests are run (3 = all)
BIGARRAY_LOG = `date +%Y-%m-%d`"-regress-bigarray.log"
PROGNAME=bin/stp
ALL_OPTIONS= -l $(REGRESS_LEVEL) $(PROGNAME)

.PHONY: regressbigarray
regressbigarray:
	@echo "*********************************************************" \
          | tee -a $(BIGARRAY_LOG)
	@echo "Starting tests at" `date` | tee -a $(BIGARRAY_LOG)
	@echo "*********************************************************" \
          | tee -a $(BIGARRAY_LOG)
	scripts/run_bigarray_tests.pl $(ALL_OPTIONS) 2>&1 | tee -a $(BIGARRAY_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(BIGARRAY_LOG)
	@echo "Output is saved in $(BIGARRAY_LOG)" | tee -a $(BIGARRAY_LOG)
	@echo "*********************************************************" \
          | tee -a $(BIGARRAY_LOG)

SMT_LOG = `date +%Y-%m-%d`"-regress-smt.log"
.PHONY: regresssmt
regresssmt:
	@echo "*********************************************************" \
          | tee -a $(SMT_LOG)
	@echo "Starting tests at" `date` | tee -a $(SMT_LOG)
	@echo "*********************************************************" \
          | tee -a $(SMT_LOG)
	scripts/run_smt_tests.pl $(ALL_OPTIONS) 2>&1 | tee -a $(SMT_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(SMT_LOG)
	@echo "Output is saved in $(SMT_LOG)" | tee -a $(SMT_LOG)
	@echo "*********************************************************" \
          | tee -a $(SMT_LOG)

CAPI_LOG = `date +%Y-%m-%d`"-regress-c-api.log"
.PHONY: regresscapi
regresscapi:
	@echo "*********************************************************" \
          | tee -a $(CAPI_LOG)
	@echo "Starting tests at" `date` | tee -a $(CAPI_LOG)
	@echo "*********************************************************" \
          | tee -a $(CAPI_LOG)
	$(MAKE) -C tests/c-api-tests 2>&1 | tee -a $(CAPI_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(CAPI_LOG)
	@echo "Output is saved in $(CAPI_LOG)" | tee -a $(CAPI_LOG)
	@echo "*********************************************************" \
          | tee -a $(CAPI_LOG)

STP_LOG = `date +%Y-%m-%d`"-regress-stp.log"
.PHONY: regressstp
regressstp:
	@echo "*********************************************************" \
          | tee -a $(STP_LOG)
	@echo "Starting tests at" `date` | tee -a $(STP_LOG)
	@echo "*********************************************************" \
          | tee -a $(STP_LOG)
	scripts/run_stp_tests.pl 2>&1 | tee -a $(STP_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(STP_LOG)
	@echo "Output is saved in $(STP_LOG)" | tee -a $(STP_LOG)
	@echo "*********************************************************" \
          | tee -a $(STP_LOG)


GRIND_LOG = `date +%Y-%m-%d`"-grind.log"
GRINDPROG = valgrind --leak-check=full --undef-value-errors=no
GRIND_TAR  = $(BIN_DIR)/stp -d
GRIND_CALL = -vc "$(GRINDPROG) $(GRIND_TAR)" 
GRIND_OPTIONS = -l $(REGRESS_LEVEL) -rt $(GRIND_CALL) $(REGRESS_TESTS)
.PHONY: grind
grind:

	$(MAKE) install CFLAGS="-ggdb -pg -g"
	@echo "*********************************************************" \
          | tee -a $(GRIND_LOG)
	@echo "Starting tests at" `date` | tee -a $(GRIND_LOG)
	@echo "*********************************************************" \
          | tee -a $(GRIND_LOG)
	scripts/run_cvc_tests.pl $(GRIND_OPTIONS) 2>&1 | tee -a $(GRIND_LOG); [ $${PIPESTATUS[0]} -eq 0 ]
	@echo "*********************************************************" \
          | tee -a $(GRIND_LOG)
	@echo "Output is saved in $(GRIND_LOG)" | tee -a $(GRIND_LOG)
	@echo "*********************************************************" \
          | tee -a $(GRIND_LOG)
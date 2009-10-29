.PHONY: core
core:
	$(MAKE) -C core lib all	
	mv Solver.or Solver.o

.PHONY: simp
simp:
	$(MAKE) -C core lib all	
	mv Solver.or Solver.o
	$(MAKE) -C simp lib all
	mv SimpSolver.or SimpSolver.o

.PHONY: unsound
unsound:
	$(MAKE) -C core lib all	
	mv Solver.or Solver.o
	$(MAKE) -C unsound lib all
	mv UnsoundSimpSolver.or UnsoundSimpSolver.o

.PHONY: cryptominisat
cryptominisat:
	$(MAKE) -C cryptominisat lib all

.PHONY: clean
clean:
	rm -rf *.o *~ libminisat.a
	$(MAKE) -C core    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C unsound clean
	$(MAKE) -C cryptominisat clean


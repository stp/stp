.PHONY: core
core:
	$(MAKE) -C core lib all	
	mv Solver.or Solver.o

.PHONY: simp
simp:
	$(MAKE) -C simp lib all
	mv SimpSolver.or SimpSolver.o

.PHONY: unsound
unsound:
	$(MAKE) -C unsound lib all
	mv UnsoundSimpSolver.or UnsoundSimpSolver.o

.PHONY: cryptominisat
cryptominisat:
	$(MAKE) -C cryptominisat
	cp cryptominisat/libminisat.a .
	cp cryptominisat/CMakeFiles/minisat.dir/Solver/*.o .

.PHONY: clean
clean:
	rm -rf *.o *~ libminisat.a
	$(MAKE) -C core    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C unsound clean
ifdef CRYPTOMINISAT
	$(MAKE) -C cryptominisat clean
endif

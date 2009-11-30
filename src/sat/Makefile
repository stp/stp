.PHONY: core
core:
	$(MAKE) -C core lib all	

.PHONY: simp
simp:
	$(MAKE) -C core lib all	
	$(MAKE) -C simp lib all

.PHONY: unsound
unsound:
	$(MAKE) -C core lib all	
	$(MAKE) -C unsound lib all

.PHONY: cryptominisat
cryptominisat:
	$(MAKE) -C cryptominisat lib all

.PHONY: cryptominisat2
cryptominisat2:
	$(MAKE) -C cryptominisat2 lib all


.PHONY: clean
clean:
	rm -rf *.o *~ libminisat.a
	$(MAKE) -C core    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C unsound clean
	$(MAKE) -C cryptominisat clean
	$(MAKE) -C cryptominisat2 clean


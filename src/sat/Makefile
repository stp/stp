.PHONY: core
core:
	$(MAKE) -C core lib all	

.PHONY: simp
simp:
	$(MAKE) -C simp lib all

.PHONY: unsound
unsound:
	$(MAKE) -C unsound lib all

.PHONY: cryptominisat
cryptominisat:
	$(MAKE) -C cryptominisat
	cp cryptominisat/libminisat.a .

.PHONY: clean
clean:
	rm -rf *.or *~ libminisat.a
	$(MAKE) -C core    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C unsound clean
ifdef CRYPTOMINISAT
	$(MAKE) -C cryptominisat clean
endif

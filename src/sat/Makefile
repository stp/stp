.PHONY: core
core:
	$(MAKE) -C core lib all	
.PHONY: simp
simp:
	$(MAKE) -C simp lib all

.PHONY: clean
clean:
	rm -rf *~ libminisat.a
	$(MAKE) -C core clean
	$(MAKE) -C simp clean
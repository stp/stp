; Two solver flags on one command line must be diagnosed, not resolved.
;
; parse_options() consults the solver flags in a fixed order rather than in
; the order they were given, so 'stp --cadical --minisat' used to run CaDiCaL
; without saying so. Only one can be meant.
;
; Separate from bad-cli-options.smt2 because this needs a pair of solver flags
; that exist, and which solvers are compiled in varies. --minisat and
; --simplifying-minisat come and go together, and neither is a default, so
; they are the pair to test with.
;
; REQUIRES: minisat

; RUN: not %solver --minisat --simplifying-minisat %s 2>&1 | %OutputCheck %s --check-prefix=TWOSOLVERS
; RUN: not %solver --simplifying-minisat --minisat %s 2>&1 | %OutputCheck %s --check-prefix=TWOSOLVERS
; TWOSOLVERS-NOT: terminate called
; TWOSOLVERS: excludes

; Either one on its own is how the flag is meant to be used.
; RUN: %solver --minisat %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; RUN: %solver --simplifying-minisat %s 2>&1 | %OutputCheck %s --check-prefix=SOLVE
; SOLVE: ^sat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= x (_ bv1 8)))
(check-sat)
(exit)

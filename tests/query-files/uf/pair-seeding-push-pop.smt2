; REQUIRES: cadical
; A fact used to seed congruence in one incremental block must not survive
; after that block is popped.
;
; RUN: %solver --cadical --uf-pair-seeding=1 --uf-ackermann-budget=1 --uf-propagate-equalities=off --uf-skeleton-preproc=off --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: pair seeding 1 pairs \(0 Real\)
; CHECK: ^unsat
; CHECK: ^sat
;
(set-logic QF_UF)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-const a S)
(declare-const b S)
(declare-const c S)
(push 1)
(assert (= a b))
(assert (not (= (f a) (f b))))
(assert (not (= (f c) c)))
(check-sat)
(pop 1)
(assert (not (= a b)))
(assert (not (= (f a) (f b))))
(check-sat)

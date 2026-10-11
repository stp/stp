; REQUIRES: cadical
; A large-enough declaration is declined by the whole-function budget. The
; pair selected through the asserted argument equality must still make the
; query unsatisfiable, and the old model checker must cover the other pairs.
;
; RUN: %solver --cadical --uf-pair-seeding=1 --uf-ackermann-budget=1 --uf-propagate-equalities=off --uf-skeleton-preproc=off --incremental=off -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: pair seeding 1 pairs \(0 Real\)
; CHECK: ^unsat
;
(set-logic QF_UF)
(declare-sort S 0)
(declare-fun f (S) S)
(declare-const a S)
(declare-const b S)
(declare-const c S)
(assert (= a b))
(assert (not (= (f a) (f b))))
(assert (not (= (f c) c)))
(check-sat)

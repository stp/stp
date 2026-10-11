; REQUIRES: cadical
; A selected Real pair goes through the ordinary LRA registration path. Other
; Real application pairs remain governed by exact-model UF refinement.
;
; RUN: %solver --cadical --uf-pair-seeding=1 --uf-ackermann-budget=32 --incremental=off -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: pair seeding 1 pairs \(1 Real\)
; CHECK: ^unsat
;
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (<= a b))
(assert (<= b a))
(assert (not (= (f a) (f b))))
(assert (> (f c) 0))
(check-sat)

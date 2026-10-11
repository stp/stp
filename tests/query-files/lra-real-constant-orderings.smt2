; RUN: %solver %s | %OutputCheck %s
(set-logic QF_LRA)
(declare-fun p () Bool)
(declare-fun q () Bool)
; An ordering of two constant Reals is decided when it is built, so each
; ite below takes one arm at construction; the conjunction is unsat.
(assert (ite (< 2.2 2) p (not p)))
(assert (ite (>= (/ 4 2) 2.0) q (not q)))
(assert (ite (> (- 1) (/ (- 1) 3)) (not p) p))
(assert (ite (<= 2 2.2) (not q) q))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)

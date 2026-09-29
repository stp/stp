; RUN: %solver %s | %OutputCheck %s
; Core equality is chainable for every sort, including mathematical Real.
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= x y z 1.0))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (> y 1.0))
; CHECK: ^unsat$
(check-sat)
(pop 1)
(assert (not (= 1.0 x y z)))
; CHECK: ^unsat$
(check-sat)

; The --hard preset on an unsatisfiable problem.

; RUN: %solver --hard %s | %OutputCheck %s
; RUN: %solver --hard --flattening 0 %s | %OutputCheck %s
; CHECK: ^unsat$

(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (bvult x (_ bv4 8)))
(assert (bvugt x (_ bv4 8)))
(check-sat)
(exit)

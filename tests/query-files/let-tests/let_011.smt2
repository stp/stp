; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

(declare-fun x () (_ BitVec 8))
(assert (= x (_ bv5 8)))

; The let shadows the declared x; once the let closes the declared x
; must be visible again.
(assert (not (=
  (bvadd (let ((x (_ bv1 8))) x) x)   ; 1 + 5
  (_ bv6 8))))
; CHECK-NEXT: ^unsat
(check-sat)

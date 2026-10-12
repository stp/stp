; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

; The binding for b opens a let while the rebinding of a, in the same list,
; is still pending. Inside that let c must see the outer a, not the new one.
(assert (not
  (let ((a (_ bv1 4)))
    (let ((a (_ bv2 4)) (b (let ((c a)) c)))
      (and (= a (_ bv2 4)) (= b (_ bv1 4)))))))
; CHECK-NEXT: ^unsat
(check-sat)

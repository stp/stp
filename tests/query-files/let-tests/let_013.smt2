; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

; In the inner binding list, b is bound in parallel with the rebinding of a,
; so b must see the outer a, not the new one.
(assert (not
  (let ((a (_ bv1 4)))
    (let ((a (_ bv2 4)) (b a))
      (and (= a (_ bv2 4)) (= b (_ bv1 4)))))))
; CHECK-NEXT: ^unsat
(check-sat)

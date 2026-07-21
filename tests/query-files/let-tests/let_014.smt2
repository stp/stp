; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status unsat)

(declare-fun y () (_ BitVec 8))
(assert (= y (_ bv10 8)))

; The binding for z opens and closes further lets that shadow y while the
; outer binding list is still pending. The binding for w and the body must
; both see the declared y.
(assert (not
  (let ((z (let ((y (_ bv1 8)))
             (bvadd y (let ((y (_ bv2 8))) y))))   ; z = 1 + 2 = 3
        (w y))                                     ; declared y = 10
    (= (bvadd z w y) (_ bv23 8)))))                ; 3 + 10 + 10
; CHECK-NEXT: ^unsat
(check-sat)

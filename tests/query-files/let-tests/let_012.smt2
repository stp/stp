; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :category "crafted")
(set-info :status sat)

(declare-fun t () (_ BitVec 4))

; Sibling lets reuse the same name after the previous one has closed,
; including with a different type.
(assert (let ((s (_ bv3 4))) (= s (_ bv3 4))))
(assert (let ((s true)) s))
(assert (and
  (let ((s true)) s)
  (let ((s (_ bv0 4))) (= s (_ bv0 4)))
  (= t t)))
; CHECK-NEXT: ^sat
(check-sat)

; RUN: %solver %s | %OutputCheck %s
(set-logic QF_ABV)
(set-info :smt-lib-version 2.0)

(assert
 (= (_ bv0 8)
    (let ((?x (_ bv0 8)))
         ?x)))
; CHECK-NEXT: ^sat
(check-sat)
(exit)
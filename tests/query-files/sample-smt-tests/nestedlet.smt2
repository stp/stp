; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_ABV)
(set-info :smt-lib-version 2.0)
(declare-fun symb_1_179 () (_ BitVec 8))
 
(assert
 (let ((?x true))
  (and
    (let ((?y true))
      ?y)
    ?x
)))
; CHECK-NEXT: ^sat
(check-sat)
(exit)

; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; bvsdivo(x,y) overflows only for INT_MIN / -1, i.e. x=0x80 and y=0xFF.
(assert (not (= (bvsdivo x y) (and (= x #x80) (= y #xFF)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)

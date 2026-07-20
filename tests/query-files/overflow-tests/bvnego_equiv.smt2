; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
; bvnego(x) iff x is the signed minimum (0x80), and independently iff -x==x and x!=0.
(assert (not (= (bvnego x) (= x #x80))))
(assert (not (= (bvnego x) (and (= x (bvneg x)) (distinct x #x00)))))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)

; RUN: %solver %s | %OutputCheck %s
; bvnego(x) iff x is the signed minimum (0x80), and independently iff
; -x==x and x!=0. One (check-sat) per characterisation: bundling both
; behind a single query would let one of them turn sat unnoticed.
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))

(push 1)
(assert (not (= (bvnego x) (= x #x80))))
; CHECK: ^unsat
(check-sat)
(pop 1)

(push 1)
(assert (not (= (bvnego x) (and (= x (bvneg x)) (distinct x #x00)))))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)

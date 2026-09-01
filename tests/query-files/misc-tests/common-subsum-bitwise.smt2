; RUN: %solver --flattening=true --common-subsum=true %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Bitwise pair extraction must preserve values. The two bvands share the
; operand pair {x,y} and the two bvxors share it too, so both kinds get
; rebuilt around a shared node; the first equality forces x to all-ones,
; which the final assert contradicts.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(declare-const w (_ BitVec 8))
(assert (= (bvand x y z) (_ bv255 8)))
(assert (= (bvand x y w) (_ bv255 8)))
(assert (= (bvxor x y z) (_ bv7 8)))
(assert (= (bvxor x y w) (_ bv9 8)))
(assert (bvult x (_ bv255 8)))
(check-sat)

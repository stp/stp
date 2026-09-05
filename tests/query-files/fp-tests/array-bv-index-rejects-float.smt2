; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; The inverse carrier-compatible mix is ill-sorted too.
; CHECK: array index is not of the declared bitvector sort
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 1)))
(assert (= (select a (_ +zero 8 24)) #b0))
(check-sat)

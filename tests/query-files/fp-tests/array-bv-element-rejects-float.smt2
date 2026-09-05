; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; A floating-point value is not interchangeable with a same-width BV element.
; CHECK: stored value is not of the declared bitvector sort
(declare-fun a () (Array (_ BitVec 1) (_ BitVec 32)))
(assert (= (select (store a #b0 (_ +zero 8 24)) #b0) #x00000000))
(check-sat)

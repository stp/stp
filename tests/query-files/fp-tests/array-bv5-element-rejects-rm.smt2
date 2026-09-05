; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; CHECK: stored value is not of the declared bitvector sort
(declare-const a (Array (_ BitVec 1) (_ BitVec 5)))
(assert (= (select (store a #b0 RNE) #b0) #b00001))
(check-sat)

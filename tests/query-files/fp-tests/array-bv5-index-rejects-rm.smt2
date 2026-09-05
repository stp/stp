; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; CHECK: array index is not of the declared bitvector sort
(declare-const a (Array (_ BitVec 5) (_ BitVec 1)))
(assert (= (select a RNE) #b0))
(check-sat)

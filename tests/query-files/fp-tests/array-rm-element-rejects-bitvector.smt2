; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; CHECK: stored value is not of sort RoundingMode
(declare-const a (Array (_ BitVec 1) RoundingMode))
(assert (= (select (store a #b0 #b00001) #b0) RNE))
(check-sat)

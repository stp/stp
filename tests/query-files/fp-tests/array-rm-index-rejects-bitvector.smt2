; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

; CHECK: array index is not of sort RoundingMode
(declare-const a (Array RoundingMode (_ BitVec 1)))
(assert (= (select a #b00001) #b0))
(check-sat)

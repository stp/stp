; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

(declare-const c Bool)
(declare-const modes (Array RoundingMode (_ BitVec 1)))
(declare-const bits (Array (_ BitVec 5) (_ BitVec 1)))
; CHECK: ite branches must have the same sort
(assert (= (select (ite c modes bits) RNE) #b0))
(check-sat)

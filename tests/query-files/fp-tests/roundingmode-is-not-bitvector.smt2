; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; The packed carrier is exposed only inside the lowering layer.
; CHECK: bitvector operator requires bitvector operands
(assert (= (bvnot RNE) #b11110))
(check-sat)

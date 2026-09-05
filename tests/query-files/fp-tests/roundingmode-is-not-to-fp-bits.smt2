; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)

; The one-argument to_fp form takes a BitVec, not an equal-width RM carrier.
; CHECK: one-argument form of to_fp takes a bitvector
(assert (fp.isNaN ((_ to_fp 3 5) RNE)))
(check-sat)

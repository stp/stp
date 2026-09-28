; RUN: %solver %s | %OutputCheck %s
(set-logic QF_FP)

; RoundingMode is a source sort, rather than an alias for (_ BitVec 5), even
; when it crosses a parameterised function boundary.
(define-fun choose ((r RoundingMode)) RoundingMode r)
(assert (= (choose RNE) RNE))
; CHECK: sat
(check-sat)

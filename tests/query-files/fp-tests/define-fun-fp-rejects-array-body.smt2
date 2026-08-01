; RUN: not %solver %s 2>&1 | %OutputCheck %s
(set-logic QF_ABVFP)

(declare-const a (Array (_ BitVec 1) (_ FloatingPoint 8 24)))
; An array with FP elements carries the same format metadata as a scalar FP,
; but its source sort is still Array.
; CHECK: body's floating-point format does not match
(define-fun bad () (_ FloatingPoint 8 24) a)
(check-sat)

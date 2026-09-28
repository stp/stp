; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
;
; sqrt(x) <= x for x >= 1, in any mode: an order rule of the square root.
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const rm RoundingMode)
(assert (fp.leq ((_ to_fp 8 24) #x3f800000) x))
(assert (fp.lt x (fp.sqrt rm x)))
(check-sat)
